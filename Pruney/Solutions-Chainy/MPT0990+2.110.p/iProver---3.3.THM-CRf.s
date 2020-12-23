%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:20 EST 2020

% Result     : Theorem 7.65s
% Output     : CNFRefutation 7.65s
% Verified   : 
% Statistics : Number of formulae       :  195 ( 889 expanded)
%              Number of clauses        :  112 ( 282 expanded)
%              Number of leaves         :   20 ( 198 expanded)
%              Depth                    :   24
%              Number of atoms          :  598 (5905 expanded)
%              Number of equality atoms :  232 (2218 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f23,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1,X2] :
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
    inference(negated_conjecture,[],[f23])).

fof(f25,plain,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_1(X3) )
           => ( ( v2_funct_1(X2)
                & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
                & k2_relset_1(X0,X1,X2) = X1 )
             => ( k2_funct_1(X2) = X3
                | k1_xboole_0 = X1
                | k1_xboole_0 = X0 ) ) ) ) ),
    inference(pure_predicate_removal,[],[f24])).

fof(f58,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f59,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f58])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_1(X3) )
     => ( k2_funct_1(X2) != sK3
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & v2_funct_1(X2)
        & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0))
        & k2_relset_1(X0,X1,X2) = X1
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( k2_funct_1(X2) != X3
            & k1_xboole_0 != X1
            & k1_xboole_0 != X0
            & v2_funct_1(X2)
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & k2_relset_1(X0,X1,X2) = X1
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k2_funct_1(sK2) != X3
          & k1_xboole_0 != sK1
          & k1_xboole_0 != sK0
          & v2_funct_1(sK2)
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & k2_relset_1(sK0,sK1,sK2) = sK1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,
    ( k2_funct_1(sK2) != sK3
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & v2_funct_1(sK2)
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & k2_relset_1(sK0,sK1,sK2) = sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f59,f65,f64])).

fof(f101,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f66])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f99,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f66])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f102,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f66])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f45,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f44])).

fof(f83,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f104,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f66])).

fof(f98,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f66])).

fof(f22,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_1(X0) ) ) ),
    inference(pure_predicate_removal,[],[f22])).

fof(f56,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f57,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f56])).

fof(f97,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f38])).

fof(f79,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f80,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f84,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f47,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f46])).

fof(f86,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f21,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f95,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f21])).

fof(f110,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f86,f95])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f108,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_partfun1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f77,f95])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f55,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f54])).

fof(f94,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f100,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f66])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f50])).

fof(f63,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f51])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f103,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f66])).

fof(f19,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f93,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f53,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f52])).

fof(f92,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f109,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_partfun1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f78,f95])).

fof(f107,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1225,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1241,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2613,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1225,c_1241])).

cnf(c_43,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_1556,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2239,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1556])).

cnf(c_2240,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2239])).

cnf(c_6,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2338,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2339,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2338])).

cnf(c_2905,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2613,c_43,c_2240,c_2339])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1223,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_2614,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1223,c_1241])).

cnf(c_41,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_1304,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
    | ~ v1_relat_1(X0)
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1361,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1304])).

cnf(c_1561,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1361])).

cnf(c_1562,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1561])).

cnf(c_1729,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1730,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1729])).

cnf(c_3095,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2614,c_41,c_1562,c_1730])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1231,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2083,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1223,c_1231])).

cnf(c_35,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_2084,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2083,c_35])).

cnf(c_17,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_33,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_464,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_33])).

cnf(c_465,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_464])).

cnf(c_39,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_467,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_465,c_39])).

cnf(c_1217,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_467])).

cnf(c_1748,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1217,c_39,c_38,c_465,c_1561,c_1729])).

cnf(c_2087,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
    inference(demodulation,[status(thm)],[c_2084,c_1748])).

cnf(c_28,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1226,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2516,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2))))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2087,c_1226])).

cnf(c_40,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_13,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1541,plain,
    ( ~ v1_funct_1(sK2)
    | v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1542,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1541])).

cnf(c_12,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1969,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1970,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1969])).

cnf(c_6818,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2))))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2516,c_40,c_41,c_1542,c_1562,c_1730,c_1970])).

cnf(c_16,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_478,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_33])).

cnf(c_479,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_478])).

cnf(c_481,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_479,c_39])).

cnf(c_1216,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_481])).

cnf(c_3101,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_3095,c_1216])).

cnf(c_6822,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6818,c_3101])).

cnf(c_6824,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6822,c_1241])).

cnf(c_6891,plain,
    ( v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6824,c_40,c_41,c_1542,c_1562,c_1730])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1237,plain,
    ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_6901,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_6891,c_1237])).

cnf(c_16278,plain,
    ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),X0) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3095,c_6901])).

cnf(c_18,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_450,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_33])).

cnf(c_451,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(unflattening,[status(thm)],[c_450])).

cnf(c_453,plain,
    ( ~ v1_relat_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_451,c_39])).

cnf(c_1218,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_453])).

cnf(c_1751,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1218,c_39,c_38,c_451,c_1561,c_1729])).

cnf(c_2086,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(demodulation,[status(thm)],[c_2084,c_1751])).

cnf(c_16286,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k6_partfun1(sK1),X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_16278,c_2086])).

cnf(c_16529,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
    inference(superposition,[status(thm)],[c_2905,c_16286])).

cnf(c_20,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_5,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_398,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_20,c_5])).

cnf(c_1221,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_398])).

cnf(c_1979,plain,
    ( r1_tarski(k1_relat_1(sK3),sK1) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1225,c_1221])).

cnf(c_10,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k6_partfun1(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1236,plain,
    ( k5_relat_1(k6_partfun1(X0),X1) = X1
    | r1_tarski(k1_relat_1(X1),X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2890,plain,
    ( k5_relat_1(k6_partfun1(sK1),sK3) = sK3
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1979,c_1236])).

cnf(c_4417,plain,
    ( k5_relat_1(k6_partfun1(sK1),sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2890,c_43,c_2240,c_2339])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1227,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3686,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1225,c_1227])).

cnf(c_37,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_42,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_3872,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3686,c_42])).

cnf(c_3873,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_3872])).

cnf(c_3882,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1223,c_3873])).

cnf(c_23,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_34,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_419,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_34])).

cnf(c_420,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_419])).

cnf(c_26,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_54,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_422,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_420,c_54])).

cnf(c_1220,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_422])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1296,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_1821,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1220,c_39,c_38,c_37,c_36,c_54,c_420,c_1296])).

cnf(c_3884,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3882,c_1821])).

cnf(c_4662,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3884,c_40])).

cnf(c_1980,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1223,c_1221])).

cnf(c_2349,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1980,c_41,c_1562,c_1730])).

cnf(c_11,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_partfun1(X1)) = X0 ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1235,plain,
    ( k5_relat_1(X0,k6_partfun1(X1)) = X0
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3504,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0)) = k2_funct_1(sK2)
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3101,c_1235])).

cnf(c_9256,plain,
    ( r1_tarski(k1_relat_1(sK2),X0) != iProver_top
    | k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0)) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3504,c_40,c_41,c_1542,c_1562,c_1730])).

cnf(c_9257,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0)) = k2_funct_1(sK2)
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_9256])).

cnf(c_9263,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k2_funct_1(sK2) ),
    inference(superposition,[status(thm)],[c_2349,c_9257])).

cnf(c_16539,plain,
    ( k2_funct_1(sK2) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_16529,c_4417,c_4662,c_9263])).

cnf(c_30,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f107])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_16539,c_30])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:51:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.65/1.51  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.65/1.51  
% 7.65/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.65/1.51  
% 7.65/1.51  ------  iProver source info
% 7.65/1.51  
% 7.65/1.51  git: date: 2020-06-30 10:37:57 +0100
% 7.65/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.65/1.51  git: non_committed_changes: false
% 7.65/1.51  git: last_make_outside_of_git: false
% 7.65/1.51  
% 7.65/1.51  ------ 
% 7.65/1.51  
% 7.65/1.51  ------ Input Options
% 7.65/1.51  
% 7.65/1.51  --out_options                           all
% 7.65/1.51  --tptp_safe_out                         true
% 7.65/1.51  --problem_path                          ""
% 7.65/1.51  --include_path                          ""
% 7.65/1.51  --clausifier                            res/vclausify_rel
% 7.65/1.51  --clausifier_options                    ""
% 7.65/1.51  --stdin                                 false
% 7.65/1.51  --stats_out                             all
% 7.65/1.51  
% 7.65/1.51  ------ General Options
% 7.65/1.51  
% 7.65/1.51  --fof                                   false
% 7.65/1.51  --time_out_real                         305.
% 7.65/1.51  --time_out_virtual                      -1.
% 7.65/1.51  --symbol_type_check                     false
% 7.65/1.51  --clausify_out                          false
% 7.65/1.51  --sig_cnt_out                           false
% 7.65/1.51  --trig_cnt_out                          false
% 7.65/1.51  --trig_cnt_out_tolerance                1.
% 7.65/1.51  --trig_cnt_out_sk_spl                   false
% 7.65/1.51  --abstr_cl_out                          false
% 7.65/1.51  
% 7.65/1.51  ------ Global Options
% 7.65/1.51  
% 7.65/1.51  --schedule                              default
% 7.65/1.51  --add_important_lit                     false
% 7.65/1.51  --prop_solver_per_cl                    1000
% 7.65/1.51  --min_unsat_core                        false
% 7.65/1.51  --soft_assumptions                      false
% 7.65/1.51  --soft_lemma_size                       3
% 7.65/1.51  --prop_impl_unit_size                   0
% 7.65/1.51  --prop_impl_unit                        []
% 7.65/1.51  --share_sel_clauses                     true
% 7.65/1.51  --reset_solvers                         false
% 7.65/1.51  --bc_imp_inh                            [conj_cone]
% 7.65/1.51  --conj_cone_tolerance                   3.
% 7.65/1.51  --extra_neg_conj                        none
% 7.65/1.51  --large_theory_mode                     true
% 7.65/1.51  --prolific_symb_bound                   200
% 7.65/1.51  --lt_threshold                          2000
% 7.65/1.51  --clause_weak_htbl                      true
% 7.65/1.51  --gc_record_bc_elim                     false
% 7.65/1.51  
% 7.65/1.51  ------ Preprocessing Options
% 7.65/1.51  
% 7.65/1.51  --preprocessing_flag                    true
% 7.65/1.51  --time_out_prep_mult                    0.1
% 7.65/1.51  --splitting_mode                        input
% 7.65/1.51  --splitting_grd                         true
% 7.65/1.51  --splitting_cvd                         false
% 7.65/1.51  --splitting_cvd_svl                     false
% 7.65/1.51  --splitting_nvd                         32
% 7.65/1.51  --sub_typing                            true
% 7.65/1.51  --prep_gs_sim                           true
% 7.65/1.51  --prep_unflatten                        true
% 7.65/1.51  --prep_res_sim                          true
% 7.65/1.51  --prep_upred                            true
% 7.65/1.51  --prep_sem_filter                       exhaustive
% 7.65/1.51  --prep_sem_filter_out                   false
% 7.65/1.51  --pred_elim                             true
% 7.65/1.51  --res_sim_input                         true
% 7.65/1.51  --eq_ax_congr_red                       true
% 7.65/1.51  --pure_diseq_elim                       true
% 7.65/1.51  --brand_transform                       false
% 7.65/1.51  --non_eq_to_eq                          false
% 7.65/1.51  --prep_def_merge                        true
% 7.65/1.51  --prep_def_merge_prop_impl              false
% 7.65/1.51  --prep_def_merge_mbd                    true
% 7.65/1.51  --prep_def_merge_tr_red                 false
% 7.65/1.51  --prep_def_merge_tr_cl                  false
% 7.65/1.51  --smt_preprocessing                     true
% 7.65/1.51  --smt_ac_axioms                         fast
% 7.65/1.51  --preprocessed_out                      false
% 7.65/1.51  --preprocessed_stats                    false
% 7.65/1.51  
% 7.65/1.51  ------ Abstraction refinement Options
% 7.65/1.51  
% 7.65/1.51  --abstr_ref                             []
% 7.65/1.51  --abstr_ref_prep                        false
% 7.65/1.51  --abstr_ref_until_sat                   false
% 7.65/1.51  --abstr_ref_sig_restrict                funpre
% 7.65/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.65/1.51  --abstr_ref_under                       []
% 7.65/1.51  
% 7.65/1.51  ------ SAT Options
% 7.65/1.51  
% 7.65/1.51  --sat_mode                              false
% 7.65/1.51  --sat_fm_restart_options                ""
% 7.65/1.51  --sat_gr_def                            false
% 7.65/1.51  --sat_epr_types                         true
% 7.65/1.51  --sat_non_cyclic_types                  false
% 7.65/1.51  --sat_finite_models                     false
% 7.65/1.51  --sat_fm_lemmas                         false
% 7.65/1.51  --sat_fm_prep                           false
% 7.65/1.51  --sat_fm_uc_incr                        true
% 7.65/1.51  --sat_out_model                         small
% 7.65/1.51  --sat_out_clauses                       false
% 7.65/1.51  
% 7.65/1.51  ------ QBF Options
% 7.65/1.51  
% 7.65/1.51  --qbf_mode                              false
% 7.65/1.51  --qbf_elim_univ                         false
% 7.65/1.51  --qbf_dom_inst                          none
% 7.65/1.51  --qbf_dom_pre_inst                      false
% 7.65/1.51  --qbf_sk_in                             false
% 7.65/1.51  --qbf_pred_elim                         true
% 7.65/1.51  --qbf_split                             512
% 7.65/1.51  
% 7.65/1.51  ------ BMC1 Options
% 7.65/1.51  
% 7.65/1.51  --bmc1_incremental                      false
% 7.65/1.51  --bmc1_axioms                           reachable_all
% 7.65/1.51  --bmc1_min_bound                        0
% 7.65/1.51  --bmc1_max_bound                        -1
% 7.65/1.51  --bmc1_max_bound_default                -1
% 7.65/1.51  --bmc1_symbol_reachability              true
% 7.65/1.51  --bmc1_property_lemmas                  false
% 7.65/1.51  --bmc1_k_induction                      false
% 7.65/1.51  --bmc1_non_equiv_states                 false
% 7.65/1.51  --bmc1_deadlock                         false
% 7.65/1.51  --bmc1_ucm                              false
% 7.65/1.51  --bmc1_add_unsat_core                   none
% 7.65/1.51  --bmc1_unsat_core_children              false
% 7.65/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.65/1.51  --bmc1_out_stat                         full
% 7.65/1.51  --bmc1_ground_init                      false
% 7.65/1.51  --bmc1_pre_inst_next_state              false
% 7.65/1.51  --bmc1_pre_inst_state                   false
% 7.65/1.51  --bmc1_pre_inst_reach_state             false
% 7.65/1.51  --bmc1_out_unsat_core                   false
% 7.65/1.51  --bmc1_aig_witness_out                  false
% 7.65/1.51  --bmc1_verbose                          false
% 7.65/1.51  --bmc1_dump_clauses_tptp                false
% 7.65/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.65/1.51  --bmc1_dump_file                        -
% 7.65/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.65/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.65/1.51  --bmc1_ucm_extend_mode                  1
% 7.65/1.51  --bmc1_ucm_init_mode                    2
% 7.65/1.51  --bmc1_ucm_cone_mode                    none
% 7.65/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.65/1.51  --bmc1_ucm_relax_model                  4
% 7.65/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.65/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.65/1.51  --bmc1_ucm_layered_model                none
% 7.65/1.51  --bmc1_ucm_max_lemma_size               10
% 7.65/1.51  
% 7.65/1.51  ------ AIG Options
% 7.65/1.51  
% 7.65/1.51  --aig_mode                              false
% 7.65/1.51  
% 7.65/1.51  ------ Instantiation Options
% 7.65/1.51  
% 7.65/1.51  --instantiation_flag                    true
% 7.65/1.51  --inst_sos_flag                         true
% 7.65/1.51  --inst_sos_phase                        true
% 7.65/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.65/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.65/1.51  --inst_lit_sel_side                     num_symb
% 7.65/1.51  --inst_solver_per_active                1400
% 7.65/1.51  --inst_solver_calls_frac                1.
% 7.65/1.51  --inst_passive_queue_type               priority_queues
% 7.65/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.65/1.51  --inst_passive_queues_freq              [25;2]
% 7.65/1.51  --inst_dismatching                      true
% 7.65/1.51  --inst_eager_unprocessed_to_passive     true
% 7.65/1.51  --inst_prop_sim_given                   true
% 7.65/1.51  --inst_prop_sim_new                     false
% 7.65/1.51  --inst_subs_new                         false
% 7.65/1.51  --inst_eq_res_simp                      false
% 7.65/1.51  --inst_subs_given                       false
% 7.65/1.51  --inst_orphan_elimination               true
% 7.65/1.51  --inst_learning_loop_flag               true
% 7.65/1.51  --inst_learning_start                   3000
% 7.65/1.51  --inst_learning_factor                  2
% 7.65/1.51  --inst_start_prop_sim_after_learn       3
% 7.65/1.51  --inst_sel_renew                        solver
% 7.65/1.51  --inst_lit_activity_flag                true
% 7.65/1.51  --inst_restr_to_given                   false
% 7.65/1.51  --inst_activity_threshold               500
% 7.65/1.51  --inst_out_proof                        true
% 7.65/1.51  
% 7.65/1.51  ------ Resolution Options
% 7.65/1.51  
% 7.65/1.51  --resolution_flag                       true
% 7.65/1.51  --res_lit_sel                           adaptive
% 7.65/1.51  --res_lit_sel_side                      none
% 7.65/1.51  --res_ordering                          kbo
% 7.65/1.51  --res_to_prop_solver                    active
% 7.65/1.51  --res_prop_simpl_new                    false
% 7.65/1.51  --res_prop_simpl_given                  true
% 7.65/1.51  --res_passive_queue_type                priority_queues
% 7.65/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.65/1.51  --res_passive_queues_freq               [15;5]
% 7.65/1.51  --res_forward_subs                      full
% 7.65/1.51  --res_backward_subs                     full
% 7.65/1.51  --res_forward_subs_resolution           true
% 7.65/1.51  --res_backward_subs_resolution          true
% 7.65/1.51  --res_orphan_elimination                true
% 7.65/1.51  --res_time_limit                        2.
% 7.65/1.51  --res_out_proof                         true
% 7.65/1.51  
% 7.65/1.51  ------ Superposition Options
% 7.65/1.51  
% 7.65/1.51  --superposition_flag                    true
% 7.65/1.51  --sup_passive_queue_type                priority_queues
% 7.65/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.65/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.65/1.51  --demod_completeness_check              fast
% 7.65/1.51  --demod_use_ground                      true
% 7.65/1.51  --sup_to_prop_solver                    passive
% 7.65/1.51  --sup_prop_simpl_new                    true
% 7.65/1.51  --sup_prop_simpl_given                  true
% 7.65/1.51  --sup_fun_splitting                     true
% 7.65/1.51  --sup_smt_interval                      50000
% 7.65/1.51  
% 7.65/1.51  ------ Superposition Simplification Setup
% 7.65/1.51  
% 7.65/1.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.65/1.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.65/1.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.65/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.65/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.65/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.65/1.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.65/1.51  --sup_immed_triv                        [TrivRules]
% 7.65/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.65/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.65/1.51  --sup_immed_bw_main                     []
% 7.65/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.65/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.65/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.65/1.51  --sup_input_bw                          []
% 7.65/1.51  
% 7.65/1.51  ------ Combination Options
% 7.65/1.51  
% 7.65/1.51  --comb_res_mult                         3
% 7.65/1.51  --comb_sup_mult                         2
% 7.65/1.51  --comb_inst_mult                        10
% 7.65/1.51  
% 7.65/1.51  ------ Debug Options
% 7.65/1.51  
% 7.65/1.51  --dbg_backtrace                         false
% 7.65/1.51  --dbg_dump_prop_clauses                 false
% 7.65/1.51  --dbg_dump_prop_clauses_file            -
% 7.65/1.51  --dbg_out_stat                          false
% 7.65/1.51  ------ Parsing...
% 7.65/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.65/1.51  
% 7.65/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.65/1.51  
% 7.65/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.65/1.51  
% 7.65/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.65/1.51  ------ Proving...
% 7.65/1.51  ------ Problem Properties 
% 7.65/1.51  
% 7.65/1.51  
% 7.65/1.51  clauses                                 33
% 7.65/1.51  conjectures                             8
% 7.65/1.51  EPR                                     6
% 7.65/1.51  Horn                                    33
% 7.65/1.51  unary                                   11
% 7.65/1.51  binary                                  8
% 7.65/1.51  lits                                    77
% 7.65/1.51  lits eq                                 19
% 7.65/1.51  fd_pure                                 0
% 7.65/1.51  fd_pseudo                               0
% 7.65/1.51  fd_cond                                 0
% 7.65/1.51  fd_pseudo_cond                          1
% 7.65/1.51  AC symbols                              0
% 7.65/1.51  
% 7.65/1.51  ------ Schedule dynamic 5 is on 
% 7.65/1.51  
% 7.65/1.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.65/1.51  
% 7.65/1.51  
% 7.65/1.51  ------ 
% 7.65/1.51  Current options:
% 7.65/1.51  ------ 
% 7.65/1.51  
% 7.65/1.51  ------ Input Options
% 7.65/1.51  
% 7.65/1.51  --out_options                           all
% 7.65/1.51  --tptp_safe_out                         true
% 7.65/1.51  --problem_path                          ""
% 7.65/1.51  --include_path                          ""
% 7.65/1.51  --clausifier                            res/vclausify_rel
% 7.65/1.51  --clausifier_options                    ""
% 7.65/1.51  --stdin                                 false
% 7.65/1.51  --stats_out                             all
% 7.65/1.51  
% 7.65/1.51  ------ General Options
% 7.65/1.51  
% 7.65/1.51  --fof                                   false
% 7.65/1.51  --time_out_real                         305.
% 7.65/1.51  --time_out_virtual                      -1.
% 7.65/1.51  --symbol_type_check                     false
% 7.65/1.51  --clausify_out                          false
% 7.65/1.51  --sig_cnt_out                           false
% 7.65/1.51  --trig_cnt_out                          false
% 7.65/1.51  --trig_cnt_out_tolerance                1.
% 7.65/1.51  --trig_cnt_out_sk_spl                   false
% 7.65/1.51  --abstr_cl_out                          false
% 7.65/1.51  
% 7.65/1.51  ------ Global Options
% 7.65/1.51  
% 7.65/1.51  --schedule                              default
% 7.65/1.51  --add_important_lit                     false
% 7.65/1.51  --prop_solver_per_cl                    1000
% 7.65/1.51  --min_unsat_core                        false
% 7.65/1.51  --soft_assumptions                      false
% 7.65/1.51  --soft_lemma_size                       3
% 7.65/1.51  --prop_impl_unit_size                   0
% 7.65/1.51  --prop_impl_unit                        []
% 7.65/1.51  --share_sel_clauses                     true
% 7.65/1.51  --reset_solvers                         false
% 7.65/1.51  --bc_imp_inh                            [conj_cone]
% 7.65/1.51  --conj_cone_tolerance                   3.
% 7.65/1.51  --extra_neg_conj                        none
% 7.65/1.51  --large_theory_mode                     true
% 7.65/1.51  --prolific_symb_bound                   200
% 7.65/1.51  --lt_threshold                          2000
% 7.65/1.51  --clause_weak_htbl                      true
% 7.65/1.51  --gc_record_bc_elim                     false
% 7.65/1.51  
% 7.65/1.51  ------ Preprocessing Options
% 7.65/1.51  
% 7.65/1.51  --preprocessing_flag                    true
% 7.65/1.51  --time_out_prep_mult                    0.1
% 7.65/1.51  --splitting_mode                        input
% 7.65/1.51  --splitting_grd                         true
% 7.65/1.51  --splitting_cvd                         false
% 7.65/1.51  --splitting_cvd_svl                     false
% 7.65/1.51  --splitting_nvd                         32
% 7.65/1.51  --sub_typing                            true
% 7.65/1.51  --prep_gs_sim                           true
% 7.65/1.51  --prep_unflatten                        true
% 7.65/1.51  --prep_res_sim                          true
% 7.65/1.51  --prep_upred                            true
% 7.65/1.51  --prep_sem_filter                       exhaustive
% 7.65/1.51  --prep_sem_filter_out                   false
% 7.65/1.51  --pred_elim                             true
% 7.65/1.51  --res_sim_input                         true
% 7.65/1.51  --eq_ax_congr_red                       true
% 7.65/1.51  --pure_diseq_elim                       true
% 7.65/1.51  --brand_transform                       false
% 7.65/1.51  --non_eq_to_eq                          false
% 7.65/1.51  --prep_def_merge                        true
% 7.65/1.51  --prep_def_merge_prop_impl              false
% 7.65/1.51  --prep_def_merge_mbd                    true
% 7.65/1.51  --prep_def_merge_tr_red                 false
% 7.65/1.51  --prep_def_merge_tr_cl                  false
% 7.65/1.51  --smt_preprocessing                     true
% 7.65/1.51  --smt_ac_axioms                         fast
% 7.65/1.51  --preprocessed_out                      false
% 7.65/1.51  --preprocessed_stats                    false
% 7.65/1.51  
% 7.65/1.51  ------ Abstraction refinement Options
% 7.65/1.51  
% 7.65/1.51  --abstr_ref                             []
% 7.65/1.51  --abstr_ref_prep                        false
% 7.65/1.51  --abstr_ref_until_sat                   false
% 7.65/1.51  --abstr_ref_sig_restrict                funpre
% 7.65/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.65/1.51  --abstr_ref_under                       []
% 7.65/1.51  
% 7.65/1.51  ------ SAT Options
% 7.65/1.51  
% 7.65/1.51  --sat_mode                              false
% 7.65/1.51  --sat_fm_restart_options                ""
% 7.65/1.51  --sat_gr_def                            false
% 7.65/1.51  --sat_epr_types                         true
% 7.65/1.51  --sat_non_cyclic_types                  false
% 7.65/1.51  --sat_finite_models                     false
% 7.65/1.51  --sat_fm_lemmas                         false
% 7.65/1.51  --sat_fm_prep                           false
% 7.65/1.51  --sat_fm_uc_incr                        true
% 7.65/1.51  --sat_out_model                         small
% 7.65/1.51  --sat_out_clauses                       false
% 7.65/1.51  
% 7.65/1.51  ------ QBF Options
% 7.65/1.51  
% 7.65/1.51  --qbf_mode                              false
% 7.65/1.51  --qbf_elim_univ                         false
% 7.65/1.51  --qbf_dom_inst                          none
% 7.65/1.51  --qbf_dom_pre_inst                      false
% 7.65/1.51  --qbf_sk_in                             false
% 7.65/1.51  --qbf_pred_elim                         true
% 7.65/1.51  --qbf_split                             512
% 7.65/1.51  
% 7.65/1.51  ------ BMC1 Options
% 7.65/1.51  
% 7.65/1.51  --bmc1_incremental                      false
% 7.65/1.51  --bmc1_axioms                           reachable_all
% 7.65/1.51  --bmc1_min_bound                        0
% 7.65/1.51  --bmc1_max_bound                        -1
% 7.65/1.51  --bmc1_max_bound_default                -1
% 7.65/1.51  --bmc1_symbol_reachability              true
% 7.65/1.51  --bmc1_property_lemmas                  false
% 7.65/1.51  --bmc1_k_induction                      false
% 7.65/1.51  --bmc1_non_equiv_states                 false
% 7.65/1.51  --bmc1_deadlock                         false
% 7.65/1.51  --bmc1_ucm                              false
% 7.65/1.51  --bmc1_add_unsat_core                   none
% 7.65/1.51  --bmc1_unsat_core_children              false
% 7.65/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.65/1.51  --bmc1_out_stat                         full
% 7.65/1.51  --bmc1_ground_init                      false
% 7.65/1.51  --bmc1_pre_inst_next_state              false
% 7.65/1.51  --bmc1_pre_inst_state                   false
% 7.65/1.51  --bmc1_pre_inst_reach_state             false
% 7.65/1.51  --bmc1_out_unsat_core                   false
% 7.65/1.51  --bmc1_aig_witness_out                  false
% 7.65/1.51  --bmc1_verbose                          false
% 7.65/1.51  --bmc1_dump_clauses_tptp                false
% 7.65/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.65/1.51  --bmc1_dump_file                        -
% 7.65/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.65/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.65/1.51  --bmc1_ucm_extend_mode                  1
% 7.65/1.51  --bmc1_ucm_init_mode                    2
% 7.65/1.51  --bmc1_ucm_cone_mode                    none
% 7.65/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.65/1.51  --bmc1_ucm_relax_model                  4
% 7.65/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.65/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.65/1.51  --bmc1_ucm_layered_model                none
% 7.65/1.51  --bmc1_ucm_max_lemma_size               10
% 7.65/1.51  
% 7.65/1.51  ------ AIG Options
% 7.65/1.51  
% 7.65/1.51  --aig_mode                              false
% 7.65/1.51  
% 7.65/1.51  ------ Instantiation Options
% 7.65/1.51  
% 7.65/1.51  --instantiation_flag                    true
% 7.65/1.51  --inst_sos_flag                         true
% 7.65/1.51  --inst_sos_phase                        true
% 7.65/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.65/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.65/1.51  --inst_lit_sel_side                     none
% 7.65/1.51  --inst_solver_per_active                1400
% 7.65/1.51  --inst_solver_calls_frac                1.
% 7.65/1.51  --inst_passive_queue_type               priority_queues
% 7.65/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.65/1.51  --inst_passive_queues_freq              [25;2]
% 7.65/1.51  --inst_dismatching                      true
% 7.65/1.51  --inst_eager_unprocessed_to_passive     true
% 7.65/1.51  --inst_prop_sim_given                   true
% 7.65/1.51  --inst_prop_sim_new                     false
% 7.65/1.51  --inst_subs_new                         false
% 7.65/1.51  --inst_eq_res_simp                      false
% 7.65/1.51  --inst_subs_given                       false
% 7.65/1.51  --inst_orphan_elimination               true
% 7.65/1.51  --inst_learning_loop_flag               true
% 7.65/1.51  --inst_learning_start                   3000
% 7.65/1.51  --inst_learning_factor                  2
% 7.65/1.51  --inst_start_prop_sim_after_learn       3
% 7.65/1.51  --inst_sel_renew                        solver
% 7.65/1.51  --inst_lit_activity_flag                true
% 7.65/1.51  --inst_restr_to_given                   false
% 7.65/1.51  --inst_activity_threshold               500
% 7.65/1.51  --inst_out_proof                        true
% 7.65/1.51  
% 7.65/1.51  ------ Resolution Options
% 7.65/1.51  
% 7.65/1.51  --resolution_flag                       false
% 7.65/1.51  --res_lit_sel                           adaptive
% 7.65/1.51  --res_lit_sel_side                      none
% 7.65/1.51  --res_ordering                          kbo
% 7.65/1.51  --res_to_prop_solver                    active
% 7.65/1.51  --res_prop_simpl_new                    false
% 7.65/1.51  --res_prop_simpl_given                  true
% 7.65/1.51  --res_passive_queue_type                priority_queues
% 7.65/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.65/1.51  --res_passive_queues_freq               [15;5]
% 7.65/1.51  --res_forward_subs                      full
% 7.65/1.51  --res_backward_subs                     full
% 7.65/1.51  --res_forward_subs_resolution           true
% 7.65/1.51  --res_backward_subs_resolution          true
% 7.65/1.51  --res_orphan_elimination                true
% 7.65/1.51  --res_time_limit                        2.
% 7.65/1.51  --res_out_proof                         true
% 7.65/1.51  
% 7.65/1.51  ------ Superposition Options
% 7.65/1.51  
% 7.65/1.51  --superposition_flag                    true
% 7.65/1.51  --sup_passive_queue_type                priority_queues
% 7.65/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.65/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.65/1.51  --demod_completeness_check              fast
% 7.65/1.51  --demod_use_ground                      true
% 7.65/1.51  --sup_to_prop_solver                    passive
% 7.65/1.51  --sup_prop_simpl_new                    true
% 7.65/1.51  --sup_prop_simpl_given                  true
% 7.65/1.51  --sup_fun_splitting                     true
% 7.65/1.51  --sup_smt_interval                      50000
% 7.65/1.51  
% 7.65/1.51  ------ Superposition Simplification Setup
% 7.65/1.51  
% 7.65/1.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.65/1.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.65/1.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.65/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.65/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.65/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.65/1.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.65/1.51  --sup_immed_triv                        [TrivRules]
% 7.65/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.65/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.65/1.51  --sup_immed_bw_main                     []
% 7.65/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.65/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.65/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.65/1.51  --sup_input_bw                          []
% 7.65/1.51  
% 7.65/1.51  ------ Combination Options
% 7.65/1.51  
% 7.65/1.51  --comb_res_mult                         3
% 7.65/1.51  --comb_sup_mult                         2
% 7.65/1.51  --comb_inst_mult                        10
% 7.65/1.51  
% 7.65/1.51  ------ Debug Options
% 7.65/1.51  
% 7.65/1.51  --dbg_backtrace                         false
% 7.65/1.51  --dbg_dump_prop_clauses                 false
% 7.65/1.51  --dbg_dump_prop_clauses_file            -
% 7.65/1.51  --dbg_out_stat                          false
% 7.65/1.51  
% 7.65/1.51  
% 7.65/1.51  
% 7.65/1.51  
% 7.65/1.51  ------ Proving...
% 7.65/1.51  
% 7.65/1.51  
% 7.65/1.51  % SZS status Theorem for theBenchmark.p
% 7.65/1.51  
% 7.65/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 7.65/1.51  
% 7.65/1.51  fof(f23,conjecture,(
% 7.65/1.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 7.65/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.51  
% 7.65/1.51  fof(f24,negated_conjecture,(
% 7.65/1.51    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 7.65/1.51    inference(negated_conjecture,[],[f23])).
% 7.65/1.51  
% 7.65/1.51  fof(f25,plain,(
% 7.65/1.51    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 7.65/1.51    inference(pure_predicate_removal,[],[f24])).
% 7.65/1.51  
% 7.65/1.51  fof(f58,plain,(
% 7.65/1.51    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 7.65/1.51    inference(ennf_transformation,[],[f25])).
% 7.65/1.51  
% 7.65/1.51  fof(f59,plain,(
% 7.65/1.51    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 7.65/1.51    inference(flattening,[],[f58])).
% 7.65/1.51  
% 7.65/1.51  fof(f65,plain,(
% 7.65/1.51    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(sK3))) )),
% 7.65/1.51    introduced(choice_axiom,[])).
% 7.65/1.51  
% 7.65/1.51  fof(f64,plain,(
% 7.65/1.51    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2))),
% 7.65/1.51    introduced(choice_axiom,[])).
% 7.65/1.51  
% 7.65/1.51  fof(f66,plain,(
% 7.65/1.51    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2)),
% 7.65/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f59,f65,f64])).
% 7.65/1.51  
% 7.65/1.51  fof(f101,plain,(
% 7.65/1.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 7.65/1.51    inference(cnf_transformation,[],[f66])).
% 7.65/1.51  
% 7.65/1.51  fof(f2,axiom,(
% 7.65/1.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 7.65/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.51  
% 7.65/1.51  fof(f29,plain,(
% 7.65/1.51    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 7.65/1.51    inference(ennf_transformation,[],[f2])).
% 7.65/1.51  
% 7.65/1.51  fof(f70,plain,(
% 7.65/1.51    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 7.65/1.51    inference(cnf_transformation,[],[f29])).
% 7.65/1.51  
% 7.65/1.51  fof(f4,axiom,(
% 7.65/1.51    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 7.65/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.51  
% 7.65/1.51  fof(f73,plain,(
% 7.65/1.51    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 7.65/1.51    inference(cnf_transformation,[],[f4])).
% 7.65/1.51  
% 7.65/1.51  fof(f99,plain,(
% 7.65/1.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 7.65/1.51    inference(cnf_transformation,[],[f66])).
% 7.65/1.51  
% 7.65/1.51  fof(f16,axiom,(
% 7.65/1.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 7.65/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.51  
% 7.65/1.51  fof(f49,plain,(
% 7.65/1.51    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.65/1.51    inference(ennf_transformation,[],[f16])).
% 7.65/1.51  
% 7.65/1.51  fof(f88,plain,(
% 7.65/1.51    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.65/1.51    inference(cnf_transformation,[],[f49])).
% 7.65/1.51  
% 7.65/1.51  fof(f102,plain,(
% 7.65/1.51    k2_relset_1(sK0,sK1,sK2) = sK1),
% 7.65/1.51    inference(cnf_transformation,[],[f66])).
% 7.65/1.51  
% 7.65/1.51  fof(f13,axiom,(
% 7.65/1.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 7.65/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.51  
% 7.65/1.51  fof(f44,plain,(
% 7.65/1.51    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.65/1.51    inference(ennf_transformation,[],[f13])).
% 7.65/1.51  
% 7.65/1.51  fof(f45,plain,(
% 7.65/1.51    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.65/1.51    inference(flattening,[],[f44])).
% 7.65/1.51  
% 7.65/1.51  fof(f83,plain,(
% 7.65/1.51    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.65/1.51    inference(cnf_transformation,[],[f45])).
% 7.65/1.51  
% 7.65/1.51  fof(f104,plain,(
% 7.65/1.51    v2_funct_1(sK2)),
% 7.65/1.51    inference(cnf_transformation,[],[f66])).
% 7.65/1.51  
% 7.65/1.51  fof(f98,plain,(
% 7.65/1.51    v1_funct_1(sK2)),
% 7.65/1.51    inference(cnf_transformation,[],[f66])).
% 7.65/1.51  
% 7.65/1.51  fof(f22,axiom,(
% 7.65/1.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 7.65/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.51  
% 7.65/1.51  fof(f26,plain,(
% 7.65/1.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_1(X0)))),
% 7.65/1.51    inference(pure_predicate_removal,[],[f22])).
% 7.65/1.51  
% 7.65/1.51  fof(f56,plain,(
% 7.65/1.51    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.65/1.51    inference(ennf_transformation,[],[f26])).
% 7.65/1.51  
% 7.65/1.51  fof(f57,plain,(
% 7.65/1.51    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.65/1.51    inference(flattening,[],[f56])).
% 7.65/1.51  
% 7.65/1.51  fof(f97,plain,(
% 7.65/1.51    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.65/1.51    inference(cnf_transformation,[],[f57])).
% 7.65/1.51  
% 7.65/1.51  fof(f10,axiom,(
% 7.65/1.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 7.65/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.51  
% 7.65/1.51  fof(f38,plain,(
% 7.65/1.51    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.65/1.51    inference(ennf_transformation,[],[f10])).
% 7.65/1.51  
% 7.65/1.51  fof(f39,plain,(
% 7.65/1.51    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.65/1.51    inference(flattening,[],[f38])).
% 7.65/1.51  
% 7.65/1.51  fof(f79,plain,(
% 7.65/1.51    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.65/1.51    inference(cnf_transformation,[],[f39])).
% 7.65/1.51  
% 7.65/1.51  fof(f80,plain,(
% 7.65/1.51    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.65/1.51    inference(cnf_transformation,[],[f39])).
% 7.65/1.51  
% 7.65/1.51  fof(f84,plain,(
% 7.65/1.51    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.65/1.51    inference(cnf_transformation,[],[f45])).
% 7.65/1.51  
% 7.65/1.51  fof(f7,axiom,(
% 7.65/1.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2))))),
% 7.65/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.51  
% 7.65/1.51  fof(f33,plain,(
% 7.65/1.51    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.65/1.51    inference(ennf_transformation,[],[f7])).
% 7.65/1.51  
% 7.65/1.51  fof(f76,plain,(
% 7.65/1.51    ( ! [X2,X0,X1] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.65/1.51    inference(cnf_transformation,[],[f33])).
% 7.65/1.51  
% 7.65/1.51  fof(f14,axiom,(
% 7.65/1.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 7.65/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.51  
% 7.65/1.51  fof(f46,plain,(
% 7.65/1.51    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.65/1.51    inference(ennf_transformation,[],[f14])).
% 7.65/1.51  
% 7.65/1.51  fof(f47,plain,(
% 7.65/1.51    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.65/1.51    inference(flattening,[],[f46])).
% 7.65/1.51  
% 7.65/1.51  fof(f86,plain,(
% 7.65/1.51    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.65/1.51    inference(cnf_transformation,[],[f47])).
% 7.65/1.51  
% 7.65/1.51  fof(f21,axiom,(
% 7.65/1.51    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 7.65/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.51  
% 7.65/1.51  fof(f95,plain,(
% 7.65/1.51    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 7.65/1.51    inference(cnf_transformation,[],[f21])).
% 7.65/1.51  
% 7.65/1.51  fof(f110,plain,(
% 7.65/1.51    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.65/1.51    inference(definition_unfolding,[],[f86,f95])).
% 7.65/1.51  
% 7.65/1.51  fof(f15,axiom,(
% 7.65/1.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.65/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.51  
% 7.65/1.51  fof(f28,plain,(
% 7.65/1.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 7.65/1.51    inference(pure_predicate_removal,[],[f15])).
% 7.65/1.51  
% 7.65/1.51  fof(f48,plain,(
% 7.65/1.51    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.65/1.51    inference(ennf_transformation,[],[f28])).
% 7.65/1.51  
% 7.65/1.51  fof(f87,plain,(
% 7.65/1.51    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.65/1.51    inference(cnf_transformation,[],[f48])).
% 7.65/1.51  
% 7.65/1.51  fof(f3,axiom,(
% 7.65/1.51    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 7.65/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.51  
% 7.65/1.51  fof(f30,plain,(
% 7.65/1.51    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.65/1.51    inference(ennf_transformation,[],[f3])).
% 7.65/1.51  
% 7.65/1.51  fof(f62,plain,(
% 7.65/1.51    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.65/1.51    inference(nnf_transformation,[],[f30])).
% 7.65/1.51  
% 7.65/1.51  fof(f71,plain,(
% 7.65/1.51    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.65/1.51    inference(cnf_transformation,[],[f62])).
% 7.65/1.51  
% 7.65/1.51  fof(f8,axiom,(
% 7.65/1.51    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 7.65/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.51  
% 7.65/1.51  fof(f34,plain,(
% 7.65/1.51    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.65/1.51    inference(ennf_transformation,[],[f8])).
% 7.65/1.51  
% 7.65/1.51  fof(f35,plain,(
% 7.65/1.51    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 7.65/1.51    inference(flattening,[],[f34])).
% 7.65/1.51  
% 7.65/1.51  fof(f77,plain,(
% 7.65/1.51    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 7.65/1.51    inference(cnf_transformation,[],[f35])).
% 7.65/1.51  
% 7.65/1.51  fof(f108,plain,(
% 7.65/1.51    ( ! [X0,X1] : (k5_relat_1(k6_partfun1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 7.65/1.51    inference(definition_unfolding,[],[f77,f95])).
% 7.65/1.51  
% 7.65/1.51  fof(f20,axiom,(
% 7.65/1.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 7.65/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.51  
% 7.65/1.51  fof(f54,plain,(
% 7.65/1.51    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 7.65/1.51    inference(ennf_transformation,[],[f20])).
% 7.65/1.51  
% 7.65/1.51  fof(f55,plain,(
% 7.65/1.51    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 7.65/1.51    inference(flattening,[],[f54])).
% 7.65/1.51  
% 7.65/1.51  fof(f94,plain,(
% 7.65/1.51    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 7.65/1.51    inference(cnf_transformation,[],[f55])).
% 7.65/1.51  
% 7.65/1.51  fof(f100,plain,(
% 7.65/1.51    v1_funct_1(sK3)),
% 7.65/1.51    inference(cnf_transformation,[],[f66])).
% 7.65/1.51  
% 7.65/1.51  fof(f17,axiom,(
% 7.65/1.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 7.65/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.51  
% 7.65/1.51  fof(f50,plain,(
% 7.65/1.51    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 7.65/1.51    inference(ennf_transformation,[],[f17])).
% 7.65/1.51  
% 7.65/1.51  fof(f51,plain,(
% 7.65/1.51    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.65/1.51    inference(flattening,[],[f50])).
% 7.65/1.51  
% 7.65/1.51  fof(f63,plain,(
% 7.65/1.51    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.65/1.51    inference(nnf_transformation,[],[f51])).
% 7.65/1.51  
% 7.65/1.51  fof(f89,plain,(
% 7.65/1.51    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.65/1.51    inference(cnf_transformation,[],[f63])).
% 7.65/1.51  
% 7.65/1.51  fof(f103,plain,(
% 7.65/1.51    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 7.65/1.51    inference(cnf_transformation,[],[f66])).
% 7.65/1.51  
% 7.65/1.51  fof(f19,axiom,(
% 7.65/1.51    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 7.65/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.51  
% 7.65/1.51  fof(f27,plain,(
% 7.65/1.51    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 7.65/1.51    inference(pure_predicate_removal,[],[f19])).
% 7.65/1.51  
% 7.65/1.51  fof(f93,plain,(
% 7.65/1.51    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 7.65/1.51    inference(cnf_transformation,[],[f27])).
% 7.65/1.51  
% 7.65/1.51  fof(f18,axiom,(
% 7.65/1.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 7.65/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.51  
% 7.65/1.51  fof(f52,plain,(
% 7.65/1.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 7.65/1.51    inference(ennf_transformation,[],[f18])).
% 7.65/1.51  
% 7.65/1.51  fof(f53,plain,(
% 7.65/1.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 7.65/1.51    inference(flattening,[],[f52])).
% 7.65/1.51  
% 7.65/1.51  fof(f92,plain,(
% 7.65/1.51    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 7.65/1.51    inference(cnf_transformation,[],[f53])).
% 7.65/1.51  
% 7.65/1.51  fof(f9,axiom,(
% 7.65/1.51    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 7.65/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.51  
% 7.65/1.51  fof(f36,plain,(
% 7.65/1.51    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.65/1.51    inference(ennf_transformation,[],[f9])).
% 7.65/1.51  
% 7.65/1.51  fof(f37,plain,(
% 7.65/1.51    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 7.65/1.51    inference(flattening,[],[f36])).
% 7.65/1.51  
% 7.65/1.51  fof(f78,plain,(
% 7.65/1.51    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 7.65/1.51    inference(cnf_transformation,[],[f37])).
% 7.65/1.51  
% 7.65/1.51  fof(f109,plain,(
% 7.65/1.51    ( ! [X0,X1] : (k5_relat_1(X1,k6_partfun1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 7.65/1.51    inference(definition_unfolding,[],[f78,f95])).
% 7.65/1.51  
% 7.65/1.51  fof(f107,plain,(
% 7.65/1.51    k2_funct_1(sK2) != sK3),
% 7.65/1.51    inference(cnf_transformation,[],[f66])).
% 7.65/1.51  
% 7.65/1.51  cnf(c_36,negated_conjecture,
% 7.65/1.51      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 7.65/1.51      inference(cnf_transformation,[],[f101]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_1225,plain,
% 7.65/1.51      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 7.65/1.51      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_3,plain,
% 7.65/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.65/1.51      | ~ v1_relat_1(X1)
% 7.65/1.51      | v1_relat_1(X0) ),
% 7.65/1.51      inference(cnf_transformation,[],[f70]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_1241,plain,
% 7.65/1.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.65/1.51      | v1_relat_1(X1) != iProver_top
% 7.65/1.51      | v1_relat_1(X0) = iProver_top ),
% 7.65/1.51      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_2613,plain,
% 7.65/1.51      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 7.65/1.51      | v1_relat_1(sK3) = iProver_top ),
% 7.65/1.51      inference(superposition,[status(thm)],[c_1225,c_1241]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_43,plain,
% 7.65/1.51      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 7.65/1.51      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_1556,plain,
% 7.65/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.65/1.51      | v1_relat_1(X0)
% 7.65/1.51      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 7.65/1.51      inference(instantiation,[status(thm)],[c_3]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_2239,plain,
% 7.65/1.51      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 7.65/1.51      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
% 7.65/1.51      | v1_relat_1(sK3) ),
% 7.65/1.51      inference(instantiation,[status(thm)],[c_1556]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_2240,plain,
% 7.65/1.51      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.65/1.51      | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 7.65/1.51      | v1_relat_1(sK3) = iProver_top ),
% 7.65/1.51      inference(predicate_to_equality,[status(thm)],[c_2239]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_6,plain,
% 7.65/1.51      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 7.65/1.51      inference(cnf_transformation,[],[f73]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_2338,plain,
% 7.65/1.51      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
% 7.65/1.51      inference(instantiation,[status(thm)],[c_6]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_2339,plain,
% 7.65/1.51      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
% 7.65/1.51      inference(predicate_to_equality,[status(thm)],[c_2338]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_2905,plain,
% 7.65/1.51      ( v1_relat_1(sK3) = iProver_top ),
% 7.65/1.51      inference(global_propositional_subsumption,
% 7.65/1.51                [status(thm)],
% 7.65/1.51                [c_2613,c_43,c_2240,c_2339]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_38,negated_conjecture,
% 7.65/1.51      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 7.65/1.51      inference(cnf_transformation,[],[f99]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_1223,plain,
% 7.65/1.51      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.65/1.51      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_2614,plain,
% 7.65/1.51      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 7.65/1.51      | v1_relat_1(sK2) = iProver_top ),
% 7.65/1.51      inference(superposition,[status(thm)],[c_1223,c_1241]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_41,plain,
% 7.65/1.51      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.65/1.51      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_1304,plain,
% 7.65/1.51      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
% 7.65/1.51      | ~ v1_relat_1(X0)
% 7.65/1.51      | v1_relat_1(sK2) ),
% 7.65/1.51      inference(instantiation,[status(thm)],[c_3]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_1361,plain,
% 7.65/1.51      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.65/1.51      | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
% 7.65/1.51      | v1_relat_1(sK2) ),
% 7.65/1.51      inference(instantiation,[status(thm)],[c_1304]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_1561,plain,
% 7.65/1.51      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.65/1.51      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
% 7.65/1.51      | v1_relat_1(sK2) ),
% 7.65/1.51      inference(instantiation,[status(thm)],[c_1361]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_1562,plain,
% 7.65/1.51      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.65/1.51      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 7.65/1.51      | v1_relat_1(sK2) = iProver_top ),
% 7.65/1.51      inference(predicate_to_equality,[status(thm)],[c_1561]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_1729,plain,
% 7.65/1.51      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 7.65/1.51      inference(instantiation,[status(thm)],[c_6]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_1730,plain,
% 7.65/1.51      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 7.65/1.51      inference(predicate_to_equality,[status(thm)],[c_1729]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_3095,plain,
% 7.65/1.51      ( v1_relat_1(sK2) = iProver_top ),
% 7.65/1.51      inference(global_propositional_subsumption,
% 7.65/1.51                [status(thm)],
% 7.65/1.51                [c_2614,c_41,c_1562,c_1730]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_21,plain,
% 7.65/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.65/1.51      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 7.65/1.51      inference(cnf_transformation,[],[f88]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_1231,plain,
% 7.65/1.51      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 7.65/1.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.65/1.51      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_2083,plain,
% 7.65/1.51      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 7.65/1.51      inference(superposition,[status(thm)],[c_1223,c_1231]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_35,negated_conjecture,
% 7.65/1.51      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 7.65/1.51      inference(cnf_transformation,[],[f102]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_2084,plain,
% 7.65/1.51      ( k2_relat_1(sK2) = sK1 ),
% 7.65/1.51      inference(light_normalisation,[status(thm)],[c_2083,c_35]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_17,plain,
% 7.65/1.51      ( ~ v2_funct_1(X0)
% 7.65/1.51      | ~ v1_funct_1(X0)
% 7.65/1.51      | ~ v1_relat_1(X0)
% 7.65/1.51      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 7.65/1.51      inference(cnf_transformation,[],[f83]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_33,negated_conjecture,
% 7.65/1.51      ( v2_funct_1(sK2) ),
% 7.65/1.51      inference(cnf_transformation,[],[f104]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_464,plain,
% 7.65/1.51      ( ~ v1_funct_1(X0)
% 7.65/1.51      | ~ v1_relat_1(X0)
% 7.65/1.51      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 7.65/1.51      | sK2 != X0 ),
% 7.65/1.51      inference(resolution_lifted,[status(thm)],[c_17,c_33]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_465,plain,
% 7.65/1.51      ( ~ v1_funct_1(sK2)
% 7.65/1.51      | ~ v1_relat_1(sK2)
% 7.65/1.51      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 7.65/1.51      inference(unflattening,[status(thm)],[c_464]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_39,negated_conjecture,
% 7.65/1.51      ( v1_funct_1(sK2) ),
% 7.65/1.51      inference(cnf_transformation,[],[f98]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_467,plain,
% 7.65/1.51      ( ~ v1_relat_1(sK2)
% 7.65/1.51      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 7.65/1.51      inference(global_propositional_subsumption,
% 7.65/1.51                [status(thm)],
% 7.65/1.51                [c_465,c_39]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_1217,plain,
% 7.65/1.51      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 7.65/1.51      | v1_relat_1(sK2) != iProver_top ),
% 7.65/1.51      inference(predicate_to_equality,[status(thm)],[c_467]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_1748,plain,
% 7.65/1.51      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 7.65/1.51      inference(global_propositional_subsumption,
% 7.65/1.51                [status(thm)],
% 7.65/1.51                [c_1217,c_39,c_38,c_465,c_1561,c_1729]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_2087,plain,
% 7.65/1.51      ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
% 7.65/1.51      inference(demodulation,[status(thm)],[c_2084,c_1748]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_28,plain,
% 7.65/1.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 7.65/1.51      | ~ v1_funct_1(X0)
% 7.65/1.51      | ~ v1_relat_1(X0) ),
% 7.65/1.51      inference(cnf_transformation,[],[f97]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_1226,plain,
% 7.65/1.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 7.65/1.51      | v1_funct_1(X0) != iProver_top
% 7.65/1.51      | v1_relat_1(X0) != iProver_top ),
% 7.65/1.51      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_2516,plain,
% 7.65/1.51      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2))))) = iProver_top
% 7.65/1.51      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 7.65/1.51      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 7.65/1.51      inference(superposition,[status(thm)],[c_2087,c_1226]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_40,plain,
% 7.65/1.51      ( v1_funct_1(sK2) = iProver_top ),
% 7.65/1.51      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_13,plain,
% 7.65/1.51      ( ~ v1_funct_1(X0)
% 7.65/1.51      | ~ v1_relat_1(X0)
% 7.65/1.51      | v1_relat_1(k2_funct_1(X0)) ),
% 7.65/1.51      inference(cnf_transformation,[],[f79]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_1541,plain,
% 7.65/1.51      ( ~ v1_funct_1(sK2)
% 7.65/1.51      | v1_relat_1(k2_funct_1(sK2))
% 7.65/1.51      | ~ v1_relat_1(sK2) ),
% 7.65/1.51      inference(instantiation,[status(thm)],[c_13]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_1542,plain,
% 7.65/1.51      ( v1_funct_1(sK2) != iProver_top
% 7.65/1.51      | v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 7.65/1.51      | v1_relat_1(sK2) != iProver_top ),
% 7.65/1.51      inference(predicate_to_equality,[status(thm)],[c_1541]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_12,plain,
% 7.65/1.51      ( ~ v1_funct_1(X0)
% 7.65/1.51      | v1_funct_1(k2_funct_1(X0))
% 7.65/1.51      | ~ v1_relat_1(X0) ),
% 7.65/1.51      inference(cnf_transformation,[],[f80]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_1969,plain,
% 7.65/1.51      ( v1_funct_1(k2_funct_1(sK2))
% 7.65/1.51      | ~ v1_funct_1(sK2)
% 7.65/1.51      | ~ v1_relat_1(sK2) ),
% 7.65/1.51      inference(instantiation,[status(thm)],[c_12]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_1970,plain,
% 7.65/1.51      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 7.65/1.51      | v1_funct_1(sK2) != iProver_top
% 7.65/1.51      | v1_relat_1(sK2) != iProver_top ),
% 7.65/1.51      inference(predicate_to_equality,[status(thm)],[c_1969]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_6818,plain,
% 7.65/1.51      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2))))) = iProver_top ),
% 7.65/1.51      inference(global_propositional_subsumption,
% 7.65/1.51                [status(thm)],
% 7.65/1.51                [c_2516,c_40,c_41,c_1542,c_1562,c_1730,c_1970]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_16,plain,
% 7.65/1.51      ( ~ v2_funct_1(X0)
% 7.65/1.51      | ~ v1_funct_1(X0)
% 7.65/1.51      | ~ v1_relat_1(X0)
% 7.65/1.51      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 7.65/1.51      inference(cnf_transformation,[],[f84]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_478,plain,
% 7.65/1.51      ( ~ v1_funct_1(X0)
% 7.65/1.51      | ~ v1_relat_1(X0)
% 7.65/1.51      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 7.65/1.51      | sK2 != X0 ),
% 7.65/1.51      inference(resolution_lifted,[status(thm)],[c_16,c_33]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_479,plain,
% 7.65/1.51      ( ~ v1_funct_1(sK2)
% 7.65/1.51      | ~ v1_relat_1(sK2)
% 7.65/1.51      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 7.65/1.51      inference(unflattening,[status(thm)],[c_478]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_481,plain,
% 7.65/1.51      ( ~ v1_relat_1(sK2)
% 7.65/1.51      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 7.65/1.51      inference(global_propositional_subsumption,
% 7.65/1.51                [status(thm)],
% 7.65/1.51                [c_479,c_39]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_1216,plain,
% 7.65/1.51      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 7.65/1.51      | v1_relat_1(sK2) != iProver_top ),
% 7.65/1.51      inference(predicate_to_equality,[status(thm)],[c_481]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_3101,plain,
% 7.65/1.51      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 7.65/1.51      inference(superposition,[status(thm)],[c_3095,c_1216]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_6822,plain,
% 7.65/1.51      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top ),
% 7.65/1.51      inference(light_normalisation,[status(thm)],[c_6818,c_3101]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_6824,plain,
% 7.65/1.51      ( v1_relat_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))) != iProver_top
% 7.65/1.51      | v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
% 7.65/1.51      inference(superposition,[status(thm)],[c_6822,c_1241]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_6891,plain,
% 7.65/1.51      ( v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
% 7.65/1.51      inference(global_propositional_subsumption,
% 7.65/1.51                [status(thm)],
% 7.65/1.51                [c_6824,c_40,c_41,c_1542,c_1562,c_1730]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_9,plain,
% 7.65/1.51      ( ~ v1_relat_1(X0)
% 7.65/1.51      | ~ v1_relat_1(X1)
% 7.65/1.51      | ~ v1_relat_1(X2)
% 7.65/1.51      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ),
% 7.65/1.51      inference(cnf_transformation,[],[f76]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_1237,plain,
% 7.65/1.51      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
% 7.65/1.51      | v1_relat_1(X0) != iProver_top
% 7.65/1.51      | v1_relat_1(X1) != iProver_top
% 7.65/1.51      | v1_relat_1(X2) != iProver_top ),
% 7.65/1.51      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_6901,plain,
% 7.65/1.51      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1)
% 7.65/1.51      | v1_relat_1(X0) != iProver_top
% 7.65/1.51      | v1_relat_1(X1) != iProver_top ),
% 7.65/1.51      inference(superposition,[status(thm)],[c_6891,c_1237]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_16278,plain,
% 7.65/1.51      ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),X0) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0))
% 7.65/1.51      | v1_relat_1(X0) != iProver_top ),
% 7.65/1.51      inference(superposition,[status(thm)],[c_3095,c_6901]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_18,plain,
% 7.65/1.51      ( ~ v2_funct_1(X0)
% 7.65/1.51      | ~ v1_funct_1(X0)
% 7.65/1.51      | ~ v1_relat_1(X0)
% 7.65/1.51      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
% 7.65/1.51      inference(cnf_transformation,[],[f110]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_450,plain,
% 7.65/1.51      ( ~ v1_funct_1(X0)
% 7.65/1.51      | ~ v1_relat_1(X0)
% 7.65/1.51      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
% 7.65/1.51      | sK2 != X0 ),
% 7.65/1.51      inference(resolution_lifted,[status(thm)],[c_18,c_33]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_451,plain,
% 7.65/1.51      ( ~ v1_funct_1(sK2)
% 7.65/1.51      | ~ v1_relat_1(sK2)
% 7.65/1.51      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 7.65/1.51      inference(unflattening,[status(thm)],[c_450]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_453,plain,
% 7.65/1.51      ( ~ v1_relat_1(sK2)
% 7.65/1.51      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 7.65/1.51      inference(global_propositional_subsumption,
% 7.65/1.51                [status(thm)],
% 7.65/1.51                [c_451,c_39]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_1218,plain,
% 7.65/1.51      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
% 7.65/1.51      | v1_relat_1(sK2) != iProver_top ),
% 7.65/1.51      inference(predicate_to_equality,[status(thm)],[c_453]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_1751,plain,
% 7.65/1.51      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 7.65/1.51      inference(global_propositional_subsumption,
% 7.65/1.51                [status(thm)],
% 7.65/1.51                [c_1218,c_39,c_38,c_451,c_1561,c_1729]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_2086,plain,
% 7.65/1.51      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
% 7.65/1.51      inference(demodulation,[status(thm)],[c_2084,c_1751]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_16286,plain,
% 7.65/1.51      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k6_partfun1(sK1),X0)
% 7.65/1.51      | v1_relat_1(X0) != iProver_top ),
% 7.65/1.51      inference(light_normalisation,[status(thm)],[c_16278,c_2086]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_16529,plain,
% 7.65/1.51      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
% 7.65/1.51      inference(superposition,[status(thm)],[c_2905,c_16286]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_20,plain,
% 7.65/1.51      ( v4_relat_1(X0,X1)
% 7.65/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.65/1.51      inference(cnf_transformation,[],[f87]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_5,plain,
% 7.65/1.51      ( ~ v4_relat_1(X0,X1)
% 7.65/1.51      | r1_tarski(k1_relat_1(X0),X1)
% 7.65/1.51      | ~ v1_relat_1(X0) ),
% 7.65/1.51      inference(cnf_transformation,[],[f71]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_398,plain,
% 7.65/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.65/1.51      | r1_tarski(k1_relat_1(X0),X1)
% 7.65/1.51      | ~ v1_relat_1(X0) ),
% 7.65/1.51      inference(resolution,[status(thm)],[c_20,c_5]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_1221,plain,
% 7.65/1.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.65/1.51      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 7.65/1.51      | v1_relat_1(X0) != iProver_top ),
% 7.65/1.51      inference(predicate_to_equality,[status(thm)],[c_398]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_1979,plain,
% 7.65/1.51      ( r1_tarski(k1_relat_1(sK3),sK1) = iProver_top
% 7.65/1.51      | v1_relat_1(sK3) != iProver_top ),
% 7.65/1.51      inference(superposition,[status(thm)],[c_1225,c_1221]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_10,plain,
% 7.65/1.51      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 7.65/1.51      | ~ v1_relat_1(X0)
% 7.65/1.51      | k5_relat_1(k6_partfun1(X1),X0) = X0 ),
% 7.65/1.51      inference(cnf_transformation,[],[f108]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_1236,plain,
% 7.65/1.51      ( k5_relat_1(k6_partfun1(X0),X1) = X1
% 7.65/1.51      | r1_tarski(k1_relat_1(X1),X0) != iProver_top
% 7.65/1.51      | v1_relat_1(X1) != iProver_top ),
% 7.65/1.51      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_2890,plain,
% 7.65/1.51      ( k5_relat_1(k6_partfun1(sK1),sK3) = sK3
% 7.65/1.51      | v1_relat_1(sK3) != iProver_top ),
% 7.65/1.51      inference(superposition,[status(thm)],[c_1979,c_1236]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_4417,plain,
% 7.65/1.51      ( k5_relat_1(k6_partfun1(sK1),sK3) = sK3 ),
% 7.65/1.51      inference(global_propositional_subsumption,
% 7.65/1.51                [status(thm)],
% 7.65/1.51                [c_2890,c_43,c_2240,c_2339]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_27,plain,
% 7.65/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.65/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.65/1.51      | ~ v1_funct_1(X0)
% 7.65/1.51      | ~ v1_funct_1(X3)
% 7.65/1.51      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 7.65/1.51      inference(cnf_transformation,[],[f94]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_1227,plain,
% 7.65/1.51      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 7.65/1.51      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 7.65/1.51      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.65/1.51      | v1_funct_1(X5) != iProver_top
% 7.65/1.51      | v1_funct_1(X4) != iProver_top ),
% 7.65/1.51      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_3686,plain,
% 7.65/1.51      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 7.65/1.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.65/1.51      | v1_funct_1(X2) != iProver_top
% 7.65/1.51      | v1_funct_1(sK3) != iProver_top ),
% 7.65/1.51      inference(superposition,[status(thm)],[c_1225,c_1227]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_37,negated_conjecture,
% 7.65/1.51      ( v1_funct_1(sK3) ),
% 7.65/1.51      inference(cnf_transformation,[],[f100]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_42,plain,
% 7.65/1.51      ( v1_funct_1(sK3) = iProver_top ),
% 7.65/1.51      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_3872,plain,
% 7.65/1.51      ( v1_funct_1(X2) != iProver_top
% 7.65/1.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.65/1.51      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 7.65/1.51      inference(global_propositional_subsumption,
% 7.65/1.51                [status(thm)],
% 7.65/1.51                [c_3686,c_42]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_3873,plain,
% 7.65/1.51      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 7.65/1.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.65/1.51      | v1_funct_1(X2) != iProver_top ),
% 7.65/1.51      inference(renaming,[status(thm)],[c_3872]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_3882,plain,
% 7.65/1.51      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 7.65/1.51      | v1_funct_1(sK2) != iProver_top ),
% 7.65/1.51      inference(superposition,[status(thm)],[c_1223,c_3873]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_23,plain,
% 7.65/1.51      ( ~ r2_relset_1(X0,X1,X2,X3)
% 7.65/1.51      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.65/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.65/1.51      | X3 = X2 ),
% 7.65/1.51      inference(cnf_transformation,[],[f89]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_34,negated_conjecture,
% 7.65/1.51      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 7.65/1.51      inference(cnf_transformation,[],[f103]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_419,plain,
% 7.65/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.65/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.65/1.51      | X3 = X0
% 7.65/1.51      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 7.65/1.51      | k6_partfun1(sK0) != X3
% 7.65/1.51      | sK0 != X2
% 7.65/1.51      | sK0 != X1 ),
% 7.65/1.51      inference(resolution_lifted,[status(thm)],[c_23,c_34]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_420,plain,
% 7.65/1.51      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.65/1.51      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.65/1.51      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.65/1.51      inference(unflattening,[status(thm)],[c_419]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_26,plain,
% 7.65/1.51      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 7.65/1.51      inference(cnf_transformation,[],[f93]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_54,plain,
% 7.65/1.51      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 7.65/1.51      inference(instantiation,[status(thm)],[c_26]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_422,plain,
% 7.65/1.51      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.65/1.51      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.65/1.51      inference(global_propositional_subsumption,
% 7.65/1.51                [status(thm)],
% 7.65/1.51                [c_420,c_54]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_1220,plain,
% 7.65/1.51      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.65/1.51      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 7.65/1.51      inference(predicate_to_equality,[status(thm)],[c_422]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_24,plain,
% 7.65/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.65/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.65/1.51      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.65/1.51      | ~ v1_funct_1(X0)
% 7.65/1.51      | ~ v1_funct_1(X3) ),
% 7.65/1.51      inference(cnf_transformation,[],[f92]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_1296,plain,
% 7.65/1.51      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.65/1.51      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 7.65/1.51      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.65/1.51      | ~ v1_funct_1(sK3)
% 7.65/1.51      | ~ v1_funct_1(sK2) ),
% 7.65/1.51      inference(instantiation,[status(thm)],[c_24]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_1821,plain,
% 7.65/1.51      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.65/1.51      inference(global_propositional_subsumption,
% 7.65/1.51                [status(thm)],
% 7.65/1.51                [c_1220,c_39,c_38,c_37,c_36,c_54,c_420,c_1296]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_3884,plain,
% 7.65/1.51      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 7.65/1.51      | v1_funct_1(sK2) != iProver_top ),
% 7.65/1.51      inference(light_normalisation,[status(thm)],[c_3882,c_1821]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_4662,plain,
% 7.65/1.51      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 7.65/1.51      inference(global_propositional_subsumption,
% 7.65/1.51                [status(thm)],
% 7.65/1.51                [c_3884,c_40]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_1980,plain,
% 7.65/1.51      ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top
% 7.65/1.51      | v1_relat_1(sK2) != iProver_top ),
% 7.65/1.51      inference(superposition,[status(thm)],[c_1223,c_1221]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_2349,plain,
% 7.65/1.51      ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
% 7.65/1.51      inference(global_propositional_subsumption,
% 7.65/1.51                [status(thm)],
% 7.65/1.51                [c_1980,c_41,c_1562,c_1730]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_11,plain,
% 7.65/1.51      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 7.65/1.51      | ~ v1_relat_1(X0)
% 7.65/1.51      | k5_relat_1(X0,k6_partfun1(X1)) = X0 ),
% 7.65/1.51      inference(cnf_transformation,[],[f109]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_1235,plain,
% 7.65/1.51      ( k5_relat_1(X0,k6_partfun1(X1)) = X0
% 7.65/1.51      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 7.65/1.51      | v1_relat_1(X0) != iProver_top ),
% 7.65/1.51      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_3504,plain,
% 7.65/1.51      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0)) = k2_funct_1(sK2)
% 7.65/1.51      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top
% 7.65/1.51      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 7.65/1.51      inference(superposition,[status(thm)],[c_3101,c_1235]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_9256,plain,
% 7.65/1.51      ( r1_tarski(k1_relat_1(sK2),X0) != iProver_top
% 7.65/1.51      | k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0)) = k2_funct_1(sK2) ),
% 7.65/1.51      inference(global_propositional_subsumption,
% 7.65/1.51                [status(thm)],
% 7.65/1.51                [c_3504,c_40,c_41,c_1542,c_1562,c_1730]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_9257,plain,
% 7.65/1.51      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0)) = k2_funct_1(sK2)
% 7.65/1.51      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
% 7.65/1.51      inference(renaming,[status(thm)],[c_9256]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_9263,plain,
% 7.65/1.51      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k2_funct_1(sK2) ),
% 7.65/1.51      inference(superposition,[status(thm)],[c_2349,c_9257]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_16539,plain,
% 7.65/1.51      ( k2_funct_1(sK2) = sK3 ),
% 7.65/1.51      inference(light_normalisation,
% 7.65/1.51                [status(thm)],
% 7.65/1.51                [c_16529,c_4417,c_4662,c_9263]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(c_30,negated_conjecture,
% 7.65/1.51      ( k2_funct_1(sK2) != sK3 ),
% 7.65/1.51      inference(cnf_transformation,[],[f107]) ).
% 7.65/1.51  
% 7.65/1.51  cnf(contradiction,plain,
% 7.65/1.51      ( $false ),
% 7.65/1.51      inference(minisat,[status(thm)],[c_16539,c_30]) ).
% 7.65/1.51  
% 7.65/1.51  
% 7.65/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.65/1.51  
% 7.65/1.51  ------                               Statistics
% 7.65/1.51  
% 7.65/1.51  ------ General
% 7.65/1.51  
% 7.65/1.51  abstr_ref_over_cycles:                  0
% 7.65/1.51  abstr_ref_under_cycles:                 0
% 7.65/1.51  gc_basic_clause_elim:                   0
% 7.65/1.51  forced_gc_time:                         0
% 7.65/1.51  parsing_time:                           0.01
% 7.65/1.51  unif_index_cands_time:                  0.
% 7.65/1.51  unif_index_add_time:                    0.
% 7.65/1.51  orderings_time:                         0.
% 7.65/1.51  out_proof_time:                         0.014
% 7.65/1.51  total_time:                             0.603
% 7.65/1.51  num_of_symbols:                         54
% 7.65/1.51  num_of_terms:                           23442
% 7.65/1.51  
% 7.65/1.51  ------ Preprocessing
% 7.65/1.51  
% 7.65/1.51  num_of_splits:                          0
% 7.65/1.51  num_of_split_atoms:                     0
% 7.65/1.51  num_of_reused_defs:                     0
% 7.65/1.51  num_eq_ax_congr_red:                    5
% 7.65/1.51  num_of_sem_filtered_clauses:            1
% 7.65/1.51  num_of_subtypes:                        0
% 7.65/1.51  monotx_restored_types:                  0
% 7.65/1.51  sat_num_of_epr_types:                   0
% 7.65/1.51  sat_num_of_non_cyclic_types:            0
% 7.65/1.51  sat_guarded_non_collapsed_types:        0
% 7.65/1.51  num_pure_diseq_elim:                    0
% 7.65/1.51  simp_replaced_by:                       0
% 7.65/1.51  res_preprocessed:                       172
% 7.65/1.51  prep_upred:                             0
% 7.65/1.51  prep_unflattend:                        13
% 7.65/1.51  smt_new_axioms:                         0
% 7.65/1.51  pred_elim_cands:                        4
% 7.65/1.51  pred_elim:                              3
% 7.65/1.51  pred_elim_cl:                           5
% 7.65/1.51  pred_elim_cycles:                       5
% 7.65/1.51  merged_defs:                            0
% 7.65/1.51  merged_defs_ncl:                        0
% 7.65/1.51  bin_hyper_res:                          0
% 7.65/1.51  prep_cycles:                            4
% 7.65/1.51  pred_elim_time:                         0.003
% 7.65/1.51  splitting_time:                         0.
% 7.65/1.51  sem_filter_time:                        0.
% 7.65/1.51  monotx_time:                            0.
% 7.65/1.51  subtype_inf_time:                       0.
% 7.65/1.51  
% 7.65/1.51  ------ Problem properties
% 7.65/1.51  
% 7.65/1.51  clauses:                                33
% 7.65/1.51  conjectures:                            8
% 7.65/1.51  epr:                                    6
% 7.65/1.51  horn:                                   33
% 7.65/1.51  ground:                                 13
% 7.65/1.51  unary:                                  11
% 7.65/1.51  binary:                                 8
% 7.65/1.51  lits:                                   77
% 7.65/1.51  lits_eq:                                19
% 7.65/1.51  fd_pure:                                0
% 7.65/1.51  fd_pseudo:                              0
% 7.65/1.51  fd_cond:                                0
% 7.65/1.51  fd_pseudo_cond:                         1
% 7.65/1.51  ac_symbols:                             0
% 7.65/1.51  
% 7.65/1.51  ------ Propositional Solver
% 7.65/1.51  
% 7.65/1.51  prop_solver_calls:                      34
% 7.65/1.51  prop_fast_solver_calls:                 1524
% 7.65/1.51  smt_solver_calls:                       0
% 7.65/1.51  smt_fast_solver_calls:                  0
% 7.65/1.51  prop_num_of_clauses:                    9308
% 7.65/1.51  prop_preprocess_simplified:             18682
% 7.65/1.51  prop_fo_subsumed:                       142
% 7.65/1.51  prop_solver_time:                       0.
% 7.65/1.51  smt_solver_time:                        0.
% 7.65/1.51  smt_fast_solver_time:                   0.
% 7.65/1.51  prop_fast_solver_time:                  0.
% 7.65/1.51  prop_unsat_core_time:                   0.002
% 7.65/1.51  
% 7.65/1.51  ------ QBF
% 7.65/1.51  
% 7.65/1.51  qbf_q_res:                              0
% 7.65/1.51  qbf_num_tautologies:                    0
% 7.65/1.51  qbf_prep_cycles:                        0
% 7.65/1.51  
% 7.65/1.51  ------ BMC1
% 7.65/1.51  
% 7.65/1.51  bmc1_current_bound:                     -1
% 7.65/1.51  bmc1_last_solved_bound:                 -1
% 7.65/1.51  bmc1_unsat_core_size:                   -1
% 7.65/1.51  bmc1_unsat_core_parents_size:           -1
% 7.65/1.51  bmc1_merge_next_fun:                    0
% 7.65/1.51  bmc1_unsat_core_clauses_time:           0.
% 7.65/1.51  
% 7.65/1.51  ------ Instantiation
% 7.65/1.51  
% 7.65/1.51  inst_num_of_clauses:                    2298
% 7.65/1.51  inst_num_in_passive:                    1058
% 7.65/1.51  inst_num_in_active:                     1101
% 7.65/1.51  inst_num_in_unprocessed:                139
% 7.65/1.51  inst_num_of_loops:                      1210
% 7.65/1.51  inst_num_of_learning_restarts:          0
% 7.65/1.51  inst_num_moves_active_passive:          104
% 7.65/1.51  inst_lit_activity:                      0
% 7.65/1.51  inst_lit_activity_moves:                1
% 7.65/1.51  inst_num_tautologies:                   0
% 7.65/1.51  inst_num_prop_implied:                  0
% 7.65/1.51  inst_num_existing_simplified:           0
% 7.65/1.51  inst_num_eq_res_simplified:             0
% 7.65/1.51  inst_num_child_elim:                    0
% 7.65/1.51  inst_num_of_dismatching_blockings:      587
% 7.65/1.51  inst_num_of_non_proper_insts:           2312
% 7.65/1.51  inst_num_of_duplicates:                 0
% 7.65/1.51  inst_inst_num_from_inst_to_res:         0
% 7.65/1.51  inst_dismatching_checking_time:         0.
% 7.65/1.51  
% 7.65/1.51  ------ Resolution
% 7.65/1.51  
% 7.65/1.51  res_num_of_clauses:                     0
% 7.65/1.51  res_num_in_passive:                     0
% 7.65/1.51  res_num_in_active:                      0
% 7.65/1.51  res_num_of_loops:                       176
% 7.65/1.51  res_forward_subset_subsumed:            155
% 7.65/1.51  res_backward_subset_subsumed:           0
% 7.65/1.51  res_forward_subsumed:                   0
% 7.65/1.51  res_backward_subsumed:                  0
% 7.65/1.51  res_forward_subsumption_resolution:     0
% 7.65/1.51  res_backward_subsumption_resolution:    0
% 7.65/1.51  res_clause_to_clause_subsumption:       1181
% 7.65/1.51  res_orphan_elimination:                 0
% 7.65/1.51  res_tautology_del:                      173
% 7.65/1.51  res_num_eq_res_simplified:              0
% 7.65/1.51  res_num_sel_changes:                    0
% 7.65/1.51  res_moves_from_active_to_pass:          0
% 7.65/1.51  
% 7.65/1.51  ------ Superposition
% 7.65/1.51  
% 7.65/1.51  sup_time_total:                         0.
% 7.65/1.51  sup_time_generating:                    0.
% 7.65/1.51  sup_time_sim_full:                      0.
% 7.65/1.51  sup_time_sim_immed:                     0.
% 7.65/1.51  
% 7.65/1.51  sup_num_of_clauses:                     584
% 7.65/1.51  sup_num_in_active:                      230
% 7.65/1.51  sup_num_in_passive:                     354
% 7.65/1.51  sup_num_of_loops:                       240
% 7.65/1.51  sup_fw_superposition:                   453
% 7.65/1.51  sup_bw_superposition:                   202
% 7.65/1.51  sup_immediate_simplified:               152
% 7.65/1.51  sup_given_eliminated:                   1
% 7.65/1.51  comparisons_done:                       0
% 7.65/1.51  comparisons_avoided:                    0
% 7.65/1.51  
% 7.65/1.51  ------ Simplifications
% 7.65/1.51  
% 7.65/1.51  
% 7.65/1.51  sim_fw_subset_subsumed:                 21
% 7.65/1.51  sim_bw_subset_subsumed:                 27
% 7.65/1.51  sim_fw_subsumed:                        14
% 7.65/1.51  sim_bw_subsumed:                        3
% 7.65/1.51  sim_fw_subsumption_res:                 0
% 7.65/1.51  sim_bw_subsumption_res:                 0
% 7.65/1.51  sim_tautology_del:                      4
% 7.65/1.51  sim_eq_tautology_del:                   27
% 7.65/1.51  sim_eq_res_simp:                        0
% 7.65/1.51  sim_fw_demodulated:                     1
% 7.65/1.51  sim_bw_demodulated:                     9
% 7.65/1.51  sim_light_normalised:                   119
% 7.65/1.51  sim_joinable_taut:                      0
% 7.65/1.51  sim_joinable_simp:                      0
% 7.65/1.51  sim_ac_normalised:                      0
% 7.65/1.51  sim_smt_subsumption:                    0
% 7.65/1.51  
%------------------------------------------------------------------------------
