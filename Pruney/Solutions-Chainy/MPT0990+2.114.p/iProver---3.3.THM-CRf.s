%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:21 EST 2020

% Result     : Theorem 7.82s
% Output     : CNFRefutation 7.82s
% Verified   : 
% Statistics : Number of formulae       :  199 ( 968 expanded)
%              Number of clauses        :  116 ( 307 expanded)
%              Number of leaves         :   20 ( 217 expanded)
%              Depth                    :   24
%              Number of atoms          :  619 (6567 expanded)
%              Number of equality atoms :  249 (2497 expanded)
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

fof(f28,plain,(
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
    inference(cnf_transformation,[],[f28])).

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

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f79,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f78,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f84,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

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

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f27])).

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

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f108,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_partfun1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f76,f95])).

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

fof(f18,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f91,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f112,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f91,f95])).

fof(f19,axiom,(
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
    inference(ennf_transformation,[],[f19])).

fof(f53,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f52])).

fof(f93,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f109,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_partfun1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f77,f95])).

fof(f107,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1269,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1284,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3066,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1269,c_1284])).

cnf(c_43,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_1519,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1932,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1519])).

cnf(c_1933,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1932])).

cnf(c_6,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2041,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2042,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2041])).

cnf(c_3331,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3066,c_43,c_1933,c_2042])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1267,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_3067,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1267,c_1284])).

cnf(c_41,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_1935,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1519])).

cnf(c_1936,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1935])).

cnf(c_2044,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2045,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2044])).

cnf(c_3550,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3067,c_41,c_1936,c_2045])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1275,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2077,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1267,c_1275])).

cnf(c_35,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_2079,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2077,c_35])).

cnf(c_17,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_33,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_484,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_33])).

cnf(c_485,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_484])).

cnf(c_39,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_487,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_485,c_39])).

cnf(c_1260,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_487])).

cnf(c_2088,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK1
    | v1_relat_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2079,c_1260])).

cnf(c_2219,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2088,c_41,c_1936,c_2045])).

cnf(c_28,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1270,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2809,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2))))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2219,c_1270])).

cnf(c_40,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_11,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1508,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1509,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1508])).

cnf(c_12,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1514,plain,
    ( ~ v1_funct_1(sK2)
    | v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1515,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1514])).

cnf(c_7464,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2))))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2809,c_40,c_41,c_1509,c_1515,c_1936,c_2045])).

cnf(c_16,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_498,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_33])).

cnf(c_499,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_498])).

cnf(c_501,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_499,c_39])).

cnf(c_1259,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_501])).

cnf(c_3558,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_3550,c_1259])).

cnf(c_7468,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7464,c_3558])).

cnf(c_7471,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7468,c_1284])).

cnf(c_8768,plain,
    ( v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7471,c_40,c_41,c_1515,c_1936,c_2045])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1281,plain,
    ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_8775,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_8768,c_1281])).

cnf(c_26777,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3550,c_8775])).

cnf(c_18,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_470,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_33])).

cnf(c_471,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(unflattening,[status(thm)],[c_470])).

cnf(c_473,plain,
    ( ~ v1_relat_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_471,c_39])).

cnf(c_1261,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_473])).

cnf(c_2087,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | v1_relat_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2079,c_1261])).

cnf(c_2447,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2087,c_41,c_1936,c_2045])).

cnf(c_26823,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k6_partfun1(sK1),X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_26777,c_2447])).

cnf(c_27850,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
    inference(superposition,[status(thm)],[c_3331,c_26823])).

cnf(c_20,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_5,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_397,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_20,c_5])).

cnf(c_1265,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_397])).

cnf(c_2000,plain,
    ( r1_tarski(k1_relat_1(sK3),sK1) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1269,c_1265])).

cnf(c_2311,plain,
    ( r1_tarski(k1_relat_1(sK3),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2000,c_43,c_1933,c_2042])).

cnf(c_9,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k6_partfun1(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1280,plain,
    ( k5_relat_1(k6_partfun1(X0),X1) = X1
    | r1_tarski(k1_relat_1(X1),X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3294,plain,
    ( k5_relat_1(k6_partfun1(sK1),sK3) = sK3
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2311,c_1280])).

cnf(c_6232,plain,
    ( k5_relat_1(k6_partfun1(sK1),sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3294,c_43,c_1933,c_2042])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1271,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_4705,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1269,c_1271])).

cnf(c_37,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_42,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_5165,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4705,c_42])).

cnf(c_5166,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_5165])).

cnf(c_5178,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1267,c_5166])).

cnf(c_1647,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(X1,X2,X3,X4,X0,sK3) = k5_relat_1(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_1886,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(X2,X3,X0,X1,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1647])).

cnf(c_2099,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(X0,X1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1886])).

cnf(c_2454,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_2099])).

cnf(c_5306,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5178,c_39,c_38,c_37,c_36,c_2454])).

cnf(c_23,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_34,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_418,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_34])).

cnf(c_419,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_418])).

cnf(c_24,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_60,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_421,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_419,c_60])).

cnf(c_1264,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_421])).

cnf(c_5309,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5306,c_1264])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1273,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_5311,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5306,c_1273])).

cnf(c_7874,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5309,c_40,c_41,c_42,c_43,c_5311])).

cnf(c_2001,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1267,c_1265])).

cnf(c_2317,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2001,c_41,c_1936,c_2045])).

cnf(c_10,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_partfun1(X1)) = X0 ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1279,plain,
    ( k5_relat_1(X0,k6_partfun1(X1)) = X0
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4280,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0)) = k2_funct_1(sK2)
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3558,c_1279])).

cnf(c_10723,plain,
    ( r1_tarski(k1_relat_1(sK2),X0) != iProver_top
    | k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0)) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4280,c_40,c_41,c_1515,c_1936,c_2045])).

cnf(c_10724,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0)) = k2_funct_1(sK2)
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_10723])).

cnf(c_10732,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k2_funct_1(sK2) ),
    inference(superposition,[status(thm)],[c_2317,c_10724])).

cnf(c_27878,plain,
    ( k2_funct_1(sK2) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_27850,c_6232,c_7874,c_10732])).

cnf(c_30,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f107])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_27878,c_30])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:41:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.82/1.52  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.82/1.52  
% 7.82/1.52  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.82/1.52  
% 7.82/1.52  ------  iProver source info
% 7.82/1.52  
% 7.82/1.52  git: date: 2020-06-30 10:37:57 +0100
% 7.82/1.52  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.82/1.52  git: non_committed_changes: false
% 7.82/1.52  git: last_make_outside_of_git: false
% 7.82/1.52  
% 7.82/1.52  ------ 
% 7.82/1.52  
% 7.82/1.52  ------ Input Options
% 7.82/1.52  
% 7.82/1.52  --out_options                           all
% 7.82/1.52  --tptp_safe_out                         true
% 7.82/1.52  --problem_path                          ""
% 7.82/1.52  --include_path                          ""
% 7.82/1.52  --clausifier                            res/vclausify_rel
% 7.82/1.52  --clausifier_options                    --mode clausify
% 7.82/1.52  --stdin                                 false
% 7.82/1.52  --stats_out                             all
% 7.82/1.52  
% 7.82/1.52  ------ General Options
% 7.82/1.52  
% 7.82/1.52  --fof                                   false
% 7.82/1.52  --time_out_real                         305.
% 7.82/1.52  --time_out_virtual                      -1.
% 7.82/1.52  --symbol_type_check                     false
% 7.82/1.52  --clausify_out                          false
% 7.82/1.52  --sig_cnt_out                           false
% 7.82/1.52  --trig_cnt_out                          false
% 7.82/1.52  --trig_cnt_out_tolerance                1.
% 7.82/1.52  --trig_cnt_out_sk_spl                   false
% 7.82/1.52  --abstr_cl_out                          false
% 7.82/1.52  
% 7.82/1.52  ------ Global Options
% 7.82/1.52  
% 7.82/1.52  --schedule                              default
% 7.82/1.52  --add_important_lit                     false
% 7.82/1.52  --prop_solver_per_cl                    1000
% 7.82/1.52  --min_unsat_core                        false
% 7.82/1.52  --soft_assumptions                      false
% 7.82/1.52  --soft_lemma_size                       3
% 7.82/1.52  --prop_impl_unit_size                   0
% 7.82/1.52  --prop_impl_unit                        []
% 7.82/1.52  --share_sel_clauses                     true
% 7.82/1.52  --reset_solvers                         false
% 7.82/1.52  --bc_imp_inh                            [conj_cone]
% 7.82/1.52  --conj_cone_tolerance                   3.
% 7.82/1.52  --extra_neg_conj                        none
% 7.82/1.52  --large_theory_mode                     true
% 7.82/1.52  --prolific_symb_bound                   200
% 7.82/1.52  --lt_threshold                          2000
% 7.82/1.52  --clause_weak_htbl                      true
% 7.82/1.52  --gc_record_bc_elim                     false
% 7.82/1.52  
% 7.82/1.52  ------ Preprocessing Options
% 7.82/1.52  
% 7.82/1.52  --preprocessing_flag                    true
% 7.82/1.52  --time_out_prep_mult                    0.1
% 7.82/1.52  --splitting_mode                        input
% 7.82/1.52  --splitting_grd                         true
% 7.82/1.52  --splitting_cvd                         false
% 7.82/1.52  --splitting_cvd_svl                     false
% 7.82/1.52  --splitting_nvd                         32
% 7.82/1.52  --sub_typing                            true
% 7.82/1.52  --prep_gs_sim                           true
% 7.82/1.52  --prep_unflatten                        true
% 7.82/1.52  --prep_res_sim                          true
% 7.82/1.52  --prep_upred                            true
% 7.82/1.52  --prep_sem_filter                       exhaustive
% 7.82/1.52  --prep_sem_filter_out                   false
% 7.82/1.52  --pred_elim                             true
% 7.82/1.52  --res_sim_input                         true
% 7.82/1.52  --eq_ax_congr_red                       true
% 7.82/1.52  --pure_diseq_elim                       true
% 7.82/1.52  --brand_transform                       false
% 7.82/1.52  --non_eq_to_eq                          false
% 7.82/1.52  --prep_def_merge                        true
% 7.82/1.52  --prep_def_merge_prop_impl              false
% 7.82/1.52  --prep_def_merge_mbd                    true
% 7.82/1.52  --prep_def_merge_tr_red                 false
% 7.82/1.52  --prep_def_merge_tr_cl                  false
% 7.82/1.52  --smt_preprocessing                     true
% 7.82/1.52  --smt_ac_axioms                         fast
% 7.82/1.52  --preprocessed_out                      false
% 7.82/1.52  --preprocessed_stats                    false
% 7.82/1.52  
% 7.82/1.52  ------ Abstraction refinement Options
% 7.82/1.52  
% 7.82/1.52  --abstr_ref                             []
% 7.82/1.52  --abstr_ref_prep                        false
% 7.82/1.52  --abstr_ref_until_sat                   false
% 7.82/1.52  --abstr_ref_sig_restrict                funpre
% 7.82/1.52  --abstr_ref_af_restrict_to_split_sk     false
% 7.82/1.52  --abstr_ref_under                       []
% 7.82/1.52  
% 7.82/1.52  ------ SAT Options
% 7.82/1.52  
% 7.82/1.52  --sat_mode                              false
% 7.82/1.52  --sat_fm_restart_options                ""
% 7.82/1.52  --sat_gr_def                            false
% 7.82/1.52  --sat_epr_types                         true
% 7.82/1.52  --sat_non_cyclic_types                  false
% 7.82/1.52  --sat_finite_models                     false
% 7.82/1.52  --sat_fm_lemmas                         false
% 7.82/1.52  --sat_fm_prep                           false
% 7.82/1.52  --sat_fm_uc_incr                        true
% 7.82/1.52  --sat_out_model                         small
% 7.82/1.52  --sat_out_clauses                       false
% 7.82/1.52  
% 7.82/1.52  ------ QBF Options
% 7.82/1.52  
% 7.82/1.52  --qbf_mode                              false
% 7.82/1.52  --qbf_elim_univ                         false
% 7.82/1.52  --qbf_dom_inst                          none
% 7.82/1.52  --qbf_dom_pre_inst                      false
% 7.82/1.52  --qbf_sk_in                             false
% 7.82/1.52  --qbf_pred_elim                         true
% 7.82/1.52  --qbf_split                             512
% 7.82/1.52  
% 7.82/1.52  ------ BMC1 Options
% 7.82/1.52  
% 7.82/1.52  --bmc1_incremental                      false
% 7.82/1.52  --bmc1_axioms                           reachable_all
% 7.82/1.52  --bmc1_min_bound                        0
% 7.82/1.52  --bmc1_max_bound                        -1
% 7.82/1.52  --bmc1_max_bound_default                -1
% 7.82/1.52  --bmc1_symbol_reachability              true
% 7.82/1.52  --bmc1_property_lemmas                  false
% 7.82/1.52  --bmc1_k_induction                      false
% 7.82/1.52  --bmc1_non_equiv_states                 false
% 7.82/1.52  --bmc1_deadlock                         false
% 7.82/1.52  --bmc1_ucm                              false
% 7.82/1.52  --bmc1_add_unsat_core                   none
% 7.82/1.52  --bmc1_unsat_core_children              false
% 7.82/1.52  --bmc1_unsat_core_extrapolate_axioms    false
% 7.82/1.52  --bmc1_out_stat                         full
% 7.82/1.52  --bmc1_ground_init                      false
% 7.82/1.52  --bmc1_pre_inst_next_state              false
% 7.82/1.52  --bmc1_pre_inst_state                   false
% 7.82/1.52  --bmc1_pre_inst_reach_state             false
% 7.82/1.52  --bmc1_out_unsat_core                   false
% 7.82/1.52  --bmc1_aig_witness_out                  false
% 7.82/1.52  --bmc1_verbose                          false
% 7.82/1.52  --bmc1_dump_clauses_tptp                false
% 7.82/1.52  --bmc1_dump_unsat_core_tptp             false
% 7.82/1.52  --bmc1_dump_file                        -
% 7.82/1.52  --bmc1_ucm_expand_uc_limit              128
% 7.82/1.52  --bmc1_ucm_n_expand_iterations          6
% 7.82/1.52  --bmc1_ucm_extend_mode                  1
% 7.82/1.52  --bmc1_ucm_init_mode                    2
% 7.82/1.52  --bmc1_ucm_cone_mode                    none
% 7.82/1.52  --bmc1_ucm_reduced_relation_type        0
% 7.82/1.52  --bmc1_ucm_relax_model                  4
% 7.82/1.52  --bmc1_ucm_full_tr_after_sat            true
% 7.82/1.52  --bmc1_ucm_expand_neg_assumptions       false
% 7.82/1.52  --bmc1_ucm_layered_model                none
% 7.82/1.52  --bmc1_ucm_max_lemma_size               10
% 7.82/1.52  
% 7.82/1.52  ------ AIG Options
% 7.82/1.52  
% 7.82/1.52  --aig_mode                              false
% 7.82/1.52  
% 7.82/1.52  ------ Instantiation Options
% 7.82/1.52  
% 7.82/1.52  --instantiation_flag                    true
% 7.82/1.52  --inst_sos_flag                         false
% 7.82/1.52  --inst_sos_phase                        true
% 7.82/1.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.82/1.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.82/1.52  --inst_lit_sel_side                     num_symb
% 7.82/1.52  --inst_solver_per_active                1400
% 7.82/1.52  --inst_solver_calls_frac                1.
% 7.82/1.52  --inst_passive_queue_type               priority_queues
% 7.82/1.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.82/1.52  --inst_passive_queues_freq              [25;2]
% 7.82/1.52  --inst_dismatching                      true
% 7.82/1.52  --inst_eager_unprocessed_to_passive     true
% 7.82/1.52  --inst_prop_sim_given                   true
% 7.82/1.52  --inst_prop_sim_new                     false
% 7.82/1.52  --inst_subs_new                         false
% 7.82/1.52  --inst_eq_res_simp                      false
% 7.82/1.52  --inst_subs_given                       false
% 7.82/1.52  --inst_orphan_elimination               true
% 7.82/1.52  --inst_learning_loop_flag               true
% 7.82/1.52  --inst_learning_start                   3000
% 7.82/1.52  --inst_learning_factor                  2
% 7.82/1.52  --inst_start_prop_sim_after_learn       3
% 7.82/1.52  --inst_sel_renew                        solver
% 7.82/1.52  --inst_lit_activity_flag                true
% 7.82/1.52  --inst_restr_to_given                   false
% 7.82/1.52  --inst_activity_threshold               500
% 7.82/1.52  --inst_out_proof                        true
% 7.82/1.52  
% 7.82/1.52  ------ Resolution Options
% 7.82/1.52  
% 7.82/1.52  --resolution_flag                       true
% 7.82/1.52  --res_lit_sel                           adaptive
% 7.82/1.52  --res_lit_sel_side                      none
% 7.82/1.52  --res_ordering                          kbo
% 7.82/1.52  --res_to_prop_solver                    active
% 7.82/1.52  --res_prop_simpl_new                    false
% 7.82/1.52  --res_prop_simpl_given                  true
% 7.82/1.52  --res_passive_queue_type                priority_queues
% 7.82/1.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.82/1.52  --res_passive_queues_freq               [15;5]
% 7.82/1.52  --res_forward_subs                      full
% 7.82/1.52  --res_backward_subs                     full
% 7.82/1.52  --res_forward_subs_resolution           true
% 7.82/1.52  --res_backward_subs_resolution          true
% 7.82/1.52  --res_orphan_elimination                true
% 7.82/1.52  --res_time_limit                        2.
% 7.82/1.52  --res_out_proof                         true
% 7.82/1.52  
% 7.82/1.52  ------ Superposition Options
% 7.82/1.52  
% 7.82/1.52  --superposition_flag                    true
% 7.82/1.52  --sup_passive_queue_type                priority_queues
% 7.82/1.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.82/1.52  --sup_passive_queues_freq               [8;1;4]
% 7.82/1.52  --demod_completeness_check              fast
% 7.82/1.52  --demod_use_ground                      true
% 7.82/1.52  --sup_to_prop_solver                    passive
% 7.82/1.52  --sup_prop_simpl_new                    true
% 7.82/1.52  --sup_prop_simpl_given                  true
% 7.82/1.52  --sup_fun_splitting                     false
% 7.82/1.52  --sup_smt_interval                      50000
% 7.82/1.52  
% 7.82/1.52  ------ Superposition Simplification Setup
% 7.82/1.52  
% 7.82/1.52  --sup_indices_passive                   []
% 7.82/1.52  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.82/1.52  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.82/1.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.82/1.52  --sup_full_triv                         [TrivRules;PropSubs]
% 7.82/1.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.82/1.52  --sup_full_bw                           [BwDemod]
% 7.82/1.52  --sup_immed_triv                        [TrivRules]
% 7.82/1.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.82/1.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.82/1.52  --sup_immed_bw_main                     []
% 7.82/1.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.82/1.52  --sup_input_triv                        [Unflattening;TrivRules]
% 7.82/1.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.82/1.52  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.82/1.52  
% 7.82/1.52  ------ Combination Options
% 7.82/1.52  
% 7.82/1.52  --comb_res_mult                         3
% 7.82/1.52  --comb_sup_mult                         2
% 7.82/1.52  --comb_inst_mult                        10
% 7.82/1.52  
% 7.82/1.52  ------ Debug Options
% 7.82/1.52  
% 7.82/1.52  --dbg_backtrace                         false
% 7.82/1.52  --dbg_dump_prop_clauses                 false
% 7.82/1.52  --dbg_dump_prop_clauses_file            -
% 7.82/1.52  --dbg_out_stat                          false
% 7.82/1.52  ------ Parsing...
% 7.82/1.52  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.82/1.52  
% 7.82/1.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.82/1.52  
% 7.82/1.52  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.82/1.52  
% 7.82/1.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.82/1.52  ------ Proving...
% 7.82/1.52  ------ Problem Properties 
% 7.82/1.52  
% 7.82/1.52  
% 7.82/1.52  clauses                                 33
% 7.82/1.52  conjectures                             8
% 7.82/1.52  EPR                                     6
% 7.82/1.52  Horn                                    33
% 7.82/1.52  unary                                   11
% 7.82/1.52  binary                                  8
% 7.82/1.52  lits                                    77
% 7.82/1.52  lits eq                                 19
% 7.82/1.52  fd_pure                                 0
% 7.82/1.52  fd_pseudo                               0
% 7.82/1.52  fd_cond                                 0
% 7.82/1.52  fd_pseudo_cond                          1
% 7.82/1.52  AC symbols                              0
% 7.82/1.52  
% 7.82/1.52  ------ Schedule dynamic 5 is on 
% 7.82/1.52  
% 7.82/1.52  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.82/1.52  
% 7.82/1.52  
% 7.82/1.52  ------ 
% 7.82/1.52  Current options:
% 7.82/1.52  ------ 
% 7.82/1.52  
% 7.82/1.52  ------ Input Options
% 7.82/1.52  
% 7.82/1.52  --out_options                           all
% 7.82/1.52  --tptp_safe_out                         true
% 7.82/1.52  --problem_path                          ""
% 7.82/1.52  --include_path                          ""
% 7.82/1.52  --clausifier                            res/vclausify_rel
% 7.82/1.52  --clausifier_options                    --mode clausify
% 7.82/1.52  --stdin                                 false
% 7.82/1.52  --stats_out                             all
% 7.82/1.52  
% 7.82/1.52  ------ General Options
% 7.82/1.52  
% 7.82/1.52  --fof                                   false
% 7.82/1.52  --time_out_real                         305.
% 7.82/1.52  --time_out_virtual                      -1.
% 7.82/1.52  --symbol_type_check                     false
% 7.82/1.52  --clausify_out                          false
% 7.82/1.52  --sig_cnt_out                           false
% 7.82/1.52  --trig_cnt_out                          false
% 7.82/1.52  --trig_cnt_out_tolerance                1.
% 7.82/1.52  --trig_cnt_out_sk_spl                   false
% 7.82/1.52  --abstr_cl_out                          false
% 7.82/1.52  
% 7.82/1.52  ------ Global Options
% 7.82/1.52  
% 7.82/1.52  --schedule                              default
% 7.82/1.52  --add_important_lit                     false
% 7.82/1.52  --prop_solver_per_cl                    1000
% 7.82/1.52  --min_unsat_core                        false
% 7.82/1.52  --soft_assumptions                      false
% 7.82/1.52  --soft_lemma_size                       3
% 7.82/1.52  --prop_impl_unit_size                   0
% 7.82/1.52  --prop_impl_unit                        []
% 7.82/1.52  --share_sel_clauses                     true
% 7.82/1.52  --reset_solvers                         false
% 7.82/1.52  --bc_imp_inh                            [conj_cone]
% 7.82/1.52  --conj_cone_tolerance                   3.
% 7.82/1.52  --extra_neg_conj                        none
% 7.82/1.52  --large_theory_mode                     true
% 7.82/1.52  --prolific_symb_bound                   200
% 7.82/1.52  --lt_threshold                          2000
% 7.82/1.52  --clause_weak_htbl                      true
% 7.82/1.52  --gc_record_bc_elim                     false
% 7.82/1.52  
% 7.82/1.52  ------ Preprocessing Options
% 7.82/1.52  
% 7.82/1.52  --preprocessing_flag                    true
% 7.82/1.52  --time_out_prep_mult                    0.1
% 7.82/1.52  --splitting_mode                        input
% 7.82/1.52  --splitting_grd                         true
% 7.82/1.52  --splitting_cvd                         false
% 7.82/1.52  --splitting_cvd_svl                     false
% 7.82/1.52  --splitting_nvd                         32
% 7.82/1.52  --sub_typing                            true
% 7.82/1.52  --prep_gs_sim                           true
% 7.82/1.52  --prep_unflatten                        true
% 7.82/1.52  --prep_res_sim                          true
% 7.82/1.52  --prep_upred                            true
% 7.82/1.52  --prep_sem_filter                       exhaustive
% 7.82/1.52  --prep_sem_filter_out                   false
% 7.82/1.52  --pred_elim                             true
% 7.82/1.52  --res_sim_input                         true
% 7.82/1.52  --eq_ax_congr_red                       true
% 7.82/1.52  --pure_diseq_elim                       true
% 7.82/1.52  --brand_transform                       false
% 7.82/1.52  --non_eq_to_eq                          false
% 7.82/1.52  --prep_def_merge                        true
% 7.82/1.52  --prep_def_merge_prop_impl              false
% 7.82/1.52  --prep_def_merge_mbd                    true
% 7.82/1.52  --prep_def_merge_tr_red                 false
% 7.82/1.52  --prep_def_merge_tr_cl                  false
% 7.82/1.52  --smt_preprocessing                     true
% 7.82/1.52  --smt_ac_axioms                         fast
% 7.82/1.52  --preprocessed_out                      false
% 7.82/1.52  --preprocessed_stats                    false
% 7.82/1.52  
% 7.82/1.52  ------ Abstraction refinement Options
% 7.82/1.52  
% 7.82/1.52  --abstr_ref                             []
% 7.82/1.52  --abstr_ref_prep                        false
% 7.82/1.52  --abstr_ref_until_sat                   false
% 7.82/1.52  --abstr_ref_sig_restrict                funpre
% 7.82/1.52  --abstr_ref_af_restrict_to_split_sk     false
% 7.82/1.52  --abstr_ref_under                       []
% 7.82/1.52  
% 7.82/1.52  ------ SAT Options
% 7.82/1.52  
% 7.82/1.52  --sat_mode                              false
% 7.82/1.52  --sat_fm_restart_options                ""
% 7.82/1.52  --sat_gr_def                            false
% 7.82/1.52  --sat_epr_types                         true
% 7.82/1.52  --sat_non_cyclic_types                  false
% 7.82/1.52  --sat_finite_models                     false
% 7.82/1.52  --sat_fm_lemmas                         false
% 7.82/1.52  --sat_fm_prep                           false
% 7.82/1.52  --sat_fm_uc_incr                        true
% 7.82/1.52  --sat_out_model                         small
% 7.82/1.52  --sat_out_clauses                       false
% 7.82/1.52  
% 7.82/1.52  ------ QBF Options
% 7.82/1.52  
% 7.82/1.52  --qbf_mode                              false
% 7.82/1.52  --qbf_elim_univ                         false
% 7.82/1.52  --qbf_dom_inst                          none
% 7.82/1.52  --qbf_dom_pre_inst                      false
% 7.82/1.52  --qbf_sk_in                             false
% 7.82/1.52  --qbf_pred_elim                         true
% 7.82/1.52  --qbf_split                             512
% 7.82/1.52  
% 7.82/1.52  ------ BMC1 Options
% 7.82/1.52  
% 7.82/1.52  --bmc1_incremental                      false
% 7.82/1.52  --bmc1_axioms                           reachable_all
% 7.82/1.52  --bmc1_min_bound                        0
% 7.82/1.52  --bmc1_max_bound                        -1
% 7.82/1.52  --bmc1_max_bound_default                -1
% 7.82/1.52  --bmc1_symbol_reachability              true
% 7.82/1.52  --bmc1_property_lemmas                  false
% 7.82/1.52  --bmc1_k_induction                      false
% 7.82/1.52  --bmc1_non_equiv_states                 false
% 7.82/1.52  --bmc1_deadlock                         false
% 7.82/1.52  --bmc1_ucm                              false
% 7.82/1.52  --bmc1_add_unsat_core                   none
% 7.82/1.52  --bmc1_unsat_core_children              false
% 7.82/1.52  --bmc1_unsat_core_extrapolate_axioms    false
% 7.82/1.52  --bmc1_out_stat                         full
% 7.82/1.52  --bmc1_ground_init                      false
% 7.82/1.52  --bmc1_pre_inst_next_state              false
% 7.82/1.52  --bmc1_pre_inst_state                   false
% 7.82/1.52  --bmc1_pre_inst_reach_state             false
% 7.82/1.52  --bmc1_out_unsat_core                   false
% 7.82/1.52  --bmc1_aig_witness_out                  false
% 7.82/1.52  --bmc1_verbose                          false
% 7.82/1.52  --bmc1_dump_clauses_tptp                false
% 7.82/1.52  --bmc1_dump_unsat_core_tptp             false
% 7.82/1.52  --bmc1_dump_file                        -
% 7.82/1.52  --bmc1_ucm_expand_uc_limit              128
% 7.82/1.52  --bmc1_ucm_n_expand_iterations          6
% 7.82/1.52  --bmc1_ucm_extend_mode                  1
% 7.82/1.52  --bmc1_ucm_init_mode                    2
% 7.82/1.52  --bmc1_ucm_cone_mode                    none
% 7.82/1.52  --bmc1_ucm_reduced_relation_type        0
% 7.82/1.52  --bmc1_ucm_relax_model                  4
% 7.82/1.52  --bmc1_ucm_full_tr_after_sat            true
% 7.82/1.52  --bmc1_ucm_expand_neg_assumptions       false
% 7.82/1.52  --bmc1_ucm_layered_model                none
% 7.82/1.52  --bmc1_ucm_max_lemma_size               10
% 7.82/1.52  
% 7.82/1.52  ------ AIG Options
% 7.82/1.52  
% 7.82/1.52  --aig_mode                              false
% 7.82/1.52  
% 7.82/1.52  ------ Instantiation Options
% 7.82/1.52  
% 7.82/1.52  --instantiation_flag                    true
% 7.82/1.52  --inst_sos_flag                         false
% 7.82/1.52  --inst_sos_phase                        true
% 7.82/1.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.82/1.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.82/1.52  --inst_lit_sel_side                     none
% 7.82/1.52  --inst_solver_per_active                1400
% 7.82/1.52  --inst_solver_calls_frac                1.
% 7.82/1.52  --inst_passive_queue_type               priority_queues
% 7.82/1.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.82/1.52  --inst_passive_queues_freq              [25;2]
% 7.82/1.52  --inst_dismatching                      true
% 7.82/1.52  --inst_eager_unprocessed_to_passive     true
% 7.82/1.52  --inst_prop_sim_given                   true
% 7.82/1.52  --inst_prop_sim_new                     false
% 7.82/1.52  --inst_subs_new                         false
% 7.82/1.52  --inst_eq_res_simp                      false
% 7.82/1.52  --inst_subs_given                       false
% 7.82/1.52  --inst_orphan_elimination               true
% 7.82/1.52  --inst_learning_loop_flag               true
% 7.82/1.52  --inst_learning_start                   3000
% 7.82/1.52  --inst_learning_factor                  2
% 7.82/1.52  --inst_start_prop_sim_after_learn       3
% 7.82/1.52  --inst_sel_renew                        solver
% 7.82/1.52  --inst_lit_activity_flag                true
% 7.82/1.52  --inst_restr_to_given                   false
% 7.82/1.52  --inst_activity_threshold               500
% 7.82/1.52  --inst_out_proof                        true
% 7.82/1.52  
% 7.82/1.52  ------ Resolution Options
% 7.82/1.52  
% 7.82/1.52  --resolution_flag                       false
% 7.82/1.52  --res_lit_sel                           adaptive
% 7.82/1.52  --res_lit_sel_side                      none
% 7.82/1.52  --res_ordering                          kbo
% 7.82/1.52  --res_to_prop_solver                    active
% 7.82/1.52  --res_prop_simpl_new                    false
% 7.82/1.52  --res_prop_simpl_given                  true
% 7.82/1.52  --res_passive_queue_type                priority_queues
% 7.82/1.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.82/1.52  --res_passive_queues_freq               [15;5]
% 7.82/1.52  --res_forward_subs                      full
% 7.82/1.52  --res_backward_subs                     full
% 7.82/1.52  --res_forward_subs_resolution           true
% 7.82/1.52  --res_backward_subs_resolution          true
% 7.82/1.52  --res_orphan_elimination                true
% 7.82/1.52  --res_time_limit                        2.
% 7.82/1.52  --res_out_proof                         true
% 7.82/1.52  
% 7.82/1.52  ------ Superposition Options
% 7.82/1.52  
% 7.82/1.52  --superposition_flag                    true
% 7.82/1.52  --sup_passive_queue_type                priority_queues
% 7.82/1.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.82/1.52  --sup_passive_queues_freq               [8;1;4]
% 7.82/1.52  --demod_completeness_check              fast
% 7.82/1.52  --demod_use_ground                      true
% 7.82/1.52  --sup_to_prop_solver                    passive
% 7.82/1.52  --sup_prop_simpl_new                    true
% 7.82/1.52  --sup_prop_simpl_given                  true
% 7.82/1.52  --sup_fun_splitting                     false
% 7.82/1.52  --sup_smt_interval                      50000
% 7.82/1.52  
% 7.82/1.52  ------ Superposition Simplification Setup
% 7.82/1.52  
% 7.82/1.52  --sup_indices_passive                   []
% 7.82/1.52  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.82/1.52  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.82/1.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.82/1.52  --sup_full_triv                         [TrivRules;PropSubs]
% 7.82/1.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.82/1.52  --sup_full_bw                           [BwDemod]
% 7.82/1.52  --sup_immed_triv                        [TrivRules]
% 7.82/1.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.82/1.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.82/1.52  --sup_immed_bw_main                     []
% 7.82/1.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.82/1.52  --sup_input_triv                        [Unflattening;TrivRules]
% 7.82/1.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.82/1.52  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.82/1.52  
% 7.82/1.52  ------ Combination Options
% 7.82/1.52  
% 7.82/1.52  --comb_res_mult                         3
% 7.82/1.52  --comb_sup_mult                         2
% 7.82/1.52  --comb_inst_mult                        10
% 7.82/1.52  
% 7.82/1.52  ------ Debug Options
% 7.82/1.52  
% 7.82/1.52  --dbg_backtrace                         false
% 7.82/1.52  --dbg_dump_prop_clauses                 false
% 7.82/1.52  --dbg_dump_prop_clauses_file            -
% 7.82/1.52  --dbg_out_stat                          false
% 7.82/1.52  
% 7.82/1.52  
% 7.82/1.52  
% 7.82/1.52  
% 7.82/1.52  ------ Proving...
% 7.82/1.52  
% 7.82/1.52  
% 7.82/1.52  % SZS status Theorem for theBenchmark.p
% 7.82/1.52  
% 7.82/1.52  % SZS output start CNFRefutation for theBenchmark.p
% 7.82/1.52  
% 7.82/1.52  fof(f23,conjecture,(
% 7.82/1.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 7.82/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.52  
% 7.82/1.52  fof(f24,negated_conjecture,(
% 7.82/1.52    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 7.82/1.52    inference(negated_conjecture,[],[f23])).
% 7.82/1.52  
% 7.82/1.52  fof(f25,plain,(
% 7.82/1.52    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 7.82/1.52    inference(pure_predicate_removal,[],[f24])).
% 7.82/1.52  
% 7.82/1.52  fof(f58,plain,(
% 7.82/1.52    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 7.82/1.52    inference(ennf_transformation,[],[f25])).
% 7.82/1.52  
% 7.82/1.52  fof(f59,plain,(
% 7.82/1.52    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 7.82/1.52    inference(flattening,[],[f58])).
% 7.82/1.52  
% 7.82/1.52  fof(f65,plain,(
% 7.82/1.52    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(sK3))) )),
% 7.82/1.52    introduced(choice_axiom,[])).
% 7.82/1.52  
% 7.82/1.52  fof(f64,plain,(
% 7.82/1.52    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2))),
% 7.82/1.52    introduced(choice_axiom,[])).
% 7.82/1.52  
% 7.82/1.52  fof(f66,plain,(
% 7.82/1.52    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2)),
% 7.82/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f59,f65,f64])).
% 7.82/1.52  
% 7.82/1.52  fof(f101,plain,(
% 7.82/1.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 7.82/1.52    inference(cnf_transformation,[],[f66])).
% 7.82/1.52  
% 7.82/1.52  fof(f2,axiom,(
% 7.82/1.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 7.82/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.52  
% 7.82/1.52  fof(f28,plain,(
% 7.82/1.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 7.82/1.52    inference(ennf_transformation,[],[f2])).
% 7.82/1.52  
% 7.82/1.52  fof(f70,plain,(
% 7.82/1.52    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 7.82/1.52    inference(cnf_transformation,[],[f28])).
% 7.82/1.52  
% 7.82/1.52  fof(f4,axiom,(
% 7.82/1.52    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 7.82/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.52  
% 7.82/1.52  fof(f73,plain,(
% 7.82/1.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 7.82/1.52    inference(cnf_transformation,[],[f4])).
% 7.82/1.52  
% 7.82/1.52  fof(f99,plain,(
% 7.82/1.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 7.82/1.52    inference(cnf_transformation,[],[f66])).
% 7.82/1.52  
% 7.82/1.52  fof(f16,axiom,(
% 7.82/1.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 7.82/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.52  
% 7.82/1.52  fof(f49,plain,(
% 7.82/1.52    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.82/1.52    inference(ennf_transformation,[],[f16])).
% 7.82/1.52  
% 7.82/1.52  fof(f88,plain,(
% 7.82/1.52    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.82/1.52    inference(cnf_transformation,[],[f49])).
% 7.82/1.52  
% 7.82/1.52  fof(f102,plain,(
% 7.82/1.52    k2_relset_1(sK0,sK1,sK2) = sK1),
% 7.82/1.52    inference(cnf_transformation,[],[f66])).
% 7.82/1.52  
% 7.82/1.52  fof(f13,axiom,(
% 7.82/1.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 7.82/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.52  
% 7.82/1.52  fof(f44,plain,(
% 7.82/1.52    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.82/1.52    inference(ennf_transformation,[],[f13])).
% 7.82/1.52  
% 7.82/1.52  fof(f45,plain,(
% 7.82/1.52    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.82/1.52    inference(flattening,[],[f44])).
% 7.82/1.52  
% 7.82/1.52  fof(f83,plain,(
% 7.82/1.52    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.82/1.52    inference(cnf_transformation,[],[f45])).
% 7.82/1.52  
% 7.82/1.52  fof(f104,plain,(
% 7.82/1.52    v2_funct_1(sK2)),
% 7.82/1.52    inference(cnf_transformation,[],[f66])).
% 7.82/1.52  
% 7.82/1.52  fof(f98,plain,(
% 7.82/1.52    v1_funct_1(sK2)),
% 7.82/1.52    inference(cnf_transformation,[],[f66])).
% 7.82/1.52  
% 7.82/1.52  fof(f22,axiom,(
% 7.82/1.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 7.82/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.52  
% 7.82/1.52  fof(f26,plain,(
% 7.82/1.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_1(X0)))),
% 7.82/1.52    inference(pure_predicate_removal,[],[f22])).
% 7.82/1.52  
% 7.82/1.52  fof(f56,plain,(
% 7.82/1.52    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.82/1.52    inference(ennf_transformation,[],[f26])).
% 7.82/1.52  
% 7.82/1.52  fof(f57,plain,(
% 7.82/1.52    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.82/1.52    inference(flattening,[],[f56])).
% 7.82/1.52  
% 7.82/1.52  fof(f97,plain,(
% 7.82/1.52    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.82/1.52    inference(cnf_transformation,[],[f57])).
% 7.82/1.52  
% 7.82/1.52  fof(f9,axiom,(
% 7.82/1.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 7.82/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.52  
% 7.82/1.52  fof(f36,plain,(
% 7.82/1.52    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.82/1.52    inference(ennf_transformation,[],[f9])).
% 7.82/1.52  
% 7.82/1.52  fof(f37,plain,(
% 7.82/1.52    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.82/1.52    inference(flattening,[],[f36])).
% 7.82/1.52  
% 7.82/1.52  fof(f79,plain,(
% 7.82/1.52    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.82/1.52    inference(cnf_transformation,[],[f37])).
% 7.82/1.52  
% 7.82/1.52  fof(f78,plain,(
% 7.82/1.52    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.82/1.52    inference(cnf_transformation,[],[f37])).
% 7.82/1.52  
% 7.82/1.52  fof(f84,plain,(
% 7.82/1.52    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.82/1.52    inference(cnf_transformation,[],[f45])).
% 7.82/1.52  
% 7.82/1.52  fof(f6,axiom,(
% 7.82/1.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2))))),
% 7.82/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.52  
% 7.82/1.52  fof(f31,plain,(
% 7.82/1.52    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.82/1.52    inference(ennf_transformation,[],[f6])).
% 7.82/1.52  
% 7.82/1.52  fof(f75,plain,(
% 7.82/1.52    ( ! [X2,X0,X1] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.82/1.52    inference(cnf_transformation,[],[f31])).
% 7.82/1.52  
% 7.82/1.52  fof(f14,axiom,(
% 7.82/1.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 7.82/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.52  
% 7.82/1.52  fof(f46,plain,(
% 7.82/1.52    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.82/1.52    inference(ennf_transformation,[],[f14])).
% 7.82/1.52  
% 7.82/1.52  fof(f47,plain,(
% 7.82/1.52    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.82/1.52    inference(flattening,[],[f46])).
% 7.82/1.52  
% 7.82/1.52  fof(f86,plain,(
% 7.82/1.52    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.82/1.52    inference(cnf_transformation,[],[f47])).
% 7.82/1.52  
% 7.82/1.52  fof(f21,axiom,(
% 7.82/1.52    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 7.82/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.52  
% 7.82/1.52  fof(f95,plain,(
% 7.82/1.52    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 7.82/1.52    inference(cnf_transformation,[],[f21])).
% 7.82/1.52  
% 7.82/1.52  fof(f110,plain,(
% 7.82/1.52    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.82/1.52    inference(definition_unfolding,[],[f86,f95])).
% 7.82/1.52  
% 7.82/1.52  fof(f15,axiom,(
% 7.82/1.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.82/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.52  
% 7.82/1.52  fof(f27,plain,(
% 7.82/1.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 7.82/1.52    inference(pure_predicate_removal,[],[f15])).
% 7.82/1.52  
% 7.82/1.52  fof(f48,plain,(
% 7.82/1.52    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.82/1.52    inference(ennf_transformation,[],[f27])).
% 7.82/1.52  
% 7.82/1.52  fof(f87,plain,(
% 7.82/1.52    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.82/1.52    inference(cnf_transformation,[],[f48])).
% 7.82/1.52  
% 7.82/1.52  fof(f3,axiom,(
% 7.82/1.52    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 7.82/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.52  
% 7.82/1.52  fof(f29,plain,(
% 7.82/1.52    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.82/1.52    inference(ennf_transformation,[],[f3])).
% 7.82/1.52  
% 7.82/1.52  fof(f62,plain,(
% 7.82/1.52    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.82/1.52    inference(nnf_transformation,[],[f29])).
% 7.82/1.52  
% 7.82/1.52  fof(f71,plain,(
% 7.82/1.52    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.82/1.52    inference(cnf_transformation,[],[f62])).
% 7.82/1.52  
% 7.82/1.52  fof(f7,axiom,(
% 7.82/1.52    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 7.82/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.52  
% 7.82/1.52  fof(f32,plain,(
% 7.82/1.52    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.82/1.52    inference(ennf_transformation,[],[f7])).
% 7.82/1.52  
% 7.82/1.52  fof(f33,plain,(
% 7.82/1.52    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 7.82/1.52    inference(flattening,[],[f32])).
% 7.82/1.52  
% 7.82/1.52  fof(f76,plain,(
% 7.82/1.52    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 7.82/1.52    inference(cnf_transformation,[],[f33])).
% 7.82/1.52  
% 7.82/1.52  fof(f108,plain,(
% 7.82/1.52    ( ! [X0,X1] : (k5_relat_1(k6_partfun1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 7.82/1.52    inference(definition_unfolding,[],[f76,f95])).
% 7.82/1.52  
% 7.82/1.52  fof(f20,axiom,(
% 7.82/1.52    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 7.82/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.52  
% 7.82/1.52  fof(f54,plain,(
% 7.82/1.52    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 7.82/1.52    inference(ennf_transformation,[],[f20])).
% 7.82/1.52  
% 7.82/1.52  fof(f55,plain,(
% 7.82/1.52    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 7.82/1.52    inference(flattening,[],[f54])).
% 7.82/1.52  
% 7.82/1.52  fof(f94,plain,(
% 7.82/1.52    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 7.82/1.52    inference(cnf_transformation,[],[f55])).
% 7.82/1.52  
% 7.82/1.52  fof(f100,plain,(
% 7.82/1.52    v1_funct_1(sK3)),
% 7.82/1.52    inference(cnf_transformation,[],[f66])).
% 7.82/1.52  
% 7.82/1.52  fof(f17,axiom,(
% 7.82/1.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 7.82/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.52  
% 7.82/1.52  fof(f50,plain,(
% 7.82/1.52    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 7.82/1.52    inference(ennf_transformation,[],[f17])).
% 7.82/1.52  
% 7.82/1.52  fof(f51,plain,(
% 7.82/1.52    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.82/1.52    inference(flattening,[],[f50])).
% 7.82/1.52  
% 7.82/1.52  fof(f63,plain,(
% 7.82/1.52    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.82/1.52    inference(nnf_transformation,[],[f51])).
% 7.82/1.52  
% 7.82/1.52  fof(f89,plain,(
% 7.82/1.52    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.82/1.52    inference(cnf_transformation,[],[f63])).
% 7.82/1.52  
% 7.82/1.52  fof(f103,plain,(
% 7.82/1.52    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 7.82/1.52    inference(cnf_transformation,[],[f66])).
% 7.82/1.52  
% 7.82/1.52  fof(f18,axiom,(
% 7.82/1.52    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 7.82/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.52  
% 7.82/1.52  fof(f91,plain,(
% 7.82/1.52    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 7.82/1.52    inference(cnf_transformation,[],[f18])).
% 7.82/1.52  
% 7.82/1.52  fof(f112,plain,(
% 7.82/1.52    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 7.82/1.52    inference(definition_unfolding,[],[f91,f95])).
% 7.82/1.52  
% 7.82/1.52  fof(f19,axiom,(
% 7.82/1.52    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 7.82/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.52  
% 7.82/1.52  fof(f52,plain,(
% 7.82/1.52    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 7.82/1.52    inference(ennf_transformation,[],[f19])).
% 7.82/1.52  
% 7.82/1.52  fof(f53,plain,(
% 7.82/1.52    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 7.82/1.52    inference(flattening,[],[f52])).
% 7.82/1.52  
% 7.82/1.52  fof(f93,plain,(
% 7.82/1.52    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 7.82/1.52    inference(cnf_transformation,[],[f53])).
% 7.82/1.52  
% 7.82/1.52  fof(f8,axiom,(
% 7.82/1.52    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 7.82/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.52  
% 7.82/1.52  fof(f34,plain,(
% 7.82/1.52    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.82/1.52    inference(ennf_transformation,[],[f8])).
% 7.82/1.52  
% 7.82/1.52  fof(f35,plain,(
% 7.82/1.52    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 7.82/1.52    inference(flattening,[],[f34])).
% 7.82/1.52  
% 7.82/1.52  fof(f77,plain,(
% 7.82/1.52    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 7.82/1.52    inference(cnf_transformation,[],[f35])).
% 7.82/1.52  
% 7.82/1.52  fof(f109,plain,(
% 7.82/1.52    ( ! [X0,X1] : (k5_relat_1(X1,k6_partfun1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 7.82/1.52    inference(definition_unfolding,[],[f77,f95])).
% 7.82/1.52  
% 7.82/1.52  fof(f107,plain,(
% 7.82/1.52    k2_funct_1(sK2) != sK3),
% 7.82/1.52    inference(cnf_transformation,[],[f66])).
% 7.82/1.52  
% 7.82/1.52  cnf(c_36,negated_conjecture,
% 7.82/1.52      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 7.82/1.52      inference(cnf_transformation,[],[f101]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_1269,plain,
% 7.82/1.52      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 7.82/1.52      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_3,plain,
% 7.82/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.82/1.52      | ~ v1_relat_1(X1)
% 7.82/1.52      | v1_relat_1(X0) ),
% 7.82/1.52      inference(cnf_transformation,[],[f70]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_1284,plain,
% 7.82/1.52      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.82/1.52      | v1_relat_1(X1) != iProver_top
% 7.82/1.52      | v1_relat_1(X0) = iProver_top ),
% 7.82/1.52      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_3066,plain,
% 7.82/1.52      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 7.82/1.52      | v1_relat_1(sK3) = iProver_top ),
% 7.82/1.52      inference(superposition,[status(thm)],[c_1269,c_1284]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_43,plain,
% 7.82/1.52      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 7.82/1.52      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_1519,plain,
% 7.82/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.82/1.52      | v1_relat_1(X0)
% 7.82/1.52      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 7.82/1.52      inference(instantiation,[status(thm)],[c_3]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_1932,plain,
% 7.82/1.52      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 7.82/1.52      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
% 7.82/1.52      | v1_relat_1(sK3) ),
% 7.82/1.52      inference(instantiation,[status(thm)],[c_1519]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_1933,plain,
% 7.82/1.52      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.82/1.52      | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 7.82/1.52      | v1_relat_1(sK3) = iProver_top ),
% 7.82/1.52      inference(predicate_to_equality,[status(thm)],[c_1932]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_6,plain,
% 7.82/1.52      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 7.82/1.52      inference(cnf_transformation,[],[f73]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_2041,plain,
% 7.82/1.52      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
% 7.82/1.52      inference(instantiation,[status(thm)],[c_6]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_2042,plain,
% 7.82/1.52      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
% 7.82/1.52      inference(predicate_to_equality,[status(thm)],[c_2041]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_3331,plain,
% 7.82/1.52      ( v1_relat_1(sK3) = iProver_top ),
% 7.82/1.52      inference(global_propositional_subsumption,
% 7.82/1.52                [status(thm)],
% 7.82/1.52                [c_3066,c_43,c_1933,c_2042]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_38,negated_conjecture,
% 7.82/1.52      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 7.82/1.52      inference(cnf_transformation,[],[f99]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_1267,plain,
% 7.82/1.52      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.82/1.52      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_3067,plain,
% 7.82/1.52      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 7.82/1.52      | v1_relat_1(sK2) = iProver_top ),
% 7.82/1.52      inference(superposition,[status(thm)],[c_1267,c_1284]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_41,plain,
% 7.82/1.52      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.82/1.52      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_1935,plain,
% 7.82/1.52      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.82/1.52      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
% 7.82/1.52      | v1_relat_1(sK2) ),
% 7.82/1.52      inference(instantiation,[status(thm)],[c_1519]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_1936,plain,
% 7.82/1.52      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.82/1.52      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 7.82/1.52      | v1_relat_1(sK2) = iProver_top ),
% 7.82/1.52      inference(predicate_to_equality,[status(thm)],[c_1935]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_2044,plain,
% 7.82/1.52      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 7.82/1.52      inference(instantiation,[status(thm)],[c_6]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_2045,plain,
% 7.82/1.52      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 7.82/1.52      inference(predicate_to_equality,[status(thm)],[c_2044]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_3550,plain,
% 7.82/1.52      ( v1_relat_1(sK2) = iProver_top ),
% 7.82/1.52      inference(global_propositional_subsumption,
% 7.82/1.52                [status(thm)],
% 7.82/1.52                [c_3067,c_41,c_1936,c_2045]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_21,plain,
% 7.82/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.82/1.52      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 7.82/1.52      inference(cnf_transformation,[],[f88]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_1275,plain,
% 7.82/1.52      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 7.82/1.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.82/1.52      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_2077,plain,
% 7.82/1.52      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 7.82/1.52      inference(superposition,[status(thm)],[c_1267,c_1275]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_35,negated_conjecture,
% 7.82/1.52      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 7.82/1.52      inference(cnf_transformation,[],[f102]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_2079,plain,
% 7.82/1.52      ( k2_relat_1(sK2) = sK1 ),
% 7.82/1.52      inference(light_normalisation,[status(thm)],[c_2077,c_35]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_17,plain,
% 7.82/1.52      ( ~ v2_funct_1(X0)
% 7.82/1.52      | ~ v1_funct_1(X0)
% 7.82/1.52      | ~ v1_relat_1(X0)
% 7.82/1.52      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 7.82/1.52      inference(cnf_transformation,[],[f83]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_33,negated_conjecture,
% 7.82/1.52      ( v2_funct_1(sK2) ),
% 7.82/1.52      inference(cnf_transformation,[],[f104]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_484,plain,
% 7.82/1.52      ( ~ v1_funct_1(X0)
% 7.82/1.52      | ~ v1_relat_1(X0)
% 7.82/1.52      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 7.82/1.52      | sK2 != X0 ),
% 7.82/1.52      inference(resolution_lifted,[status(thm)],[c_17,c_33]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_485,plain,
% 7.82/1.52      ( ~ v1_funct_1(sK2)
% 7.82/1.52      | ~ v1_relat_1(sK2)
% 7.82/1.52      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 7.82/1.52      inference(unflattening,[status(thm)],[c_484]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_39,negated_conjecture,
% 7.82/1.52      ( v1_funct_1(sK2) ),
% 7.82/1.52      inference(cnf_transformation,[],[f98]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_487,plain,
% 7.82/1.52      ( ~ v1_relat_1(sK2)
% 7.82/1.52      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 7.82/1.52      inference(global_propositional_subsumption,
% 7.82/1.52                [status(thm)],
% 7.82/1.52                [c_485,c_39]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_1260,plain,
% 7.82/1.52      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 7.82/1.52      | v1_relat_1(sK2) != iProver_top ),
% 7.82/1.52      inference(predicate_to_equality,[status(thm)],[c_487]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_2088,plain,
% 7.82/1.52      ( k1_relat_1(k2_funct_1(sK2)) = sK1
% 7.82/1.52      | v1_relat_1(sK2) != iProver_top ),
% 7.82/1.52      inference(demodulation,[status(thm)],[c_2079,c_1260]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_2219,plain,
% 7.82/1.52      ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
% 7.82/1.52      inference(global_propositional_subsumption,
% 7.82/1.52                [status(thm)],
% 7.82/1.52                [c_2088,c_41,c_1936,c_2045]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_28,plain,
% 7.82/1.52      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 7.82/1.52      | ~ v1_funct_1(X0)
% 7.82/1.52      | ~ v1_relat_1(X0) ),
% 7.82/1.52      inference(cnf_transformation,[],[f97]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_1270,plain,
% 7.82/1.52      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 7.82/1.52      | v1_funct_1(X0) != iProver_top
% 7.82/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.82/1.52      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_2809,plain,
% 7.82/1.52      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2))))) = iProver_top
% 7.82/1.52      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 7.82/1.52      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 7.82/1.52      inference(superposition,[status(thm)],[c_2219,c_1270]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_40,plain,
% 7.82/1.52      ( v1_funct_1(sK2) = iProver_top ),
% 7.82/1.52      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_11,plain,
% 7.82/1.52      ( ~ v1_funct_1(X0)
% 7.82/1.52      | v1_funct_1(k2_funct_1(X0))
% 7.82/1.52      | ~ v1_relat_1(X0) ),
% 7.82/1.52      inference(cnf_transformation,[],[f79]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_1508,plain,
% 7.82/1.52      ( v1_funct_1(k2_funct_1(sK2))
% 7.82/1.52      | ~ v1_funct_1(sK2)
% 7.82/1.52      | ~ v1_relat_1(sK2) ),
% 7.82/1.52      inference(instantiation,[status(thm)],[c_11]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_1509,plain,
% 7.82/1.52      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 7.82/1.52      | v1_funct_1(sK2) != iProver_top
% 7.82/1.52      | v1_relat_1(sK2) != iProver_top ),
% 7.82/1.52      inference(predicate_to_equality,[status(thm)],[c_1508]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_12,plain,
% 7.82/1.52      ( ~ v1_funct_1(X0)
% 7.82/1.52      | ~ v1_relat_1(X0)
% 7.82/1.52      | v1_relat_1(k2_funct_1(X0)) ),
% 7.82/1.52      inference(cnf_transformation,[],[f78]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_1514,plain,
% 7.82/1.52      ( ~ v1_funct_1(sK2)
% 7.82/1.52      | v1_relat_1(k2_funct_1(sK2))
% 7.82/1.52      | ~ v1_relat_1(sK2) ),
% 7.82/1.52      inference(instantiation,[status(thm)],[c_12]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_1515,plain,
% 7.82/1.52      ( v1_funct_1(sK2) != iProver_top
% 7.82/1.52      | v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 7.82/1.52      | v1_relat_1(sK2) != iProver_top ),
% 7.82/1.52      inference(predicate_to_equality,[status(thm)],[c_1514]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_7464,plain,
% 7.82/1.52      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2))))) = iProver_top ),
% 7.82/1.52      inference(global_propositional_subsumption,
% 7.82/1.52                [status(thm)],
% 7.82/1.52                [c_2809,c_40,c_41,c_1509,c_1515,c_1936,c_2045]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_16,plain,
% 7.82/1.52      ( ~ v2_funct_1(X0)
% 7.82/1.52      | ~ v1_funct_1(X0)
% 7.82/1.52      | ~ v1_relat_1(X0)
% 7.82/1.52      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 7.82/1.52      inference(cnf_transformation,[],[f84]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_498,plain,
% 7.82/1.52      ( ~ v1_funct_1(X0)
% 7.82/1.52      | ~ v1_relat_1(X0)
% 7.82/1.52      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 7.82/1.52      | sK2 != X0 ),
% 7.82/1.52      inference(resolution_lifted,[status(thm)],[c_16,c_33]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_499,plain,
% 7.82/1.52      ( ~ v1_funct_1(sK2)
% 7.82/1.52      | ~ v1_relat_1(sK2)
% 7.82/1.52      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 7.82/1.52      inference(unflattening,[status(thm)],[c_498]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_501,plain,
% 7.82/1.52      ( ~ v1_relat_1(sK2)
% 7.82/1.52      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 7.82/1.52      inference(global_propositional_subsumption,
% 7.82/1.52                [status(thm)],
% 7.82/1.52                [c_499,c_39]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_1259,plain,
% 7.82/1.52      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 7.82/1.52      | v1_relat_1(sK2) != iProver_top ),
% 7.82/1.52      inference(predicate_to_equality,[status(thm)],[c_501]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_3558,plain,
% 7.82/1.52      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 7.82/1.52      inference(superposition,[status(thm)],[c_3550,c_1259]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_7468,plain,
% 7.82/1.52      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top ),
% 7.82/1.52      inference(light_normalisation,[status(thm)],[c_7464,c_3558]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_7471,plain,
% 7.82/1.52      ( v1_relat_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))) != iProver_top
% 7.82/1.52      | v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
% 7.82/1.52      inference(superposition,[status(thm)],[c_7468,c_1284]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_8768,plain,
% 7.82/1.52      ( v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
% 7.82/1.52      inference(global_propositional_subsumption,
% 7.82/1.52                [status(thm)],
% 7.82/1.52                [c_7471,c_40,c_41,c_1515,c_1936,c_2045]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_8,plain,
% 7.82/1.52      ( ~ v1_relat_1(X0)
% 7.82/1.52      | ~ v1_relat_1(X1)
% 7.82/1.52      | ~ v1_relat_1(X2)
% 7.82/1.52      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ),
% 7.82/1.52      inference(cnf_transformation,[],[f75]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_1281,plain,
% 7.82/1.52      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
% 7.82/1.52      | v1_relat_1(X0) != iProver_top
% 7.82/1.52      | v1_relat_1(X1) != iProver_top
% 7.82/1.52      | v1_relat_1(X2) != iProver_top ),
% 7.82/1.52      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_8775,plain,
% 7.82/1.52      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1)
% 7.82/1.52      | v1_relat_1(X0) != iProver_top
% 7.82/1.52      | v1_relat_1(X1) != iProver_top ),
% 7.82/1.52      inference(superposition,[status(thm)],[c_8768,c_1281]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_26777,plain,
% 7.82/1.52      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),X0)
% 7.82/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.82/1.52      inference(superposition,[status(thm)],[c_3550,c_8775]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_18,plain,
% 7.82/1.52      ( ~ v2_funct_1(X0)
% 7.82/1.52      | ~ v1_funct_1(X0)
% 7.82/1.52      | ~ v1_relat_1(X0)
% 7.82/1.52      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
% 7.82/1.52      inference(cnf_transformation,[],[f110]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_470,plain,
% 7.82/1.52      ( ~ v1_funct_1(X0)
% 7.82/1.52      | ~ v1_relat_1(X0)
% 7.82/1.52      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
% 7.82/1.52      | sK2 != X0 ),
% 7.82/1.52      inference(resolution_lifted,[status(thm)],[c_18,c_33]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_471,plain,
% 7.82/1.52      ( ~ v1_funct_1(sK2)
% 7.82/1.52      | ~ v1_relat_1(sK2)
% 7.82/1.52      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 7.82/1.52      inference(unflattening,[status(thm)],[c_470]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_473,plain,
% 7.82/1.52      ( ~ v1_relat_1(sK2)
% 7.82/1.52      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 7.82/1.52      inference(global_propositional_subsumption,
% 7.82/1.52                [status(thm)],
% 7.82/1.52                [c_471,c_39]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_1261,plain,
% 7.82/1.52      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
% 7.82/1.52      | v1_relat_1(sK2) != iProver_top ),
% 7.82/1.52      inference(predicate_to_equality,[status(thm)],[c_473]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_2087,plain,
% 7.82/1.52      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 7.82/1.52      | v1_relat_1(sK2) != iProver_top ),
% 7.82/1.52      inference(demodulation,[status(thm)],[c_2079,c_1261]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_2447,plain,
% 7.82/1.52      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
% 7.82/1.52      inference(global_propositional_subsumption,
% 7.82/1.52                [status(thm)],
% 7.82/1.52                [c_2087,c_41,c_1936,c_2045]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_26823,plain,
% 7.82/1.52      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k6_partfun1(sK1),X0)
% 7.82/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.82/1.52      inference(light_normalisation,[status(thm)],[c_26777,c_2447]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_27850,plain,
% 7.82/1.52      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
% 7.82/1.52      inference(superposition,[status(thm)],[c_3331,c_26823]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_20,plain,
% 7.82/1.52      ( v4_relat_1(X0,X1)
% 7.82/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.82/1.52      inference(cnf_transformation,[],[f87]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_5,plain,
% 7.82/1.52      ( ~ v4_relat_1(X0,X1)
% 7.82/1.52      | r1_tarski(k1_relat_1(X0),X1)
% 7.82/1.52      | ~ v1_relat_1(X0) ),
% 7.82/1.52      inference(cnf_transformation,[],[f71]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_397,plain,
% 7.82/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.82/1.52      | r1_tarski(k1_relat_1(X0),X1)
% 7.82/1.52      | ~ v1_relat_1(X0) ),
% 7.82/1.52      inference(resolution,[status(thm)],[c_20,c_5]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_1265,plain,
% 7.82/1.52      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.82/1.52      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 7.82/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.82/1.52      inference(predicate_to_equality,[status(thm)],[c_397]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_2000,plain,
% 7.82/1.52      ( r1_tarski(k1_relat_1(sK3),sK1) = iProver_top
% 7.82/1.52      | v1_relat_1(sK3) != iProver_top ),
% 7.82/1.52      inference(superposition,[status(thm)],[c_1269,c_1265]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_2311,plain,
% 7.82/1.52      ( r1_tarski(k1_relat_1(sK3),sK1) = iProver_top ),
% 7.82/1.52      inference(global_propositional_subsumption,
% 7.82/1.52                [status(thm)],
% 7.82/1.52                [c_2000,c_43,c_1933,c_2042]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_9,plain,
% 7.82/1.52      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 7.82/1.52      | ~ v1_relat_1(X0)
% 7.82/1.52      | k5_relat_1(k6_partfun1(X1),X0) = X0 ),
% 7.82/1.52      inference(cnf_transformation,[],[f108]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_1280,plain,
% 7.82/1.52      ( k5_relat_1(k6_partfun1(X0),X1) = X1
% 7.82/1.52      | r1_tarski(k1_relat_1(X1),X0) != iProver_top
% 7.82/1.52      | v1_relat_1(X1) != iProver_top ),
% 7.82/1.52      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_3294,plain,
% 7.82/1.52      ( k5_relat_1(k6_partfun1(sK1),sK3) = sK3
% 7.82/1.52      | v1_relat_1(sK3) != iProver_top ),
% 7.82/1.52      inference(superposition,[status(thm)],[c_2311,c_1280]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_6232,plain,
% 7.82/1.52      ( k5_relat_1(k6_partfun1(sK1),sK3) = sK3 ),
% 7.82/1.52      inference(global_propositional_subsumption,
% 7.82/1.52                [status(thm)],
% 7.82/1.52                [c_3294,c_43,c_1933,c_2042]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_27,plain,
% 7.82/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.82/1.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.82/1.52      | ~ v1_funct_1(X0)
% 7.82/1.52      | ~ v1_funct_1(X3)
% 7.82/1.52      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 7.82/1.52      inference(cnf_transformation,[],[f94]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_1271,plain,
% 7.82/1.52      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 7.82/1.52      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 7.82/1.52      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.82/1.52      | v1_funct_1(X5) != iProver_top
% 7.82/1.52      | v1_funct_1(X4) != iProver_top ),
% 7.82/1.52      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_4705,plain,
% 7.82/1.52      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 7.82/1.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.82/1.52      | v1_funct_1(X2) != iProver_top
% 7.82/1.52      | v1_funct_1(sK3) != iProver_top ),
% 7.82/1.52      inference(superposition,[status(thm)],[c_1269,c_1271]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_37,negated_conjecture,
% 7.82/1.52      ( v1_funct_1(sK3) ),
% 7.82/1.52      inference(cnf_transformation,[],[f100]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_42,plain,
% 7.82/1.52      ( v1_funct_1(sK3) = iProver_top ),
% 7.82/1.52      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_5165,plain,
% 7.82/1.52      ( v1_funct_1(X2) != iProver_top
% 7.82/1.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.82/1.52      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 7.82/1.52      inference(global_propositional_subsumption,
% 7.82/1.52                [status(thm)],
% 7.82/1.52                [c_4705,c_42]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_5166,plain,
% 7.82/1.52      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 7.82/1.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.82/1.52      | v1_funct_1(X2) != iProver_top ),
% 7.82/1.52      inference(renaming,[status(thm)],[c_5165]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_5178,plain,
% 7.82/1.52      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 7.82/1.52      | v1_funct_1(sK2) != iProver_top ),
% 7.82/1.52      inference(superposition,[status(thm)],[c_1267,c_5166]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_1647,plain,
% 7.82/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.82/1.52      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 7.82/1.52      | ~ v1_funct_1(X0)
% 7.82/1.52      | ~ v1_funct_1(sK3)
% 7.82/1.52      | k1_partfun1(X1,X2,X3,X4,X0,sK3) = k5_relat_1(X0,sK3) ),
% 7.82/1.52      inference(instantiation,[status(thm)],[c_27]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_1886,plain,
% 7.82/1.52      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.82/1.52      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 7.82/1.52      | ~ v1_funct_1(sK3)
% 7.82/1.52      | ~ v1_funct_1(sK2)
% 7.82/1.52      | k1_partfun1(X2,X3,X0,X1,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 7.82/1.52      inference(instantiation,[status(thm)],[c_1647]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_2099,plain,
% 7.82/1.52      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 7.82/1.52      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.82/1.52      | ~ v1_funct_1(sK3)
% 7.82/1.52      | ~ v1_funct_1(sK2)
% 7.82/1.52      | k1_partfun1(X0,X1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 7.82/1.52      inference(instantiation,[status(thm)],[c_1886]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_2454,plain,
% 7.82/1.52      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 7.82/1.52      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.82/1.52      | ~ v1_funct_1(sK3)
% 7.82/1.52      | ~ v1_funct_1(sK2)
% 7.82/1.52      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 7.82/1.52      inference(instantiation,[status(thm)],[c_2099]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_5306,plain,
% 7.82/1.52      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 7.82/1.52      inference(global_propositional_subsumption,
% 7.82/1.52                [status(thm)],
% 7.82/1.52                [c_5178,c_39,c_38,c_37,c_36,c_2454]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_23,plain,
% 7.82/1.52      ( ~ r2_relset_1(X0,X1,X2,X3)
% 7.82/1.52      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.82/1.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.82/1.52      | X3 = X2 ),
% 7.82/1.52      inference(cnf_transformation,[],[f89]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_34,negated_conjecture,
% 7.82/1.52      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 7.82/1.52      inference(cnf_transformation,[],[f103]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_418,plain,
% 7.82/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.82/1.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.82/1.52      | X3 = X0
% 7.82/1.52      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 7.82/1.52      | k6_partfun1(sK0) != X3
% 7.82/1.52      | sK0 != X2
% 7.82/1.52      | sK0 != X1 ),
% 7.82/1.52      inference(resolution_lifted,[status(thm)],[c_23,c_34]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_419,plain,
% 7.82/1.52      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.82/1.52      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.82/1.52      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.82/1.52      inference(unflattening,[status(thm)],[c_418]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_24,plain,
% 7.82/1.52      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 7.82/1.52      inference(cnf_transformation,[],[f112]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_60,plain,
% 7.82/1.52      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 7.82/1.52      inference(instantiation,[status(thm)],[c_24]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_421,plain,
% 7.82/1.52      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.82/1.52      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.82/1.52      inference(global_propositional_subsumption,
% 7.82/1.52                [status(thm)],
% 7.82/1.52                [c_419,c_60]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_1264,plain,
% 7.82/1.52      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.82/1.52      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 7.82/1.52      inference(predicate_to_equality,[status(thm)],[c_421]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_5309,plain,
% 7.82/1.52      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 7.82/1.52      | m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 7.82/1.52      inference(demodulation,[status(thm)],[c_5306,c_1264]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_25,plain,
% 7.82/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.82/1.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.82/1.52      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.82/1.52      | ~ v1_funct_1(X0)
% 7.82/1.52      | ~ v1_funct_1(X3) ),
% 7.82/1.52      inference(cnf_transformation,[],[f93]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_1273,plain,
% 7.82/1.52      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.82/1.52      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 7.82/1.52      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 7.82/1.52      | v1_funct_1(X0) != iProver_top
% 7.82/1.52      | v1_funct_1(X3) != iProver_top ),
% 7.82/1.52      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_5311,plain,
% 7.82/1.52      ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 7.82/1.52      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.82/1.52      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.82/1.52      | v1_funct_1(sK3) != iProver_top
% 7.82/1.52      | v1_funct_1(sK2) != iProver_top ),
% 7.82/1.52      inference(superposition,[status(thm)],[c_5306,c_1273]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_7874,plain,
% 7.82/1.52      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 7.82/1.52      inference(global_propositional_subsumption,
% 7.82/1.52                [status(thm)],
% 7.82/1.52                [c_5309,c_40,c_41,c_42,c_43,c_5311]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_2001,plain,
% 7.82/1.52      ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top
% 7.82/1.52      | v1_relat_1(sK2) != iProver_top ),
% 7.82/1.52      inference(superposition,[status(thm)],[c_1267,c_1265]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_2317,plain,
% 7.82/1.52      ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
% 7.82/1.52      inference(global_propositional_subsumption,
% 7.82/1.52                [status(thm)],
% 7.82/1.52                [c_2001,c_41,c_1936,c_2045]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_10,plain,
% 7.82/1.52      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 7.82/1.52      | ~ v1_relat_1(X0)
% 7.82/1.52      | k5_relat_1(X0,k6_partfun1(X1)) = X0 ),
% 7.82/1.52      inference(cnf_transformation,[],[f109]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_1279,plain,
% 7.82/1.52      ( k5_relat_1(X0,k6_partfun1(X1)) = X0
% 7.82/1.52      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 7.82/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.82/1.52      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_4280,plain,
% 7.82/1.52      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0)) = k2_funct_1(sK2)
% 7.82/1.52      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top
% 7.82/1.52      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 7.82/1.52      inference(superposition,[status(thm)],[c_3558,c_1279]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_10723,plain,
% 7.82/1.52      ( r1_tarski(k1_relat_1(sK2),X0) != iProver_top
% 7.82/1.52      | k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0)) = k2_funct_1(sK2) ),
% 7.82/1.52      inference(global_propositional_subsumption,
% 7.82/1.52                [status(thm)],
% 7.82/1.52                [c_4280,c_40,c_41,c_1515,c_1936,c_2045]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_10724,plain,
% 7.82/1.52      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0)) = k2_funct_1(sK2)
% 7.82/1.52      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
% 7.82/1.52      inference(renaming,[status(thm)],[c_10723]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_10732,plain,
% 7.82/1.52      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k2_funct_1(sK2) ),
% 7.82/1.52      inference(superposition,[status(thm)],[c_2317,c_10724]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_27878,plain,
% 7.82/1.52      ( k2_funct_1(sK2) = sK3 ),
% 7.82/1.52      inference(light_normalisation,
% 7.82/1.52                [status(thm)],
% 7.82/1.52                [c_27850,c_6232,c_7874,c_10732]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(c_30,negated_conjecture,
% 7.82/1.52      ( k2_funct_1(sK2) != sK3 ),
% 7.82/1.52      inference(cnf_transformation,[],[f107]) ).
% 7.82/1.52  
% 7.82/1.52  cnf(contradiction,plain,
% 7.82/1.52      ( $false ),
% 7.82/1.52      inference(minisat,[status(thm)],[c_27878,c_30]) ).
% 7.82/1.52  
% 7.82/1.52  
% 7.82/1.52  % SZS output end CNFRefutation for theBenchmark.p
% 7.82/1.52  
% 7.82/1.52  ------                               Statistics
% 7.82/1.52  
% 7.82/1.52  ------ General
% 7.82/1.52  
% 7.82/1.52  abstr_ref_over_cycles:                  0
% 7.82/1.52  abstr_ref_under_cycles:                 0
% 7.82/1.52  gc_basic_clause_elim:                   0
% 7.82/1.52  forced_gc_time:                         0
% 7.82/1.52  parsing_time:                           0.015
% 7.82/1.52  unif_index_cands_time:                  0.
% 7.82/1.52  unif_index_add_time:                    0.
% 7.82/1.52  orderings_time:                         0.
% 7.82/1.52  out_proof_time:                         0.02
% 7.82/1.52  total_time:                             0.955
% 7.82/1.52  num_of_symbols:                         54
% 7.82/1.52  num_of_terms:                           35209
% 7.82/1.52  
% 7.82/1.52  ------ Preprocessing
% 7.82/1.52  
% 7.82/1.52  num_of_splits:                          0
% 7.82/1.52  num_of_split_atoms:                     0
% 7.82/1.52  num_of_reused_defs:                     0
% 7.82/1.52  num_eq_ax_congr_red:                    3
% 7.82/1.52  num_of_sem_filtered_clauses:            1
% 7.82/1.52  num_of_subtypes:                        0
% 7.82/1.52  monotx_restored_types:                  0
% 7.82/1.52  sat_num_of_epr_types:                   0
% 7.82/1.52  sat_num_of_non_cyclic_types:            0
% 7.82/1.52  sat_guarded_non_collapsed_types:        0
% 7.82/1.52  num_pure_diseq_elim:                    0
% 7.82/1.52  simp_replaced_by:                       0
% 7.82/1.52  res_preprocessed:                       172
% 7.82/1.52  prep_upred:                             0
% 7.82/1.52  prep_unflattend:                        14
% 7.82/1.52  smt_new_axioms:                         0
% 7.82/1.52  pred_elim_cands:                        4
% 7.82/1.52  pred_elim:                              3
% 7.82/1.52  pred_elim_cl:                           5
% 7.82/1.52  pred_elim_cycles:                       5
% 7.82/1.52  merged_defs:                            0
% 7.82/1.52  merged_defs_ncl:                        0
% 7.82/1.52  bin_hyper_res:                          0
% 7.82/1.52  prep_cycles:                            4
% 7.82/1.52  pred_elim_time:                         0.006
% 7.82/1.52  splitting_time:                         0.
% 7.82/1.52  sem_filter_time:                        0.
% 7.82/1.52  monotx_time:                            0.
% 7.82/1.52  subtype_inf_time:                       0.
% 7.82/1.52  
% 7.82/1.52  ------ Problem properties
% 7.82/1.52  
% 7.82/1.52  clauses:                                33
% 7.82/1.52  conjectures:                            8
% 7.82/1.52  epr:                                    6
% 7.82/1.52  horn:                                   33
% 7.82/1.52  ground:                                 13
% 7.82/1.52  unary:                                  11
% 7.82/1.52  binary:                                 8
% 7.82/1.52  lits:                                   77
% 7.82/1.52  lits_eq:                                19
% 7.82/1.52  fd_pure:                                0
% 7.82/1.52  fd_pseudo:                              0
% 7.82/1.52  fd_cond:                                0
% 7.82/1.52  fd_pseudo_cond:                         1
% 7.82/1.52  ac_symbols:                             0
% 7.82/1.52  
% 7.82/1.52  ------ Propositional Solver
% 7.82/1.52  
% 7.82/1.52  prop_solver_calls:                      32
% 7.82/1.52  prop_fast_solver_calls:                 1480
% 7.82/1.52  smt_solver_calls:                       0
% 7.82/1.52  smt_fast_solver_calls:                  0
% 7.82/1.52  prop_num_of_clauses:                    14481
% 7.82/1.52  prop_preprocess_simplified:             29855
% 7.82/1.52  prop_fo_subsumed:                       104
% 7.82/1.52  prop_solver_time:                       0.
% 7.82/1.52  smt_solver_time:                        0.
% 7.82/1.52  smt_fast_solver_time:                   0.
% 7.82/1.52  prop_fast_solver_time:                  0.
% 7.82/1.52  prop_unsat_core_time:                   0.002
% 7.82/1.52  
% 7.82/1.52  ------ QBF
% 7.82/1.52  
% 7.82/1.52  qbf_q_res:                              0
% 7.82/1.52  qbf_num_tautologies:                    0
% 7.82/1.52  qbf_prep_cycles:                        0
% 7.82/1.52  
% 7.82/1.52  ------ BMC1
% 7.82/1.52  
% 7.82/1.52  bmc1_current_bound:                     -1
% 7.82/1.52  bmc1_last_solved_bound:                 -1
% 7.82/1.52  bmc1_unsat_core_size:                   -1
% 7.82/1.52  bmc1_unsat_core_parents_size:           -1
% 7.82/1.52  bmc1_merge_next_fun:                    0
% 7.82/1.52  bmc1_unsat_core_clauses_time:           0.
% 7.82/1.52  
% 7.82/1.52  ------ Instantiation
% 7.82/1.52  
% 7.82/1.52  inst_num_of_clauses:                    3747
% 7.82/1.52  inst_num_in_passive:                    2687
% 7.82/1.52  inst_num_in_active:                     932
% 7.82/1.52  inst_num_in_unprocessed:                128
% 7.82/1.52  inst_num_of_loops:                      1100
% 7.82/1.52  inst_num_of_learning_restarts:          0
% 7.82/1.52  inst_num_moves_active_passive:          166
% 7.82/1.52  inst_lit_activity:                      0
% 7.82/1.52  inst_lit_activity_moves:                3
% 7.82/1.52  inst_num_tautologies:                   0
% 7.82/1.52  inst_num_prop_implied:                  0
% 7.82/1.52  inst_num_existing_simplified:           0
% 7.82/1.52  inst_num_eq_res_simplified:             0
% 7.82/1.52  inst_num_child_elim:                    0
% 7.82/1.52  inst_num_of_dismatching_blockings:      280
% 7.82/1.52  inst_num_of_non_proper_insts:           2557
% 7.82/1.52  inst_num_of_duplicates:                 0
% 7.82/1.52  inst_inst_num_from_inst_to_res:         0
% 7.82/1.52  inst_dismatching_checking_time:         0.
% 7.82/1.52  
% 7.82/1.52  ------ Resolution
% 7.82/1.52  
% 7.82/1.52  res_num_of_clauses:                     0
% 7.82/1.52  res_num_in_passive:                     0
% 7.82/1.52  res_num_in_active:                      0
% 7.82/1.52  res_num_of_loops:                       176
% 7.82/1.52  res_forward_subset_subsumed:            31
% 7.82/1.52  res_backward_subset_subsumed:           0
% 7.82/1.52  res_forward_subsumed:                   0
% 7.82/1.52  res_backward_subsumed:                  0
% 7.82/1.52  res_forward_subsumption_resolution:     0
% 7.82/1.52  res_backward_subsumption_resolution:    0
% 7.82/1.52  res_clause_to_clause_subsumption:       1080
% 7.82/1.52  res_orphan_elimination:                 0
% 7.82/1.52  res_tautology_del:                      29
% 7.82/1.52  res_num_eq_res_simplified:              0
% 7.82/1.52  res_num_sel_changes:                    0
% 7.82/1.52  res_moves_from_active_to_pass:          0
% 7.82/1.52  
% 7.82/1.52  ------ Superposition
% 7.82/1.52  
% 7.82/1.52  sup_time_total:                         0.
% 7.82/1.52  sup_time_generating:                    0.
% 7.82/1.52  sup_time_sim_full:                      0.
% 7.82/1.52  sup_time_sim_immed:                     0.
% 7.82/1.52  
% 7.82/1.52  sup_num_of_clauses:                     570
% 7.82/1.52  sup_num_in_active:                      209
% 7.82/1.52  sup_num_in_passive:                     361
% 7.82/1.52  sup_num_of_loops:                       219
% 7.82/1.52  sup_fw_superposition:                   431
% 7.82/1.52  sup_bw_superposition:                   180
% 7.82/1.52  sup_immediate_simplified:               94
% 7.82/1.52  sup_given_eliminated:                   1
% 7.82/1.52  comparisons_done:                       0
% 7.82/1.52  comparisons_avoided:                    0
% 7.82/1.52  
% 7.82/1.52  ------ Simplifications
% 7.82/1.52  
% 7.82/1.52  
% 7.82/1.52  sim_fw_subset_subsumed:                 20
% 7.82/1.52  sim_bw_subset_subsumed:                 8
% 7.82/1.52  sim_fw_subsumed:                        11
% 7.82/1.52  sim_bw_subsumed:                        0
% 7.82/1.52  sim_fw_subsumption_res:                 3
% 7.82/1.52  sim_bw_subsumption_res:                 0
% 7.82/1.52  sim_tautology_del:                      1
% 7.82/1.52  sim_eq_tautology_del:                   15
% 7.82/1.52  sim_eq_res_simp:                        0
% 7.82/1.52  sim_fw_demodulated:                     3
% 7.82/1.52  sim_bw_demodulated:                     13
% 7.82/1.52  sim_light_normalised:                   69
% 7.82/1.52  sim_joinable_taut:                      0
% 7.82/1.52  sim_joinable_simp:                      0
% 7.82/1.52  sim_ac_normalised:                      0
% 7.82/1.52  sim_smt_subsumption:                    0
% 7.82/1.52  
%------------------------------------------------------------------------------
