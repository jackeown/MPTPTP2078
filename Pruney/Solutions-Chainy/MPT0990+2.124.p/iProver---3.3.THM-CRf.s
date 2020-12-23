%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:23 EST 2020

% Result     : Theorem 27.35s
% Output     : CNFRefutation 27.35s
% Verified   : 
% Statistics : Number of formulae       :  227 (1017 expanded)
%              Number of clauses        :  141 ( 365 expanded)
%              Number of leaves         :   21 ( 213 expanded)
%              Depth                    :   26
%              Number of atoms          :  684 (6532 expanded)
%              Number of equality atoms :  278 (2452 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22,conjecture,(
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

fof(f23,negated_conjecture,(
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
    inference(negated_conjecture,[],[f22])).

fof(f24,plain,(
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
    inference(pure_predicate_removal,[],[f23])).

fof(f56,plain,(
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
    inference(ennf_transformation,[],[f24])).

fof(f57,plain,(
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
    inference(flattening,[],[f56])).

fof(f61,plain,(
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

fof(f60,plain,
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

fof(f62,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f57,f61,f60])).

fof(f92,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f62])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f43,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f42])).

fof(f77,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f97,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f62])).

fof(f91,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f62])).

fof(f1,axiom,(
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
    inference(ennf_transformation,[],[f1])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
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
    inference(ennf_transformation,[],[f2])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f20,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f88,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f20])).

fof(f101,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_partfun1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f71,f88])).

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

fof(f73,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f94,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f62])).

fof(f21,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_1(X0) ) ) ),
    inference(pure_predicate_removal,[],[f21])).

fof(f54,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f55,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f54])).

fof(f90,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f95,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f62])).

fof(f76,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f74,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f45,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f44])).

fof(f79,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f103,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f79,f88])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f53,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f52])).

fof(f87,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f93,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f62])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f48])).

fof(f59,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f49])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f96,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f62])).

fof(f18,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f86,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f51,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f50])).

fof(f85,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f102,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_partfun1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f72,f88])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f100,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_786,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_35])).

cnf(c_1314,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_786])).

cnf(c_17,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_799,plain,
    ( v4_relat_1(X0_52,X0_53)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1305,plain,
    ( v4_relat_1(X0_52,X0_53) = iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_799])).

cnf(c_1954,plain,
    ( v4_relat_1(sK2,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1314,c_1305])).

cnf(c_13,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_30,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_503,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_30])).

cnf(c_504,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_503])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_506,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_504,c_36])).

cnf(c_779,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_506])).

cnf(c_1321,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_779])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_808,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(X1_52))
    | ~ v1_relat_1(X1_52)
    | v1_relat_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1364,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0_52))
    | ~ v1_relat_1(X0_52)
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_808])).

cnf(c_1401,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ v1_relat_1(k2_zfmisc_1(X0_53,X1_53))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1364])).

cnf(c_1445,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1401])).

cnf(c_3,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_807,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_53,X1_53)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1458,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_807])).

cnf(c_1665,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1321,c_35,c_779,c_1445,c_1458])).

cnf(c_2,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_8,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_partfun1(X1)) = X0 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_392,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X2)
    | X3 != X1
    | k5_relat_1(X2,k6_partfun1(X3)) = X2
    | k2_relat_1(X2) != k1_relat_1(X0) ),
    inference(resolution_lifted,[status(thm)],[c_2,c_8])).

cnf(c_393,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X2)
    | k5_relat_1(X2,k6_partfun1(X1)) = X2
    | k2_relat_1(X2) != k1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_392])).

cnf(c_783,plain,
    ( ~ v4_relat_1(X0_52,X0_53)
    | ~ v1_relat_1(X0_52)
    | ~ v1_relat_1(X1_52)
    | k2_relat_1(X1_52) != k1_relat_1(X0_52)
    | k5_relat_1(X1_52,k6_partfun1(X0_53)) = X1_52 ),
    inference(subtyping,[status(esa)],[c_393])).

cnf(c_1317,plain,
    ( k2_relat_1(X0_52) != k1_relat_1(X1_52)
    | k5_relat_1(X0_52,k6_partfun1(X0_53)) = X0_52
    | v4_relat_1(X1_52,X0_53) != iProver_top
    | v1_relat_1(X1_52) != iProver_top
    | v1_relat_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_783])).

cnf(c_4387,plain,
    ( k1_relat_1(X0_52) != k1_relat_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0_53)) = k2_funct_1(sK2)
    | v4_relat_1(X0_52,X0_53) != iProver_top
    | v1_relat_1(X0_52) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1665,c_1317])).

cnf(c_37,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_38,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_11,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_800,plain,
    ( ~ v1_funct_1(X0_52)
    | ~ v1_relat_1(X0_52)
    | v1_relat_1(k2_funct_1(X0_52)) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_867,plain,
    ( v1_funct_1(X0_52) != iProver_top
    | v1_relat_1(X0_52) != iProver_top
    | v1_relat_1(k2_funct_1(X0_52)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_800])).

cnf(c_869,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_867])).

cnf(c_1446,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1445])).

cnf(c_1459,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1458])).

cnf(c_8510,plain,
    ( v1_relat_1(X0_52) != iProver_top
    | v4_relat_1(X0_52,X0_53) != iProver_top
    | k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0_53)) = k2_funct_1(sK2)
    | k1_relat_1(X0_52) != k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4387,c_37,c_38,c_869,c_1446,c_1459])).

cnf(c_8511,plain,
    ( k1_relat_1(X0_52) != k1_relat_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0_53)) = k2_funct_1(sK2)
    | v4_relat_1(X0_52,X0_53) != iProver_top
    | v1_relat_1(X0_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_8510])).

cnf(c_8517,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0_53)) = k2_funct_1(sK2)
    | v4_relat_1(sK2,X0_53) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_8511])).

cnf(c_81356,plain,
    ( v4_relat_1(sK2,X0_53) != iProver_top
    | k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0_53)) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8517,c_38,c_1446,c_1459])).

cnf(c_81357,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0_53)) = k2_funct_1(sK2)
    | v4_relat_1(sK2,X0_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_81356])).

cnf(c_81362,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k2_funct_1(sK2) ),
    inference(superposition,[status(thm)],[c_1954,c_81357])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_788,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subtyping,[status(esa)],[c_33])).

cnf(c_1312,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_788])).

cnf(c_1296,plain,
    ( m1_subset_1(X0_52,k1_zfmisc_1(X1_52)) != iProver_top
    | v1_relat_1(X1_52) != iProver_top
    | v1_relat_1(X0_52) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_808])).

cnf(c_1576,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1312,c_1296])).

cnf(c_40,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_1435,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | v1_relat_1(X0_52)
    | ~ v1_relat_1(k2_zfmisc_1(X0_53,X1_53)) ),
    inference(instantiation,[status(thm)],[c_808])).

cnf(c_1529,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1435])).

cnf(c_1530,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1529])).

cnf(c_1567,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_807])).

cnf(c_1568,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1567])).

cnf(c_1668,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1576,c_40,c_1530,c_1568])).

cnf(c_1577,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1314,c_1296])).

cnf(c_1701,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1577,c_38,c_1446,c_1459])).

cnf(c_25,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_793,plain,
    ( m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_52),k2_relat_1(X0_52))))
    | ~ v1_funct_1(X0_52)
    | ~ v1_relat_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1311,plain,
    ( m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_52),k2_relat_1(X0_52)))) = iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_relat_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_793])).

cnf(c_2504,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1665,c_1311])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_798,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | k2_relset_1(X0_53,X1_53,X0_52) = k2_relat_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1306,plain,
    ( k2_relset_1(X0_53,X1_53,X0_52) = k2_relat_1(X0_52)
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_798])).

cnf(c_2049,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1314,c_1306])).

cnf(c_32,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_789,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(subtyping,[status(esa)],[c_32])).

cnf(c_2051,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2049,c_789])).

cnf(c_14,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_489,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_30])).

cnf(c_490,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_489])).

cnf(c_492,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_490,c_36])).

cnf(c_780,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_492])).

cnf(c_1320,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_780])).

cnf(c_1642,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1320,c_35,c_780,c_1445,c_1458])).

cnf(c_2078,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
    inference(demodulation,[status(thm)],[c_2051,c_1642])).

cnf(c_2508,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2504,c_2078])).

cnf(c_10,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_801,plain,
    ( ~ v1_funct_1(X0_52)
    | v1_funct_1(k2_funct_1(X0_52))
    | ~ v1_relat_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_864,plain,
    ( v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(k2_funct_1(X0_52)) = iProver_top
    | v1_relat_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_801])).

cnf(c_866,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_864])).

cnf(c_5605,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2508,c_37,c_38,c_866,c_869,c_1446,c_1459])).

cnf(c_5614,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5605,c_1296])).

cnf(c_6196,plain,
    ( v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5614,c_37,c_38,c_869,c_1446,c_1459])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_803,plain,
    ( ~ v1_relat_1(X0_52)
    | ~ v1_relat_1(X1_52)
    | ~ v1_relat_1(X2_52)
    | k5_relat_1(k5_relat_1(X0_52,X1_52),X2_52) = k5_relat_1(X0_52,k5_relat_1(X1_52,X2_52)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1301,plain,
    ( k5_relat_1(k5_relat_1(X0_52,X1_52),X2_52) = k5_relat_1(X0_52,k5_relat_1(X1_52,X2_52))
    | v1_relat_1(X0_52) != iProver_top
    | v1_relat_1(X1_52) != iProver_top
    | v1_relat_1(X2_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_803])).

cnf(c_6205,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0_52,X1_52)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0_52),X1_52)
    | v1_relat_1(X0_52) != iProver_top
    | v1_relat_1(X1_52) != iProver_top ),
    inference(superposition,[status(thm)],[c_6196,c_1301])).

cnf(c_12538,plain,
    ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),X0_52) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0_52))
    | v1_relat_1(X0_52) != iProver_top ),
    inference(superposition,[status(thm)],[c_1701,c_6205])).

cnf(c_15,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_475,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_30])).

cnf(c_476,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(unflattening,[status(thm)],[c_475])).

cnf(c_478,plain,
    ( ~ v1_relat_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_476,c_36])).

cnf(c_781,plain,
    ( ~ v1_relat_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(subtyping,[status(esa)],[c_478])).

cnf(c_1319,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_781])).

cnf(c_1768,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1319,c_35,c_781,c_1445,c_1458])).

cnf(c_2077,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(demodulation,[status(thm)],[c_2051,c_1768])).

cnf(c_12548,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0_52)) = k5_relat_1(k6_partfun1(sK1),X0_52)
    | v1_relat_1(X0_52) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12538,c_2077])).

cnf(c_12628,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
    inference(superposition,[status(thm)],[c_1668,c_12548])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_794,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(X2_53,X3_53)))
    | ~ v1_funct_1(X0_52)
    | ~ v1_funct_1(X1_52)
    | k1_partfun1(X2_53,X3_53,X0_53,X1_53,X1_52,X0_52) = k5_relat_1(X1_52,X0_52) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1310,plain,
    ( k1_partfun1(X0_53,X1_53,X2_53,X3_53,X0_52,X1_52) = k5_relat_1(X0_52,X1_52)
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(X2_53,X3_53))) != iProver_top
    | v1_funct_1(X1_52) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_794])).

cnf(c_3227,plain,
    ( k1_partfun1(X0_53,X1_53,sK1,sK0,X0_52,sK3) = k5_relat_1(X0_52,sK3)
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1312,c_1310])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_39,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_3574,plain,
    ( v1_funct_1(X0_52) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | k1_partfun1(X0_53,X1_53,sK1,sK0,X0_52,sK3) = k5_relat_1(X0_52,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3227,c_39])).

cnf(c_3575,plain,
    ( k1_partfun1(X0_53,X1_53,sK1,sK0,X0_52,sK3) = k5_relat_1(X0_52,sK3)
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_3574])).

cnf(c_3581,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1314,c_3575])).

cnf(c_20,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_31,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_374,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_31])).

cnf(c_375,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_374])).

cnf(c_23,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_51,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_377,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_375,c_51])).

cnf(c_784,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_377])).

cnf(c_1316,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_784])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_797,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(X2_53,X3_53)))
    | m1_subset_1(k1_partfun1(X2_53,X3_53,X0_53,X1_53,X1_52,X0_52),k1_zfmisc_1(k2_zfmisc_1(X2_53,X1_53)))
    | ~ v1_funct_1(X0_52)
    | ~ v1_funct_1(X1_52) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1376,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_797])).

cnf(c_1819,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1316,c_36,c_35,c_34,c_33,c_784,c_1376])).

cnf(c_3587,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3581,c_1819])).

cnf(c_3797,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3587,c_37])).

cnf(c_12638,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
    inference(light_normalisation,[status(thm)],[c_12628,c_3797])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_partfun1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_802,plain,
    ( ~ v1_relat_1(X0_52)
    | k5_relat_1(k6_partfun1(X0_53),X0_52) = k7_relat_1(X0_52,X0_53) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1302,plain,
    ( k5_relat_1(k6_partfun1(X0_53),X0_52) = k7_relat_1(X0_52,X0_53)
    | v1_relat_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_802])).

cnf(c_1824,plain,
    ( k5_relat_1(k6_partfun1(X0_53),sK3) = k7_relat_1(sK3,X0_53) ),
    inference(superposition,[status(thm)],[c_1668,c_1302])).

cnf(c_1953,plain,
    ( v4_relat_1(sK3,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1312,c_1305])).

cnf(c_6,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_804,plain,
    ( ~ v4_relat_1(X0_52,X0_53)
    | ~ v1_relat_1(X0_52)
    | k7_relat_1(X0_52,X0_53) = X0_52 ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1300,plain,
    ( k7_relat_1(X0_52,X0_53) = X0_52
    | v4_relat_1(X0_52,X0_53) != iProver_top
    | v1_relat_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_804])).

cnf(c_2419,plain,
    ( k7_relat_1(sK3,sK1) = sK3
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1953,c_1300])).

cnf(c_3437,plain,
    ( k7_relat_1(sK3,sK1) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2419,c_40,c_1530,c_1568])).

cnf(c_12639,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = sK3 ),
    inference(demodulation,[status(thm)],[c_12638,c_1824,c_3437])).

cnf(c_81365,plain,
    ( k2_funct_1(sK2) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_81362,c_12639])).

cnf(c_27,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_792,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_81365,c_792])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:26:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 27.35/4.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.35/4.00  
% 27.35/4.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.35/4.00  
% 27.35/4.00  ------  iProver source info
% 27.35/4.00  
% 27.35/4.00  git: date: 2020-06-30 10:37:57 +0100
% 27.35/4.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.35/4.00  git: non_committed_changes: false
% 27.35/4.00  git: last_make_outside_of_git: false
% 27.35/4.00  
% 27.35/4.00  ------ 
% 27.35/4.00  
% 27.35/4.00  ------ Input Options
% 27.35/4.00  
% 27.35/4.00  --out_options                           all
% 27.35/4.00  --tptp_safe_out                         true
% 27.35/4.00  --problem_path                          ""
% 27.35/4.00  --include_path                          ""
% 27.35/4.00  --clausifier                            res/vclausify_rel
% 27.35/4.00  --clausifier_options                    ""
% 27.35/4.00  --stdin                                 false
% 27.35/4.00  --stats_out                             all
% 27.35/4.00  
% 27.35/4.00  ------ General Options
% 27.35/4.00  
% 27.35/4.00  --fof                                   false
% 27.35/4.00  --time_out_real                         305.
% 27.35/4.00  --time_out_virtual                      -1.
% 27.35/4.00  --symbol_type_check                     false
% 27.35/4.00  --clausify_out                          false
% 27.35/4.00  --sig_cnt_out                           false
% 27.35/4.00  --trig_cnt_out                          false
% 27.35/4.00  --trig_cnt_out_tolerance                1.
% 27.35/4.00  --trig_cnt_out_sk_spl                   false
% 27.35/4.00  --abstr_cl_out                          false
% 27.35/4.00  
% 27.35/4.00  ------ Global Options
% 27.35/4.00  
% 27.35/4.00  --schedule                              default
% 27.35/4.00  --add_important_lit                     false
% 27.35/4.00  --prop_solver_per_cl                    1000
% 27.35/4.00  --min_unsat_core                        false
% 27.35/4.00  --soft_assumptions                      false
% 27.35/4.00  --soft_lemma_size                       3
% 27.35/4.00  --prop_impl_unit_size                   0
% 27.35/4.00  --prop_impl_unit                        []
% 27.35/4.00  --share_sel_clauses                     true
% 27.35/4.00  --reset_solvers                         false
% 27.35/4.00  --bc_imp_inh                            [conj_cone]
% 27.35/4.00  --conj_cone_tolerance                   3.
% 27.35/4.00  --extra_neg_conj                        none
% 27.35/4.00  --large_theory_mode                     true
% 27.35/4.00  --prolific_symb_bound                   200
% 27.35/4.00  --lt_threshold                          2000
% 27.35/4.00  --clause_weak_htbl                      true
% 27.35/4.00  --gc_record_bc_elim                     false
% 27.35/4.00  
% 27.35/4.00  ------ Preprocessing Options
% 27.35/4.00  
% 27.35/4.00  --preprocessing_flag                    true
% 27.35/4.00  --time_out_prep_mult                    0.1
% 27.35/4.00  --splitting_mode                        input
% 27.35/4.00  --splitting_grd                         true
% 27.35/4.00  --splitting_cvd                         false
% 27.35/4.00  --splitting_cvd_svl                     false
% 27.35/4.00  --splitting_nvd                         32
% 27.35/4.00  --sub_typing                            true
% 27.35/4.00  --prep_gs_sim                           true
% 27.35/4.00  --prep_unflatten                        true
% 27.35/4.00  --prep_res_sim                          true
% 27.35/4.00  --prep_upred                            true
% 27.35/4.00  --prep_sem_filter                       exhaustive
% 27.35/4.00  --prep_sem_filter_out                   false
% 27.35/4.00  --pred_elim                             true
% 27.35/4.00  --res_sim_input                         true
% 27.35/4.00  --eq_ax_congr_red                       true
% 27.35/4.00  --pure_diseq_elim                       true
% 27.35/4.00  --brand_transform                       false
% 27.35/4.00  --non_eq_to_eq                          false
% 27.35/4.00  --prep_def_merge                        true
% 27.35/4.00  --prep_def_merge_prop_impl              false
% 27.35/4.00  --prep_def_merge_mbd                    true
% 27.35/4.00  --prep_def_merge_tr_red                 false
% 27.35/4.00  --prep_def_merge_tr_cl                  false
% 27.35/4.00  --smt_preprocessing                     true
% 27.35/4.00  --smt_ac_axioms                         fast
% 27.35/4.00  --preprocessed_out                      false
% 27.35/4.00  --preprocessed_stats                    false
% 27.35/4.00  
% 27.35/4.00  ------ Abstraction refinement Options
% 27.35/4.00  
% 27.35/4.00  --abstr_ref                             []
% 27.35/4.00  --abstr_ref_prep                        false
% 27.35/4.00  --abstr_ref_until_sat                   false
% 27.35/4.00  --abstr_ref_sig_restrict                funpre
% 27.35/4.00  --abstr_ref_af_restrict_to_split_sk     false
% 27.35/4.00  --abstr_ref_under                       []
% 27.35/4.00  
% 27.35/4.00  ------ SAT Options
% 27.35/4.00  
% 27.35/4.00  --sat_mode                              false
% 27.35/4.00  --sat_fm_restart_options                ""
% 27.35/4.00  --sat_gr_def                            false
% 27.35/4.00  --sat_epr_types                         true
% 27.35/4.00  --sat_non_cyclic_types                  false
% 27.35/4.00  --sat_finite_models                     false
% 27.35/4.00  --sat_fm_lemmas                         false
% 27.35/4.00  --sat_fm_prep                           false
% 27.35/4.00  --sat_fm_uc_incr                        true
% 27.35/4.00  --sat_out_model                         small
% 27.35/4.00  --sat_out_clauses                       false
% 27.35/4.00  
% 27.35/4.00  ------ QBF Options
% 27.35/4.00  
% 27.35/4.00  --qbf_mode                              false
% 27.35/4.00  --qbf_elim_univ                         false
% 27.35/4.00  --qbf_dom_inst                          none
% 27.35/4.00  --qbf_dom_pre_inst                      false
% 27.35/4.00  --qbf_sk_in                             false
% 27.35/4.00  --qbf_pred_elim                         true
% 27.35/4.00  --qbf_split                             512
% 27.35/4.00  
% 27.35/4.00  ------ BMC1 Options
% 27.35/4.00  
% 27.35/4.00  --bmc1_incremental                      false
% 27.35/4.00  --bmc1_axioms                           reachable_all
% 27.35/4.00  --bmc1_min_bound                        0
% 27.35/4.00  --bmc1_max_bound                        -1
% 27.35/4.00  --bmc1_max_bound_default                -1
% 27.35/4.00  --bmc1_symbol_reachability              true
% 27.35/4.00  --bmc1_property_lemmas                  false
% 27.35/4.00  --bmc1_k_induction                      false
% 27.35/4.00  --bmc1_non_equiv_states                 false
% 27.35/4.00  --bmc1_deadlock                         false
% 27.35/4.00  --bmc1_ucm                              false
% 27.35/4.00  --bmc1_add_unsat_core                   none
% 27.35/4.00  --bmc1_unsat_core_children              false
% 27.35/4.00  --bmc1_unsat_core_extrapolate_axioms    false
% 27.35/4.00  --bmc1_out_stat                         full
% 27.35/4.00  --bmc1_ground_init                      false
% 27.35/4.00  --bmc1_pre_inst_next_state              false
% 27.35/4.00  --bmc1_pre_inst_state                   false
% 27.35/4.00  --bmc1_pre_inst_reach_state             false
% 27.35/4.00  --bmc1_out_unsat_core                   false
% 27.35/4.00  --bmc1_aig_witness_out                  false
% 27.35/4.00  --bmc1_verbose                          false
% 27.35/4.00  --bmc1_dump_clauses_tptp                false
% 27.35/4.00  --bmc1_dump_unsat_core_tptp             false
% 27.35/4.00  --bmc1_dump_file                        -
% 27.35/4.00  --bmc1_ucm_expand_uc_limit              128
% 27.35/4.00  --bmc1_ucm_n_expand_iterations          6
% 27.35/4.00  --bmc1_ucm_extend_mode                  1
% 27.35/4.00  --bmc1_ucm_init_mode                    2
% 27.35/4.00  --bmc1_ucm_cone_mode                    none
% 27.35/4.00  --bmc1_ucm_reduced_relation_type        0
% 27.35/4.00  --bmc1_ucm_relax_model                  4
% 27.35/4.00  --bmc1_ucm_full_tr_after_sat            true
% 27.35/4.00  --bmc1_ucm_expand_neg_assumptions       false
% 27.35/4.00  --bmc1_ucm_layered_model                none
% 27.35/4.00  --bmc1_ucm_max_lemma_size               10
% 27.35/4.00  
% 27.35/4.00  ------ AIG Options
% 27.35/4.00  
% 27.35/4.00  --aig_mode                              false
% 27.35/4.00  
% 27.35/4.00  ------ Instantiation Options
% 27.35/4.00  
% 27.35/4.00  --instantiation_flag                    true
% 27.35/4.00  --inst_sos_flag                         true
% 27.35/4.00  --inst_sos_phase                        true
% 27.35/4.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.35/4.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.35/4.00  --inst_lit_sel_side                     num_symb
% 27.35/4.00  --inst_solver_per_active                1400
% 27.35/4.00  --inst_solver_calls_frac                1.
% 27.35/4.00  --inst_passive_queue_type               priority_queues
% 27.35/4.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.35/4.00  --inst_passive_queues_freq              [25;2]
% 27.35/4.00  --inst_dismatching                      true
% 27.35/4.00  --inst_eager_unprocessed_to_passive     true
% 27.35/4.00  --inst_prop_sim_given                   true
% 27.35/4.00  --inst_prop_sim_new                     false
% 27.35/4.00  --inst_subs_new                         false
% 27.35/4.00  --inst_eq_res_simp                      false
% 27.35/4.00  --inst_subs_given                       false
% 27.35/4.00  --inst_orphan_elimination               true
% 27.35/4.00  --inst_learning_loop_flag               true
% 27.35/4.00  --inst_learning_start                   3000
% 27.35/4.00  --inst_learning_factor                  2
% 27.35/4.00  --inst_start_prop_sim_after_learn       3
% 27.35/4.00  --inst_sel_renew                        solver
% 27.35/4.00  --inst_lit_activity_flag                true
% 27.35/4.00  --inst_restr_to_given                   false
% 27.35/4.00  --inst_activity_threshold               500
% 27.35/4.00  --inst_out_proof                        true
% 27.35/4.00  
% 27.35/4.00  ------ Resolution Options
% 27.35/4.00  
% 27.35/4.00  --resolution_flag                       true
% 27.35/4.00  --res_lit_sel                           adaptive
% 27.35/4.00  --res_lit_sel_side                      none
% 27.35/4.00  --res_ordering                          kbo
% 27.35/4.00  --res_to_prop_solver                    active
% 27.35/4.00  --res_prop_simpl_new                    false
% 27.35/4.00  --res_prop_simpl_given                  true
% 27.35/4.00  --res_passive_queue_type                priority_queues
% 27.35/4.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.35/4.00  --res_passive_queues_freq               [15;5]
% 27.35/4.00  --res_forward_subs                      full
% 27.35/4.00  --res_backward_subs                     full
% 27.35/4.00  --res_forward_subs_resolution           true
% 27.35/4.00  --res_backward_subs_resolution          true
% 27.35/4.00  --res_orphan_elimination                true
% 27.35/4.00  --res_time_limit                        2.
% 27.35/4.00  --res_out_proof                         true
% 27.35/4.00  
% 27.35/4.00  ------ Superposition Options
% 27.35/4.00  
% 27.35/4.00  --superposition_flag                    true
% 27.35/4.00  --sup_passive_queue_type                priority_queues
% 27.35/4.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.35/4.00  --sup_passive_queues_freq               [8;1;4]
% 27.35/4.00  --demod_completeness_check              fast
% 27.35/4.00  --demod_use_ground                      true
% 27.35/4.00  --sup_to_prop_solver                    passive
% 27.35/4.00  --sup_prop_simpl_new                    true
% 27.35/4.00  --sup_prop_simpl_given                  true
% 27.35/4.00  --sup_fun_splitting                     true
% 27.35/4.00  --sup_smt_interval                      50000
% 27.35/4.00  
% 27.35/4.00  ------ Superposition Simplification Setup
% 27.35/4.00  
% 27.35/4.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 27.35/4.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 27.35/4.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 27.35/4.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 27.35/4.00  --sup_full_triv                         [TrivRules;PropSubs]
% 27.35/4.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 27.35/4.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 27.35/4.00  --sup_immed_triv                        [TrivRules]
% 27.35/4.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.35/4.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.35/4.00  --sup_immed_bw_main                     []
% 27.35/4.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 27.35/4.00  --sup_input_triv                        [Unflattening;TrivRules]
% 27.35/4.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.35/4.00  --sup_input_bw                          []
% 27.35/4.00  
% 27.35/4.00  ------ Combination Options
% 27.35/4.00  
% 27.35/4.00  --comb_res_mult                         3
% 27.35/4.00  --comb_sup_mult                         2
% 27.35/4.00  --comb_inst_mult                        10
% 27.35/4.00  
% 27.35/4.00  ------ Debug Options
% 27.35/4.00  
% 27.35/4.00  --dbg_backtrace                         false
% 27.35/4.00  --dbg_dump_prop_clauses                 false
% 27.35/4.00  --dbg_dump_prop_clauses_file            -
% 27.35/4.00  --dbg_out_stat                          false
% 27.35/4.00  ------ Parsing...
% 27.35/4.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.35/4.00  
% 27.35/4.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 27.35/4.00  
% 27.35/4.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.35/4.00  
% 27.35/4.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.35/4.00  ------ Proving...
% 27.35/4.00  ------ Problem Properties 
% 27.35/4.00  
% 27.35/4.00  
% 27.35/4.00  clauses                                 31
% 27.35/4.00  conjectures                             8
% 27.35/4.00  EPR                                     4
% 27.35/4.00  Horn                                    31
% 27.35/4.00  unary                                   10
% 27.35/4.00  binary                                  11
% 27.35/4.00  lits                                    71
% 27.35/4.00  lits eq                                 19
% 27.35/4.00  fd_pure                                 0
% 27.35/4.00  fd_pseudo                               0
% 27.35/4.00  fd_cond                                 0
% 27.35/4.00  fd_pseudo_cond                          0
% 27.35/4.00  AC symbols                              0
% 27.35/4.00  
% 27.35/4.00  ------ Schedule dynamic 5 is on 
% 27.35/4.00  
% 27.35/4.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 27.35/4.00  
% 27.35/4.00  
% 27.35/4.00  ------ 
% 27.35/4.00  Current options:
% 27.35/4.00  ------ 
% 27.35/4.00  
% 27.35/4.00  ------ Input Options
% 27.35/4.00  
% 27.35/4.00  --out_options                           all
% 27.35/4.00  --tptp_safe_out                         true
% 27.35/4.00  --problem_path                          ""
% 27.35/4.00  --include_path                          ""
% 27.35/4.00  --clausifier                            res/vclausify_rel
% 27.35/4.00  --clausifier_options                    ""
% 27.35/4.00  --stdin                                 false
% 27.35/4.00  --stats_out                             all
% 27.35/4.00  
% 27.35/4.00  ------ General Options
% 27.35/4.00  
% 27.35/4.00  --fof                                   false
% 27.35/4.00  --time_out_real                         305.
% 27.35/4.00  --time_out_virtual                      -1.
% 27.35/4.00  --symbol_type_check                     false
% 27.35/4.00  --clausify_out                          false
% 27.35/4.00  --sig_cnt_out                           false
% 27.35/4.00  --trig_cnt_out                          false
% 27.35/4.00  --trig_cnt_out_tolerance                1.
% 27.35/4.00  --trig_cnt_out_sk_spl                   false
% 27.35/4.00  --abstr_cl_out                          false
% 27.35/4.00  
% 27.35/4.00  ------ Global Options
% 27.35/4.00  
% 27.35/4.00  --schedule                              default
% 27.35/4.00  --add_important_lit                     false
% 27.35/4.00  --prop_solver_per_cl                    1000
% 27.35/4.00  --min_unsat_core                        false
% 27.35/4.00  --soft_assumptions                      false
% 27.35/4.00  --soft_lemma_size                       3
% 27.35/4.00  --prop_impl_unit_size                   0
% 27.35/4.00  --prop_impl_unit                        []
% 27.35/4.00  --share_sel_clauses                     true
% 27.35/4.00  --reset_solvers                         false
% 27.35/4.00  --bc_imp_inh                            [conj_cone]
% 27.35/4.00  --conj_cone_tolerance                   3.
% 27.35/4.00  --extra_neg_conj                        none
% 27.35/4.00  --large_theory_mode                     true
% 27.35/4.00  --prolific_symb_bound                   200
% 27.35/4.00  --lt_threshold                          2000
% 27.35/4.00  --clause_weak_htbl                      true
% 27.35/4.00  --gc_record_bc_elim                     false
% 27.35/4.00  
% 27.35/4.00  ------ Preprocessing Options
% 27.35/4.00  
% 27.35/4.00  --preprocessing_flag                    true
% 27.35/4.00  --time_out_prep_mult                    0.1
% 27.35/4.00  --splitting_mode                        input
% 27.35/4.00  --splitting_grd                         true
% 27.35/4.00  --splitting_cvd                         false
% 27.35/4.00  --splitting_cvd_svl                     false
% 27.35/4.00  --splitting_nvd                         32
% 27.35/4.00  --sub_typing                            true
% 27.35/4.00  --prep_gs_sim                           true
% 27.35/4.00  --prep_unflatten                        true
% 27.35/4.00  --prep_res_sim                          true
% 27.35/4.00  --prep_upred                            true
% 27.35/4.00  --prep_sem_filter                       exhaustive
% 27.35/4.00  --prep_sem_filter_out                   false
% 27.35/4.00  --pred_elim                             true
% 27.35/4.00  --res_sim_input                         true
% 27.35/4.00  --eq_ax_congr_red                       true
% 27.35/4.00  --pure_diseq_elim                       true
% 27.35/4.00  --brand_transform                       false
% 27.35/4.00  --non_eq_to_eq                          false
% 27.35/4.00  --prep_def_merge                        true
% 27.35/4.00  --prep_def_merge_prop_impl              false
% 27.35/4.00  --prep_def_merge_mbd                    true
% 27.35/4.00  --prep_def_merge_tr_red                 false
% 27.35/4.00  --prep_def_merge_tr_cl                  false
% 27.35/4.00  --smt_preprocessing                     true
% 27.35/4.00  --smt_ac_axioms                         fast
% 27.35/4.00  --preprocessed_out                      false
% 27.35/4.00  --preprocessed_stats                    false
% 27.35/4.00  
% 27.35/4.00  ------ Abstraction refinement Options
% 27.35/4.00  
% 27.35/4.00  --abstr_ref                             []
% 27.35/4.00  --abstr_ref_prep                        false
% 27.35/4.00  --abstr_ref_until_sat                   false
% 27.35/4.00  --abstr_ref_sig_restrict                funpre
% 27.35/4.00  --abstr_ref_af_restrict_to_split_sk     false
% 27.35/4.00  --abstr_ref_under                       []
% 27.35/4.00  
% 27.35/4.00  ------ SAT Options
% 27.35/4.00  
% 27.35/4.00  --sat_mode                              false
% 27.35/4.00  --sat_fm_restart_options                ""
% 27.35/4.00  --sat_gr_def                            false
% 27.35/4.00  --sat_epr_types                         true
% 27.35/4.00  --sat_non_cyclic_types                  false
% 27.35/4.00  --sat_finite_models                     false
% 27.35/4.00  --sat_fm_lemmas                         false
% 27.35/4.00  --sat_fm_prep                           false
% 27.35/4.00  --sat_fm_uc_incr                        true
% 27.35/4.00  --sat_out_model                         small
% 27.35/4.00  --sat_out_clauses                       false
% 27.35/4.00  
% 27.35/4.00  ------ QBF Options
% 27.35/4.00  
% 27.35/4.00  --qbf_mode                              false
% 27.35/4.00  --qbf_elim_univ                         false
% 27.35/4.00  --qbf_dom_inst                          none
% 27.35/4.00  --qbf_dom_pre_inst                      false
% 27.35/4.00  --qbf_sk_in                             false
% 27.35/4.00  --qbf_pred_elim                         true
% 27.35/4.00  --qbf_split                             512
% 27.35/4.00  
% 27.35/4.00  ------ BMC1 Options
% 27.35/4.00  
% 27.35/4.00  --bmc1_incremental                      false
% 27.35/4.00  --bmc1_axioms                           reachable_all
% 27.35/4.00  --bmc1_min_bound                        0
% 27.35/4.00  --bmc1_max_bound                        -1
% 27.35/4.00  --bmc1_max_bound_default                -1
% 27.35/4.00  --bmc1_symbol_reachability              true
% 27.35/4.00  --bmc1_property_lemmas                  false
% 27.35/4.00  --bmc1_k_induction                      false
% 27.35/4.00  --bmc1_non_equiv_states                 false
% 27.35/4.00  --bmc1_deadlock                         false
% 27.35/4.00  --bmc1_ucm                              false
% 27.35/4.00  --bmc1_add_unsat_core                   none
% 27.35/4.00  --bmc1_unsat_core_children              false
% 27.35/4.00  --bmc1_unsat_core_extrapolate_axioms    false
% 27.35/4.00  --bmc1_out_stat                         full
% 27.35/4.00  --bmc1_ground_init                      false
% 27.35/4.00  --bmc1_pre_inst_next_state              false
% 27.35/4.00  --bmc1_pre_inst_state                   false
% 27.35/4.00  --bmc1_pre_inst_reach_state             false
% 27.35/4.00  --bmc1_out_unsat_core                   false
% 27.35/4.00  --bmc1_aig_witness_out                  false
% 27.35/4.00  --bmc1_verbose                          false
% 27.35/4.00  --bmc1_dump_clauses_tptp                false
% 27.35/4.00  --bmc1_dump_unsat_core_tptp             false
% 27.35/4.00  --bmc1_dump_file                        -
% 27.35/4.00  --bmc1_ucm_expand_uc_limit              128
% 27.35/4.00  --bmc1_ucm_n_expand_iterations          6
% 27.35/4.00  --bmc1_ucm_extend_mode                  1
% 27.35/4.00  --bmc1_ucm_init_mode                    2
% 27.35/4.00  --bmc1_ucm_cone_mode                    none
% 27.35/4.00  --bmc1_ucm_reduced_relation_type        0
% 27.35/4.00  --bmc1_ucm_relax_model                  4
% 27.35/4.00  --bmc1_ucm_full_tr_after_sat            true
% 27.35/4.00  --bmc1_ucm_expand_neg_assumptions       false
% 27.35/4.00  --bmc1_ucm_layered_model                none
% 27.35/4.00  --bmc1_ucm_max_lemma_size               10
% 27.35/4.00  
% 27.35/4.00  ------ AIG Options
% 27.35/4.00  
% 27.35/4.00  --aig_mode                              false
% 27.35/4.00  
% 27.35/4.00  ------ Instantiation Options
% 27.35/4.00  
% 27.35/4.00  --instantiation_flag                    true
% 27.35/4.00  --inst_sos_flag                         true
% 27.35/4.00  --inst_sos_phase                        true
% 27.35/4.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.35/4.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.35/4.00  --inst_lit_sel_side                     none
% 27.35/4.00  --inst_solver_per_active                1400
% 27.35/4.00  --inst_solver_calls_frac                1.
% 27.35/4.00  --inst_passive_queue_type               priority_queues
% 27.35/4.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.35/4.00  --inst_passive_queues_freq              [25;2]
% 27.35/4.00  --inst_dismatching                      true
% 27.35/4.00  --inst_eager_unprocessed_to_passive     true
% 27.35/4.00  --inst_prop_sim_given                   true
% 27.35/4.00  --inst_prop_sim_new                     false
% 27.35/4.00  --inst_subs_new                         false
% 27.35/4.00  --inst_eq_res_simp                      false
% 27.35/4.00  --inst_subs_given                       false
% 27.35/4.00  --inst_orphan_elimination               true
% 27.35/4.00  --inst_learning_loop_flag               true
% 27.35/4.00  --inst_learning_start                   3000
% 27.35/4.00  --inst_learning_factor                  2
% 27.35/4.00  --inst_start_prop_sim_after_learn       3
% 27.35/4.00  --inst_sel_renew                        solver
% 27.35/4.00  --inst_lit_activity_flag                true
% 27.35/4.00  --inst_restr_to_given                   false
% 27.35/4.00  --inst_activity_threshold               500
% 27.35/4.00  --inst_out_proof                        true
% 27.35/4.00  
% 27.35/4.00  ------ Resolution Options
% 27.35/4.00  
% 27.35/4.00  --resolution_flag                       false
% 27.35/4.00  --res_lit_sel                           adaptive
% 27.35/4.00  --res_lit_sel_side                      none
% 27.35/4.00  --res_ordering                          kbo
% 27.35/4.00  --res_to_prop_solver                    active
% 27.35/4.00  --res_prop_simpl_new                    false
% 27.35/4.00  --res_prop_simpl_given                  true
% 27.35/4.00  --res_passive_queue_type                priority_queues
% 27.35/4.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.35/4.00  --res_passive_queues_freq               [15;5]
% 27.35/4.00  --res_forward_subs                      full
% 27.35/4.00  --res_backward_subs                     full
% 27.35/4.00  --res_forward_subs_resolution           true
% 27.35/4.00  --res_backward_subs_resolution          true
% 27.35/4.00  --res_orphan_elimination                true
% 27.35/4.00  --res_time_limit                        2.
% 27.35/4.00  --res_out_proof                         true
% 27.35/4.00  
% 27.35/4.00  ------ Superposition Options
% 27.35/4.00  
% 27.35/4.00  --superposition_flag                    true
% 27.35/4.00  --sup_passive_queue_type                priority_queues
% 27.35/4.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.35/4.00  --sup_passive_queues_freq               [8;1;4]
% 27.35/4.00  --demod_completeness_check              fast
% 27.35/4.00  --demod_use_ground                      true
% 27.35/4.00  --sup_to_prop_solver                    passive
% 27.35/4.00  --sup_prop_simpl_new                    true
% 27.35/4.00  --sup_prop_simpl_given                  true
% 27.35/4.00  --sup_fun_splitting                     true
% 27.35/4.00  --sup_smt_interval                      50000
% 27.35/4.00  
% 27.35/4.00  ------ Superposition Simplification Setup
% 27.35/4.00  
% 27.35/4.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 27.35/4.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 27.35/4.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 27.35/4.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 27.35/4.00  --sup_full_triv                         [TrivRules;PropSubs]
% 27.35/4.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 27.35/4.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 27.35/4.00  --sup_immed_triv                        [TrivRules]
% 27.35/4.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.35/4.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.35/4.00  --sup_immed_bw_main                     []
% 27.35/4.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 27.35/4.00  --sup_input_triv                        [Unflattening;TrivRules]
% 27.35/4.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.35/4.00  --sup_input_bw                          []
% 27.35/4.00  
% 27.35/4.00  ------ Combination Options
% 27.35/4.00  
% 27.35/4.00  --comb_res_mult                         3
% 27.35/4.00  --comb_sup_mult                         2
% 27.35/4.00  --comb_inst_mult                        10
% 27.35/4.00  
% 27.35/4.00  ------ Debug Options
% 27.35/4.00  
% 27.35/4.00  --dbg_backtrace                         false
% 27.35/4.00  --dbg_dump_prop_clauses                 false
% 27.35/4.00  --dbg_dump_prop_clauses_file            -
% 27.35/4.00  --dbg_out_stat                          false
% 27.35/4.00  
% 27.35/4.00  
% 27.35/4.00  
% 27.35/4.00  
% 27.35/4.00  ------ Proving...
% 27.35/4.00  
% 27.35/4.00  
% 27.35/4.00  % SZS status Theorem for theBenchmark.p
% 27.35/4.00  
% 27.35/4.00  % SZS output start CNFRefutation for theBenchmark.p
% 27.35/4.00  
% 27.35/4.00  fof(f22,conjecture,(
% 27.35/4.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 27.35/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.35/4.00  
% 27.35/4.00  fof(f23,negated_conjecture,(
% 27.35/4.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 27.35/4.00    inference(negated_conjecture,[],[f22])).
% 27.35/4.00  
% 27.35/4.00  fof(f24,plain,(
% 27.35/4.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 27.35/4.00    inference(pure_predicate_removal,[],[f23])).
% 27.35/4.00  
% 27.35/4.00  fof(f56,plain,(
% 27.35/4.00    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 27.35/4.00    inference(ennf_transformation,[],[f24])).
% 27.35/4.00  
% 27.35/4.00  fof(f57,plain,(
% 27.35/4.00    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 27.35/4.00    inference(flattening,[],[f56])).
% 27.35/4.00  
% 27.35/4.00  fof(f61,plain,(
% 27.35/4.00    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(sK3))) )),
% 27.35/4.00    introduced(choice_axiom,[])).
% 27.35/4.00  
% 27.35/4.00  fof(f60,plain,(
% 27.35/4.00    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2))),
% 27.35/4.00    introduced(choice_axiom,[])).
% 27.35/4.00  
% 27.35/4.00  fof(f62,plain,(
% 27.35/4.00    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2)),
% 27.35/4.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f57,f61,f60])).
% 27.35/4.00  
% 27.35/4.00  fof(f92,plain,(
% 27.35/4.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 27.35/4.00    inference(cnf_transformation,[],[f62])).
% 27.35/4.00  
% 27.35/4.00  fof(f14,axiom,(
% 27.35/4.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 27.35/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.35/4.00  
% 27.35/4.00  fof(f27,plain,(
% 27.35/4.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 27.35/4.00    inference(pure_predicate_removal,[],[f14])).
% 27.35/4.00  
% 27.35/4.00  fof(f46,plain,(
% 27.35/4.00    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 27.35/4.00    inference(ennf_transformation,[],[f27])).
% 27.35/4.00  
% 27.35/4.00  fof(f80,plain,(
% 27.35/4.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 27.35/4.00    inference(cnf_transformation,[],[f46])).
% 27.35/4.00  
% 27.35/4.00  fof(f12,axiom,(
% 27.35/4.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 27.35/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.35/4.00  
% 27.35/4.00  fof(f42,plain,(
% 27.35/4.00    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 27.35/4.00    inference(ennf_transformation,[],[f12])).
% 27.35/4.00  
% 27.35/4.00  fof(f43,plain,(
% 27.35/4.00    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 27.35/4.00    inference(flattening,[],[f42])).
% 27.35/4.00  
% 27.35/4.00  fof(f77,plain,(
% 27.35/4.00    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 27.35/4.00    inference(cnf_transformation,[],[f43])).
% 27.35/4.00  
% 27.35/4.00  fof(f97,plain,(
% 27.35/4.00    v2_funct_1(sK2)),
% 27.35/4.00    inference(cnf_transformation,[],[f62])).
% 27.35/4.00  
% 27.35/4.00  fof(f91,plain,(
% 27.35/4.00    v1_funct_1(sK2)),
% 27.35/4.00    inference(cnf_transformation,[],[f62])).
% 27.35/4.00  
% 27.35/4.00  fof(f1,axiom,(
% 27.35/4.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 27.35/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.35/4.00  
% 27.35/4.00  fof(f28,plain,(
% 27.35/4.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 27.35/4.00    inference(ennf_transformation,[],[f1])).
% 27.35/4.00  
% 27.35/4.00  fof(f63,plain,(
% 27.35/4.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 27.35/4.00    inference(cnf_transformation,[],[f28])).
% 27.35/4.00  
% 27.35/4.00  fof(f3,axiom,(
% 27.35/4.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 27.35/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.35/4.00  
% 27.35/4.00  fof(f66,plain,(
% 27.35/4.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 27.35/4.00    inference(cnf_transformation,[],[f3])).
% 27.35/4.00  
% 27.35/4.00  fof(f2,axiom,(
% 27.35/4.00    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 27.35/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.35/4.00  
% 27.35/4.00  fof(f29,plain,(
% 27.35/4.00    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 27.35/4.00    inference(ennf_transformation,[],[f2])).
% 27.35/4.00  
% 27.35/4.00  fof(f58,plain,(
% 27.35/4.00    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 27.35/4.00    inference(nnf_transformation,[],[f29])).
% 27.35/4.00  
% 27.35/4.00  fof(f64,plain,(
% 27.35/4.00    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 27.35/4.00    inference(cnf_transformation,[],[f58])).
% 27.35/4.00  
% 27.35/4.00  fof(f8,axiom,(
% 27.35/4.00    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 27.35/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.35/4.00  
% 27.35/4.00  fof(f35,plain,(
% 27.35/4.00    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 27.35/4.00    inference(ennf_transformation,[],[f8])).
% 27.35/4.00  
% 27.35/4.00  fof(f36,plain,(
% 27.35/4.00    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 27.35/4.00    inference(flattening,[],[f35])).
% 27.35/4.00  
% 27.35/4.00  fof(f71,plain,(
% 27.35/4.00    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 27.35/4.00    inference(cnf_transformation,[],[f36])).
% 27.35/4.00  
% 27.35/4.00  fof(f20,axiom,(
% 27.35/4.00    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 27.35/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.35/4.00  
% 27.35/4.00  fof(f88,plain,(
% 27.35/4.00    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 27.35/4.00    inference(cnf_transformation,[],[f20])).
% 27.35/4.00  
% 27.35/4.00  fof(f101,plain,(
% 27.35/4.00    ( ! [X0,X1] : (k5_relat_1(X1,k6_partfun1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 27.35/4.00    inference(definition_unfolding,[],[f71,f88])).
% 27.35/4.00  
% 27.35/4.00  fof(f10,axiom,(
% 27.35/4.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 27.35/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.35/4.00  
% 27.35/4.00  fof(f38,plain,(
% 27.35/4.00    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 27.35/4.00    inference(ennf_transformation,[],[f10])).
% 27.35/4.00  
% 27.35/4.00  fof(f39,plain,(
% 27.35/4.00    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 27.35/4.00    inference(flattening,[],[f38])).
% 27.35/4.00  
% 27.35/4.00  fof(f73,plain,(
% 27.35/4.00    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 27.35/4.00    inference(cnf_transformation,[],[f39])).
% 27.35/4.00  
% 27.35/4.00  fof(f94,plain,(
% 27.35/4.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 27.35/4.00    inference(cnf_transformation,[],[f62])).
% 27.35/4.00  
% 27.35/4.00  fof(f21,axiom,(
% 27.35/4.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 27.35/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.35/4.00  
% 27.35/4.00  fof(f25,plain,(
% 27.35/4.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_1(X0)))),
% 27.35/4.00    inference(pure_predicate_removal,[],[f21])).
% 27.35/4.00  
% 27.35/4.00  fof(f54,plain,(
% 27.35/4.00    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 27.35/4.00    inference(ennf_transformation,[],[f25])).
% 27.35/4.00  
% 27.35/4.00  fof(f55,plain,(
% 27.35/4.00    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 27.35/4.00    inference(flattening,[],[f54])).
% 27.35/4.00  
% 27.35/4.00  fof(f90,plain,(
% 27.35/4.00    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 27.35/4.00    inference(cnf_transformation,[],[f55])).
% 27.35/4.00  
% 27.35/4.00  fof(f15,axiom,(
% 27.35/4.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 27.35/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.35/4.00  
% 27.35/4.00  fof(f47,plain,(
% 27.35/4.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 27.35/4.00    inference(ennf_transformation,[],[f15])).
% 27.35/4.00  
% 27.35/4.00  fof(f81,plain,(
% 27.35/4.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 27.35/4.00    inference(cnf_transformation,[],[f47])).
% 27.35/4.00  
% 27.35/4.00  fof(f95,plain,(
% 27.35/4.00    k2_relset_1(sK0,sK1,sK2) = sK1),
% 27.35/4.00    inference(cnf_transformation,[],[f62])).
% 27.35/4.00  
% 27.35/4.00  fof(f76,plain,(
% 27.35/4.00    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 27.35/4.00    inference(cnf_transformation,[],[f43])).
% 27.35/4.00  
% 27.35/4.00  fof(f74,plain,(
% 27.35/4.00    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 27.35/4.00    inference(cnf_transformation,[],[f39])).
% 27.35/4.00  
% 27.35/4.00  fof(f7,axiom,(
% 27.35/4.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2))))),
% 27.35/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.35/4.00  
% 27.35/4.00  fof(f34,plain,(
% 27.35/4.00    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 27.35/4.00    inference(ennf_transformation,[],[f7])).
% 27.35/4.00  
% 27.35/4.00  fof(f70,plain,(
% 27.35/4.00    ( ! [X2,X0,X1] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 27.35/4.00    inference(cnf_transformation,[],[f34])).
% 27.35/4.00  
% 27.35/4.00  fof(f13,axiom,(
% 27.35/4.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 27.35/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.35/4.00  
% 27.35/4.00  fof(f44,plain,(
% 27.35/4.00    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 27.35/4.00    inference(ennf_transformation,[],[f13])).
% 27.35/4.00  
% 27.35/4.00  fof(f45,plain,(
% 27.35/4.00    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 27.35/4.00    inference(flattening,[],[f44])).
% 27.35/4.00  
% 27.35/4.00  fof(f79,plain,(
% 27.35/4.00    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 27.35/4.00    inference(cnf_transformation,[],[f45])).
% 27.35/4.00  
% 27.35/4.00  fof(f103,plain,(
% 27.35/4.00    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 27.35/4.00    inference(definition_unfolding,[],[f79,f88])).
% 27.35/4.00  
% 27.35/4.00  fof(f19,axiom,(
% 27.35/4.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 27.35/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.35/4.00  
% 27.35/4.00  fof(f52,plain,(
% 27.35/4.00    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 27.35/4.00    inference(ennf_transformation,[],[f19])).
% 27.35/4.00  
% 27.35/4.00  fof(f53,plain,(
% 27.35/4.00    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 27.35/4.00    inference(flattening,[],[f52])).
% 27.35/4.00  
% 27.35/4.00  fof(f87,plain,(
% 27.35/4.00    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 27.35/4.00    inference(cnf_transformation,[],[f53])).
% 27.35/4.00  
% 27.35/4.00  fof(f93,plain,(
% 27.35/4.00    v1_funct_1(sK3)),
% 27.35/4.00    inference(cnf_transformation,[],[f62])).
% 27.35/4.00  
% 27.35/4.00  fof(f16,axiom,(
% 27.35/4.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 27.35/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.35/4.00  
% 27.35/4.00  fof(f48,plain,(
% 27.35/4.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 27.35/4.00    inference(ennf_transformation,[],[f16])).
% 27.35/4.00  
% 27.35/4.00  fof(f49,plain,(
% 27.35/4.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 27.35/4.00    inference(flattening,[],[f48])).
% 27.35/4.00  
% 27.35/4.00  fof(f59,plain,(
% 27.35/4.00    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 27.35/4.00    inference(nnf_transformation,[],[f49])).
% 27.35/4.00  
% 27.35/4.00  fof(f82,plain,(
% 27.35/4.00    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 27.35/4.00    inference(cnf_transformation,[],[f59])).
% 27.35/4.00  
% 27.35/4.00  fof(f96,plain,(
% 27.35/4.00    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 27.35/4.00    inference(cnf_transformation,[],[f62])).
% 27.35/4.00  
% 27.35/4.00  fof(f18,axiom,(
% 27.35/4.00    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 27.35/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.35/4.00  
% 27.35/4.00  fof(f26,plain,(
% 27.35/4.00    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 27.35/4.00    inference(pure_predicate_removal,[],[f18])).
% 27.35/4.00  
% 27.35/4.00  fof(f86,plain,(
% 27.35/4.00    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 27.35/4.00    inference(cnf_transformation,[],[f26])).
% 27.35/4.00  
% 27.35/4.00  fof(f17,axiom,(
% 27.35/4.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 27.35/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.35/4.00  
% 27.35/4.00  fof(f50,plain,(
% 27.35/4.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 27.35/4.00    inference(ennf_transformation,[],[f17])).
% 27.35/4.00  
% 27.35/4.00  fof(f51,plain,(
% 27.35/4.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 27.35/4.00    inference(flattening,[],[f50])).
% 27.35/4.00  
% 27.35/4.00  fof(f85,plain,(
% 27.35/4.00    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 27.35/4.00    inference(cnf_transformation,[],[f51])).
% 27.35/4.00  
% 27.35/4.00  fof(f9,axiom,(
% 27.35/4.00    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 27.35/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.35/4.00  
% 27.35/4.00  fof(f37,plain,(
% 27.35/4.00    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 27.35/4.00    inference(ennf_transformation,[],[f9])).
% 27.35/4.00  
% 27.35/4.00  fof(f72,plain,(
% 27.35/4.00    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 27.35/4.00    inference(cnf_transformation,[],[f37])).
% 27.35/4.00  
% 27.35/4.00  fof(f102,plain,(
% 27.35/4.00    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_partfun1(X0),X1) | ~v1_relat_1(X1)) )),
% 27.35/4.00    inference(definition_unfolding,[],[f72,f88])).
% 27.35/4.00  
% 27.35/4.00  fof(f6,axiom,(
% 27.35/4.00    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 27.35/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.35/4.00  
% 27.35/4.00  fof(f32,plain,(
% 27.35/4.00    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 27.35/4.00    inference(ennf_transformation,[],[f6])).
% 27.35/4.00  
% 27.35/4.00  fof(f33,plain,(
% 27.35/4.00    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 27.35/4.00    inference(flattening,[],[f32])).
% 27.35/4.00  
% 27.35/4.00  fof(f69,plain,(
% 27.35/4.00    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 27.35/4.00    inference(cnf_transformation,[],[f33])).
% 27.35/4.00  
% 27.35/4.00  fof(f100,plain,(
% 27.35/4.00    k2_funct_1(sK2) != sK3),
% 27.35/4.00    inference(cnf_transformation,[],[f62])).
% 27.35/4.00  
% 27.35/4.00  cnf(c_35,negated_conjecture,
% 27.35/4.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 27.35/4.00      inference(cnf_transformation,[],[f92]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_786,negated_conjecture,
% 27.35/4.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 27.35/4.00      inference(subtyping,[status(esa)],[c_35]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_1314,plain,
% 27.35/4.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 27.35/4.00      inference(predicate_to_equality,[status(thm)],[c_786]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_17,plain,
% 27.35/4.00      ( v4_relat_1(X0,X1)
% 27.35/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 27.35/4.00      inference(cnf_transformation,[],[f80]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_799,plain,
% 27.35/4.00      ( v4_relat_1(X0_52,X0_53)
% 27.35/4.00      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) ),
% 27.35/4.00      inference(subtyping,[status(esa)],[c_17]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_1305,plain,
% 27.35/4.00      ( v4_relat_1(X0_52,X0_53) = iProver_top
% 27.35/4.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
% 27.35/4.00      inference(predicate_to_equality,[status(thm)],[c_799]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_1954,plain,
% 27.35/4.00      ( v4_relat_1(sK2,sK0) = iProver_top ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_1314,c_1305]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_13,plain,
% 27.35/4.00      ( ~ v2_funct_1(X0)
% 27.35/4.00      | ~ v1_funct_1(X0)
% 27.35/4.00      | ~ v1_relat_1(X0)
% 27.35/4.00      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 27.35/4.00      inference(cnf_transformation,[],[f77]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_30,negated_conjecture,
% 27.35/4.00      ( v2_funct_1(sK2) ),
% 27.35/4.00      inference(cnf_transformation,[],[f97]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_503,plain,
% 27.35/4.00      ( ~ v1_funct_1(X0)
% 27.35/4.00      | ~ v1_relat_1(X0)
% 27.35/4.00      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 27.35/4.00      | sK2 != X0 ),
% 27.35/4.00      inference(resolution_lifted,[status(thm)],[c_13,c_30]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_504,plain,
% 27.35/4.00      ( ~ v1_funct_1(sK2)
% 27.35/4.00      | ~ v1_relat_1(sK2)
% 27.35/4.00      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 27.35/4.00      inference(unflattening,[status(thm)],[c_503]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_36,negated_conjecture,
% 27.35/4.00      ( v1_funct_1(sK2) ),
% 27.35/4.00      inference(cnf_transformation,[],[f91]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_506,plain,
% 27.35/4.00      ( ~ v1_relat_1(sK2)
% 27.35/4.00      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 27.35/4.00      inference(global_propositional_subsumption,
% 27.35/4.00                [status(thm)],
% 27.35/4.00                [c_504,c_36]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_779,plain,
% 27.35/4.00      ( ~ v1_relat_1(sK2)
% 27.35/4.00      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 27.35/4.00      inference(subtyping,[status(esa)],[c_506]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_1321,plain,
% 27.35/4.00      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 27.35/4.00      | v1_relat_1(sK2) != iProver_top ),
% 27.35/4.00      inference(predicate_to_equality,[status(thm)],[c_779]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_0,plain,
% 27.35/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 27.35/4.00      | ~ v1_relat_1(X1)
% 27.35/4.00      | v1_relat_1(X0) ),
% 27.35/4.00      inference(cnf_transformation,[],[f63]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_808,plain,
% 27.35/4.00      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(X1_52))
% 27.35/4.00      | ~ v1_relat_1(X1_52)
% 27.35/4.00      | v1_relat_1(X0_52) ),
% 27.35/4.00      inference(subtyping,[status(esa)],[c_0]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_1364,plain,
% 27.35/4.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0_52))
% 27.35/4.00      | ~ v1_relat_1(X0_52)
% 27.35/4.00      | v1_relat_1(sK2) ),
% 27.35/4.00      inference(instantiation,[status(thm)],[c_808]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_1401,plain,
% 27.35/4.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 27.35/4.00      | ~ v1_relat_1(k2_zfmisc_1(X0_53,X1_53))
% 27.35/4.00      | v1_relat_1(sK2) ),
% 27.35/4.00      inference(instantiation,[status(thm)],[c_1364]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_1445,plain,
% 27.35/4.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 27.35/4.00      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
% 27.35/4.00      | v1_relat_1(sK2) ),
% 27.35/4.00      inference(instantiation,[status(thm)],[c_1401]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_3,plain,
% 27.35/4.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 27.35/4.00      inference(cnf_transformation,[],[f66]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_807,plain,
% 27.35/4.00      ( v1_relat_1(k2_zfmisc_1(X0_53,X1_53)) ),
% 27.35/4.00      inference(subtyping,[status(esa)],[c_3]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_1458,plain,
% 27.35/4.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 27.35/4.00      inference(instantiation,[status(thm)],[c_807]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_1665,plain,
% 27.35/4.00      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 27.35/4.00      inference(global_propositional_subsumption,
% 27.35/4.00                [status(thm)],
% 27.35/4.00                [c_1321,c_35,c_779,c_1445,c_1458]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_2,plain,
% 27.35/4.00      ( r1_tarski(k1_relat_1(X0),X1)
% 27.35/4.00      | ~ v4_relat_1(X0,X1)
% 27.35/4.00      | ~ v1_relat_1(X0) ),
% 27.35/4.00      inference(cnf_transformation,[],[f64]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_8,plain,
% 27.35/4.00      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 27.35/4.00      | ~ v1_relat_1(X0)
% 27.35/4.00      | k5_relat_1(X0,k6_partfun1(X1)) = X0 ),
% 27.35/4.00      inference(cnf_transformation,[],[f101]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_392,plain,
% 27.35/4.00      ( ~ v4_relat_1(X0,X1)
% 27.35/4.00      | ~ v1_relat_1(X0)
% 27.35/4.00      | ~ v1_relat_1(X2)
% 27.35/4.00      | X3 != X1
% 27.35/4.00      | k5_relat_1(X2,k6_partfun1(X3)) = X2
% 27.35/4.00      | k2_relat_1(X2) != k1_relat_1(X0) ),
% 27.35/4.00      inference(resolution_lifted,[status(thm)],[c_2,c_8]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_393,plain,
% 27.35/4.00      ( ~ v4_relat_1(X0,X1)
% 27.35/4.00      | ~ v1_relat_1(X0)
% 27.35/4.00      | ~ v1_relat_1(X2)
% 27.35/4.00      | k5_relat_1(X2,k6_partfun1(X1)) = X2
% 27.35/4.00      | k2_relat_1(X2) != k1_relat_1(X0) ),
% 27.35/4.00      inference(unflattening,[status(thm)],[c_392]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_783,plain,
% 27.35/4.00      ( ~ v4_relat_1(X0_52,X0_53)
% 27.35/4.00      | ~ v1_relat_1(X0_52)
% 27.35/4.00      | ~ v1_relat_1(X1_52)
% 27.35/4.00      | k2_relat_1(X1_52) != k1_relat_1(X0_52)
% 27.35/4.00      | k5_relat_1(X1_52,k6_partfun1(X0_53)) = X1_52 ),
% 27.35/4.00      inference(subtyping,[status(esa)],[c_393]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_1317,plain,
% 27.35/4.00      ( k2_relat_1(X0_52) != k1_relat_1(X1_52)
% 27.35/4.00      | k5_relat_1(X0_52,k6_partfun1(X0_53)) = X0_52
% 27.35/4.00      | v4_relat_1(X1_52,X0_53) != iProver_top
% 27.35/4.00      | v1_relat_1(X1_52) != iProver_top
% 27.35/4.00      | v1_relat_1(X0_52) != iProver_top ),
% 27.35/4.00      inference(predicate_to_equality,[status(thm)],[c_783]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_4387,plain,
% 27.35/4.00      ( k1_relat_1(X0_52) != k1_relat_1(sK2)
% 27.35/4.00      | k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0_53)) = k2_funct_1(sK2)
% 27.35/4.00      | v4_relat_1(X0_52,X0_53) != iProver_top
% 27.35/4.00      | v1_relat_1(X0_52) != iProver_top
% 27.35/4.00      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_1665,c_1317]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_37,plain,
% 27.35/4.00      ( v1_funct_1(sK2) = iProver_top ),
% 27.35/4.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_38,plain,
% 27.35/4.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 27.35/4.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_11,plain,
% 27.35/4.00      ( ~ v1_funct_1(X0)
% 27.35/4.00      | ~ v1_relat_1(X0)
% 27.35/4.00      | v1_relat_1(k2_funct_1(X0)) ),
% 27.35/4.00      inference(cnf_transformation,[],[f73]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_800,plain,
% 27.35/4.00      ( ~ v1_funct_1(X0_52)
% 27.35/4.00      | ~ v1_relat_1(X0_52)
% 27.35/4.00      | v1_relat_1(k2_funct_1(X0_52)) ),
% 27.35/4.00      inference(subtyping,[status(esa)],[c_11]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_867,plain,
% 27.35/4.00      ( v1_funct_1(X0_52) != iProver_top
% 27.35/4.00      | v1_relat_1(X0_52) != iProver_top
% 27.35/4.00      | v1_relat_1(k2_funct_1(X0_52)) = iProver_top ),
% 27.35/4.00      inference(predicate_to_equality,[status(thm)],[c_800]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_869,plain,
% 27.35/4.00      ( v1_funct_1(sK2) != iProver_top
% 27.35/4.00      | v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 27.35/4.00      | v1_relat_1(sK2) != iProver_top ),
% 27.35/4.00      inference(instantiation,[status(thm)],[c_867]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_1446,plain,
% 27.35/4.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 27.35/4.00      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 27.35/4.00      | v1_relat_1(sK2) = iProver_top ),
% 27.35/4.00      inference(predicate_to_equality,[status(thm)],[c_1445]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_1459,plain,
% 27.35/4.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 27.35/4.00      inference(predicate_to_equality,[status(thm)],[c_1458]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_8510,plain,
% 27.35/4.00      ( v1_relat_1(X0_52) != iProver_top
% 27.35/4.00      | v4_relat_1(X0_52,X0_53) != iProver_top
% 27.35/4.00      | k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0_53)) = k2_funct_1(sK2)
% 27.35/4.00      | k1_relat_1(X0_52) != k1_relat_1(sK2) ),
% 27.35/4.00      inference(global_propositional_subsumption,
% 27.35/4.00                [status(thm)],
% 27.35/4.00                [c_4387,c_37,c_38,c_869,c_1446,c_1459]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_8511,plain,
% 27.35/4.00      ( k1_relat_1(X0_52) != k1_relat_1(sK2)
% 27.35/4.00      | k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0_53)) = k2_funct_1(sK2)
% 27.35/4.00      | v4_relat_1(X0_52,X0_53) != iProver_top
% 27.35/4.00      | v1_relat_1(X0_52) != iProver_top ),
% 27.35/4.00      inference(renaming,[status(thm)],[c_8510]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_8517,plain,
% 27.35/4.00      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0_53)) = k2_funct_1(sK2)
% 27.35/4.00      | v4_relat_1(sK2,X0_53) != iProver_top
% 27.35/4.00      | v1_relat_1(sK2) != iProver_top ),
% 27.35/4.00      inference(equality_resolution,[status(thm)],[c_8511]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_81356,plain,
% 27.35/4.00      ( v4_relat_1(sK2,X0_53) != iProver_top
% 27.35/4.00      | k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0_53)) = k2_funct_1(sK2) ),
% 27.35/4.00      inference(global_propositional_subsumption,
% 27.35/4.00                [status(thm)],
% 27.35/4.00                [c_8517,c_38,c_1446,c_1459]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_81357,plain,
% 27.35/4.00      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(X0_53)) = k2_funct_1(sK2)
% 27.35/4.00      | v4_relat_1(sK2,X0_53) != iProver_top ),
% 27.35/4.00      inference(renaming,[status(thm)],[c_81356]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_81362,plain,
% 27.35/4.00      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k2_funct_1(sK2) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_1954,c_81357]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_33,negated_conjecture,
% 27.35/4.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 27.35/4.00      inference(cnf_transformation,[],[f94]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_788,negated_conjecture,
% 27.35/4.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 27.35/4.00      inference(subtyping,[status(esa)],[c_33]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_1312,plain,
% 27.35/4.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 27.35/4.00      inference(predicate_to_equality,[status(thm)],[c_788]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_1296,plain,
% 27.35/4.00      ( m1_subset_1(X0_52,k1_zfmisc_1(X1_52)) != iProver_top
% 27.35/4.00      | v1_relat_1(X1_52) != iProver_top
% 27.35/4.00      | v1_relat_1(X0_52) = iProver_top ),
% 27.35/4.00      inference(predicate_to_equality,[status(thm)],[c_808]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_1576,plain,
% 27.35/4.00      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 27.35/4.00      | v1_relat_1(sK3) = iProver_top ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_1312,c_1296]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_40,plain,
% 27.35/4.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 27.35/4.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_1435,plain,
% 27.35/4.00      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 27.35/4.00      | v1_relat_1(X0_52)
% 27.35/4.00      | ~ v1_relat_1(k2_zfmisc_1(X0_53,X1_53)) ),
% 27.35/4.00      inference(instantiation,[status(thm)],[c_808]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_1529,plain,
% 27.35/4.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 27.35/4.00      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
% 27.35/4.00      | v1_relat_1(sK3) ),
% 27.35/4.00      inference(instantiation,[status(thm)],[c_1435]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_1530,plain,
% 27.35/4.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 27.35/4.00      | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 27.35/4.00      | v1_relat_1(sK3) = iProver_top ),
% 27.35/4.00      inference(predicate_to_equality,[status(thm)],[c_1529]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_1567,plain,
% 27.35/4.00      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
% 27.35/4.00      inference(instantiation,[status(thm)],[c_807]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_1568,plain,
% 27.35/4.00      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
% 27.35/4.00      inference(predicate_to_equality,[status(thm)],[c_1567]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_1668,plain,
% 27.35/4.00      ( v1_relat_1(sK3) = iProver_top ),
% 27.35/4.00      inference(global_propositional_subsumption,
% 27.35/4.00                [status(thm)],
% 27.35/4.00                [c_1576,c_40,c_1530,c_1568]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_1577,plain,
% 27.35/4.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 27.35/4.00      | v1_relat_1(sK2) = iProver_top ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_1314,c_1296]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_1701,plain,
% 27.35/4.00      ( v1_relat_1(sK2) = iProver_top ),
% 27.35/4.00      inference(global_propositional_subsumption,
% 27.35/4.00                [status(thm)],
% 27.35/4.00                [c_1577,c_38,c_1446,c_1459]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_25,plain,
% 27.35/4.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 27.35/4.00      | ~ v1_funct_1(X0)
% 27.35/4.00      | ~ v1_relat_1(X0) ),
% 27.35/4.00      inference(cnf_transformation,[],[f90]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_793,plain,
% 27.35/4.00      ( m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_52),k2_relat_1(X0_52))))
% 27.35/4.00      | ~ v1_funct_1(X0_52)
% 27.35/4.00      | ~ v1_relat_1(X0_52) ),
% 27.35/4.00      inference(subtyping,[status(esa)],[c_25]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_1311,plain,
% 27.35/4.00      ( m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_52),k2_relat_1(X0_52)))) = iProver_top
% 27.35/4.00      | v1_funct_1(X0_52) != iProver_top
% 27.35/4.00      | v1_relat_1(X0_52) != iProver_top ),
% 27.35/4.00      inference(predicate_to_equality,[status(thm)],[c_793]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_2504,plain,
% 27.35/4.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) = iProver_top
% 27.35/4.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 27.35/4.00      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_1665,c_1311]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_18,plain,
% 27.35/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.35/4.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 27.35/4.00      inference(cnf_transformation,[],[f81]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_798,plain,
% 27.35/4.00      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 27.35/4.00      | k2_relset_1(X0_53,X1_53,X0_52) = k2_relat_1(X0_52) ),
% 27.35/4.00      inference(subtyping,[status(esa)],[c_18]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_1306,plain,
% 27.35/4.00      ( k2_relset_1(X0_53,X1_53,X0_52) = k2_relat_1(X0_52)
% 27.35/4.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
% 27.35/4.00      inference(predicate_to_equality,[status(thm)],[c_798]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_2049,plain,
% 27.35/4.00      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_1314,c_1306]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_32,negated_conjecture,
% 27.35/4.00      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 27.35/4.00      inference(cnf_transformation,[],[f95]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_789,negated_conjecture,
% 27.35/4.00      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 27.35/4.00      inference(subtyping,[status(esa)],[c_32]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_2051,plain,
% 27.35/4.00      ( k2_relat_1(sK2) = sK1 ),
% 27.35/4.00      inference(light_normalisation,[status(thm)],[c_2049,c_789]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_14,plain,
% 27.35/4.00      ( ~ v2_funct_1(X0)
% 27.35/4.00      | ~ v1_funct_1(X0)
% 27.35/4.00      | ~ v1_relat_1(X0)
% 27.35/4.00      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 27.35/4.00      inference(cnf_transformation,[],[f76]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_489,plain,
% 27.35/4.00      ( ~ v1_funct_1(X0)
% 27.35/4.00      | ~ v1_relat_1(X0)
% 27.35/4.00      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 27.35/4.00      | sK2 != X0 ),
% 27.35/4.00      inference(resolution_lifted,[status(thm)],[c_14,c_30]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_490,plain,
% 27.35/4.00      ( ~ v1_funct_1(sK2)
% 27.35/4.00      | ~ v1_relat_1(sK2)
% 27.35/4.00      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 27.35/4.00      inference(unflattening,[status(thm)],[c_489]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_492,plain,
% 27.35/4.00      ( ~ v1_relat_1(sK2)
% 27.35/4.00      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 27.35/4.00      inference(global_propositional_subsumption,
% 27.35/4.00                [status(thm)],
% 27.35/4.00                [c_490,c_36]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_780,plain,
% 27.35/4.00      ( ~ v1_relat_1(sK2)
% 27.35/4.00      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 27.35/4.00      inference(subtyping,[status(esa)],[c_492]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_1320,plain,
% 27.35/4.00      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 27.35/4.00      | v1_relat_1(sK2) != iProver_top ),
% 27.35/4.00      inference(predicate_to_equality,[status(thm)],[c_780]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_1642,plain,
% 27.35/4.00      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 27.35/4.00      inference(global_propositional_subsumption,
% 27.35/4.00                [status(thm)],
% 27.35/4.00                [c_1320,c_35,c_780,c_1445,c_1458]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_2078,plain,
% 27.35/4.00      ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
% 27.35/4.00      inference(demodulation,[status(thm)],[c_2051,c_1642]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_2508,plain,
% 27.35/4.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top
% 27.35/4.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 27.35/4.00      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 27.35/4.00      inference(light_normalisation,[status(thm)],[c_2504,c_2078]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_10,plain,
% 27.35/4.00      ( ~ v1_funct_1(X0)
% 27.35/4.00      | v1_funct_1(k2_funct_1(X0))
% 27.35/4.00      | ~ v1_relat_1(X0) ),
% 27.35/4.00      inference(cnf_transformation,[],[f74]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_801,plain,
% 27.35/4.00      ( ~ v1_funct_1(X0_52)
% 27.35/4.00      | v1_funct_1(k2_funct_1(X0_52))
% 27.35/4.00      | ~ v1_relat_1(X0_52) ),
% 27.35/4.00      inference(subtyping,[status(esa)],[c_10]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_864,plain,
% 27.35/4.00      ( v1_funct_1(X0_52) != iProver_top
% 27.35/4.00      | v1_funct_1(k2_funct_1(X0_52)) = iProver_top
% 27.35/4.00      | v1_relat_1(X0_52) != iProver_top ),
% 27.35/4.00      inference(predicate_to_equality,[status(thm)],[c_801]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_866,plain,
% 27.35/4.00      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 27.35/4.00      | v1_funct_1(sK2) != iProver_top
% 27.35/4.00      | v1_relat_1(sK2) != iProver_top ),
% 27.35/4.00      inference(instantiation,[status(thm)],[c_864]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_5605,plain,
% 27.35/4.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top ),
% 27.35/4.00      inference(global_propositional_subsumption,
% 27.35/4.00                [status(thm)],
% 27.35/4.00                [c_2508,c_37,c_38,c_866,c_869,c_1446,c_1459]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_5614,plain,
% 27.35/4.00      ( v1_relat_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))) != iProver_top
% 27.35/4.00      | v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_5605,c_1296]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_6196,plain,
% 27.35/4.00      ( v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
% 27.35/4.00      inference(global_propositional_subsumption,
% 27.35/4.00                [status(thm)],
% 27.35/4.00                [c_5614,c_37,c_38,c_869,c_1446,c_1459]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_7,plain,
% 27.35/4.00      ( ~ v1_relat_1(X0)
% 27.35/4.00      | ~ v1_relat_1(X1)
% 27.35/4.00      | ~ v1_relat_1(X2)
% 27.35/4.00      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ),
% 27.35/4.00      inference(cnf_transformation,[],[f70]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_803,plain,
% 27.35/4.00      ( ~ v1_relat_1(X0_52)
% 27.35/4.00      | ~ v1_relat_1(X1_52)
% 27.35/4.00      | ~ v1_relat_1(X2_52)
% 27.35/4.00      | k5_relat_1(k5_relat_1(X0_52,X1_52),X2_52) = k5_relat_1(X0_52,k5_relat_1(X1_52,X2_52)) ),
% 27.35/4.00      inference(subtyping,[status(esa)],[c_7]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_1301,plain,
% 27.35/4.00      ( k5_relat_1(k5_relat_1(X0_52,X1_52),X2_52) = k5_relat_1(X0_52,k5_relat_1(X1_52,X2_52))
% 27.35/4.00      | v1_relat_1(X0_52) != iProver_top
% 27.35/4.00      | v1_relat_1(X1_52) != iProver_top
% 27.35/4.00      | v1_relat_1(X2_52) != iProver_top ),
% 27.35/4.00      inference(predicate_to_equality,[status(thm)],[c_803]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_6205,plain,
% 27.35/4.00      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0_52,X1_52)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0_52),X1_52)
% 27.35/4.00      | v1_relat_1(X0_52) != iProver_top
% 27.35/4.00      | v1_relat_1(X1_52) != iProver_top ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_6196,c_1301]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_12538,plain,
% 27.35/4.00      ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),X0_52) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0_52))
% 27.35/4.00      | v1_relat_1(X0_52) != iProver_top ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_1701,c_6205]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_15,plain,
% 27.35/4.00      ( ~ v2_funct_1(X0)
% 27.35/4.00      | ~ v1_funct_1(X0)
% 27.35/4.00      | ~ v1_relat_1(X0)
% 27.35/4.00      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
% 27.35/4.00      inference(cnf_transformation,[],[f103]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_475,plain,
% 27.35/4.00      ( ~ v1_funct_1(X0)
% 27.35/4.00      | ~ v1_relat_1(X0)
% 27.35/4.00      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
% 27.35/4.00      | sK2 != X0 ),
% 27.35/4.00      inference(resolution_lifted,[status(thm)],[c_15,c_30]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_476,plain,
% 27.35/4.00      ( ~ v1_funct_1(sK2)
% 27.35/4.00      | ~ v1_relat_1(sK2)
% 27.35/4.00      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 27.35/4.00      inference(unflattening,[status(thm)],[c_475]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_478,plain,
% 27.35/4.00      ( ~ v1_relat_1(sK2)
% 27.35/4.00      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 27.35/4.00      inference(global_propositional_subsumption,
% 27.35/4.00                [status(thm)],
% 27.35/4.00                [c_476,c_36]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_781,plain,
% 27.35/4.00      ( ~ v1_relat_1(sK2)
% 27.35/4.00      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 27.35/4.00      inference(subtyping,[status(esa)],[c_478]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_1319,plain,
% 27.35/4.00      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
% 27.35/4.00      | v1_relat_1(sK2) != iProver_top ),
% 27.35/4.00      inference(predicate_to_equality,[status(thm)],[c_781]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_1768,plain,
% 27.35/4.00      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 27.35/4.00      inference(global_propositional_subsumption,
% 27.35/4.00                [status(thm)],
% 27.35/4.00                [c_1319,c_35,c_781,c_1445,c_1458]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_2077,plain,
% 27.35/4.00      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
% 27.35/4.00      inference(demodulation,[status(thm)],[c_2051,c_1768]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_12548,plain,
% 27.35/4.00      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0_52)) = k5_relat_1(k6_partfun1(sK1),X0_52)
% 27.35/4.00      | v1_relat_1(X0_52) != iProver_top ),
% 27.35/4.00      inference(light_normalisation,[status(thm)],[c_12538,c_2077]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_12628,plain,
% 27.35/4.00      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_1668,c_12548]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_24,plain,
% 27.35/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.35/4.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 27.35/4.00      | ~ v1_funct_1(X0)
% 27.35/4.00      | ~ v1_funct_1(X3)
% 27.35/4.00      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 27.35/4.00      inference(cnf_transformation,[],[f87]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_794,plain,
% 27.35/4.00      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 27.35/4.00      | ~ m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(X2_53,X3_53)))
% 27.35/4.00      | ~ v1_funct_1(X0_52)
% 27.35/4.00      | ~ v1_funct_1(X1_52)
% 27.35/4.00      | k1_partfun1(X2_53,X3_53,X0_53,X1_53,X1_52,X0_52) = k5_relat_1(X1_52,X0_52) ),
% 27.35/4.00      inference(subtyping,[status(esa)],[c_24]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_1310,plain,
% 27.35/4.00      ( k1_partfun1(X0_53,X1_53,X2_53,X3_53,X0_52,X1_52) = k5_relat_1(X0_52,X1_52)
% 27.35/4.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 27.35/4.00      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(X2_53,X3_53))) != iProver_top
% 27.35/4.00      | v1_funct_1(X1_52) != iProver_top
% 27.35/4.00      | v1_funct_1(X0_52) != iProver_top ),
% 27.35/4.00      inference(predicate_to_equality,[status(thm)],[c_794]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_3227,plain,
% 27.35/4.00      ( k1_partfun1(X0_53,X1_53,sK1,sK0,X0_52,sK3) = k5_relat_1(X0_52,sK3)
% 27.35/4.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 27.35/4.00      | v1_funct_1(X0_52) != iProver_top
% 27.35/4.00      | v1_funct_1(sK3) != iProver_top ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_1312,c_1310]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_34,negated_conjecture,
% 27.35/4.00      ( v1_funct_1(sK3) ),
% 27.35/4.00      inference(cnf_transformation,[],[f93]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_39,plain,
% 27.35/4.00      ( v1_funct_1(sK3) = iProver_top ),
% 27.35/4.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_3574,plain,
% 27.35/4.00      ( v1_funct_1(X0_52) != iProver_top
% 27.35/4.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 27.35/4.00      | k1_partfun1(X0_53,X1_53,sK1,sK0,X0_52,sK3) = k5_relat_1(X0_52,sK3) ),
% 27.35/4.00      inference(global_propositional_subsumption,
% 27.35/4.00                [status(thm)],
% 27.35/4.00                [c_3227,c_39]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_3575,plain,
% 27.35/4.00      ( k1_partfun1(X0_53,X1_53,sK1,sK0,X0_52,sK3) = k5_relat_1(X0_52,sK3)
% 27.35/4.00      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 27.35/4.00      | v1_funct_1(X0_52) != iProver_top ),
% 27.35/4.00      inference(renaming,[status(thm)],[c_3574]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_3581,plain,
% 27.35/4.00      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 27.35/4.00      | v1_funct_1(sK2) != iProver_top ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_1314,c_3575]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_20,plain,
% 27.35/4.00      ( ~ r2_relset_1(X0,X1,X2,X3)
% 27.35/4.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 27.35/4.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 27.35/4.00      | X3 = X2 ),
% 27.35/4.00      inference(cnf_transformation,[],[f82]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_31,negated_conjecture,
% 27.35/4.00      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 27.35/4.00      inference(cnf_transformation,[],[f96]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_374,plain,
% 27.35/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.35/4.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.35/4.00      | X3 = X0
% 27.35/4.00      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 27.35/4.00      | k6_partfun1(sK0) != X3
% 27.35/4.00      | sK0 != X2
% 27.35/4.00      | sK0 != X1 ),
% 27.35/4.00      inference(resolution_lifted,[status(thm)],[c_20,c_31]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_375,plain,
% 27.35/4.00      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 27.35/4.00      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 27.35/4.00      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 27.35/4.00      inference(unflattening,[status(thm)],[c_374]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_23,plain,
% 27.35/4.00      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 27.35/4.00      inference(cnf_transformation,[],[f86]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_51,plain,
% 27.35/4.00      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 27.35/4.00      inference(instantiation,[status(thm)],[c_23]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_377,plain,
% 27.35/4.00      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 27.35/4.00      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 27.35/4.00      inference(global_propositional_subsumption,
% 27.35/4.00                [status(thm)],
% 27.35/4.00                [c_375,c_51]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_784,plain,
% 27.35/4.00      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 27.35/4.00      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 27.35/4.00      inference(subtyping,[status(esa)],[c_377]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_1316,plain,
% 27.35/4.00      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 27.35/4.00      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 27.35/4.00      inference(predicate_to_equality,[status(thm)],[c_784]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_21,plain,
% 27.35/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.35/4.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 27.35/4.00      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 27.35/4.00      | ~ v1_funct_1(X0)
% 27.35/4.00      | ~ v1_funct_1(X3) ),
% 27.35/4.00      inference(cnf_transformation,[],[f85]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_797,plain,
% 27.35/4.00      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 27.35/4.00      | ~ m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(X2_53,X3_53)))
% 27.35/4.00      | m1_subset_1(k1_partfun1(X2_53,X3_53,X0_53,X1_53,X1_52,X0_52),k1_zfmisc_1(k2_zfmisc_1(X2_53,X1_53)))
% 27.35/4.00      | ~ v1_funct_1(X0_52)
% 27.35/4.00      | ~ v1_funct_1(X1_52) ),
% 27.35/4.00      inference(subtyping,[status(esa)],[c_21]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_1376,plain,
% 27.35/4.00      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 27.35/4.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 27.35/4.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 27.35/4.00      | ~ v1_funct_1(sK3)
% 27.35/4.00      | ~ v1_funct_1(sK2) ),
% 27.35/4.00      inference(instantiation,[status(thm)],[c_797]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_1819,plain,
% 27.35/4.00      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 27.35/4.00      inference(global_propositional_subsumption,
% 27.35/4.00                [status(thm)],
% 27.35/4.00                [c_1316,c_36,c_35,c_34,c_33,c_784,c_1376]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_3587,plain,
% 27.35/4.00      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 27.35/4.00      | v1_funct_1(sK2) != iProver_top ),
% 27.35/4.00      inference(light_normalisation,[status(thm)],[c_3581,c_1819]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_3797,plain,
% 27.35/4.00      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 27.35/4.00      inference(global_propositional_subsumption,
% 27.35/4.00                [status(thm)],
% 27.35/4.00                [c_3587,c_37]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_12638,plain,
% 27.35/4.00      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
% 27.35/4.00      inference(light_normalisation,[status(thm)],[c_12628,c_3797]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_9,plain,
% 27.35/4.00      ( ~ v1_relat_1(X0)
% 27.35/4.00      | k5_relat_1(k6_partfun1(X1),X0) = k7_relat_1(X0,X1) ),
% 27.35/4.00      inference(cnf_transformation,[],[f102]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_802,plain,
% 27.35/4.00      ( ~ v1_relat_1(X0_52)
% 27.35/4.00      | k5_relat_1(k6_partfun1(X0_53),X0_52) = k7_relat_1(X0_52,X0_53) ),
% 27.35/4.00      inference(subtyping,[status(esa)],[c_9]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_1302,plain,
% 27.35/4.00      ( k5_relat_1(k6_partfun1(X0_53),X0_52) = k7_relat_1(X0_52,X0_53)
% 27.35/4.00      | v1_relat_1(X0_52) != iProver_top ),
% 27.35/4.00      inference(predicate_to_equality,[status(thm)],[c_802]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_1824,plain,
% 27.35/4.00      ( k5_relat_1(k6_partfun1(X0_53),sK3) = k7_relat_1(sK3,X0_53) ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_1668,c_1302]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_1953,plain,
% 27.35/4.00      ( v4_relat_1(sK3,sK1) = iProver_top ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_1312,c_1305]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_6,plain,
% 27.35/4.00      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 27.35/4.00      inference(cnf_transformation,[],[f69]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_804,plain,
% 27.35/4.00      ( ~ v4_relat_1(X0_52,X0_53)
% 27.35/4.00      | ~ v1_relat_1(X0_52)
% 27.35/4.00      | k7_relat_1(X0_52,X0_53) = X0_52 ),
% 27.35/4.00      inference(subtyping,[status(esa)],[c_6]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_1300,plain,
% 27.35/4.00      ( k7_relat_1(X0_52,X0_53) = X0_52
% 27.35/4.00      | v4_relat_1(X0_52,X0_53) != iProver_top
% 27.35/4.00      | v1_relat_1(X0_52) != iProver_top ),
% 27.35/4.00      inference(predicate_to_equality,[status(thm)],[c_804]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_2419,plain,
% 27.35/4.00      ( k7_relat_1(sK3,sK1) = sK3 | v1_relat_1(sK3) != iProver_top ),
% 27.35/4.00      inference(superposition,[status(thm)],[c_1953,c_1300]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_3437,plain,
% 27.35/4.00      ( k7_relat_1(sK3,sK1) = sK3 ),
% 27.35/4.00      inference(global_propositional_subsumption,
% 27.35/4.00                [status(thm)],
% 27.35/4.00                [c_2419,c_40,c_1530,c_1568]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_12639,plain,
% 27.35/4.00      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = sK3 ),
% 27.35/4.00      inference(demodulation,[status(thm)],[c_12638,c_1824,c_3437]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_81365,plain,
% 27.35/4.00      ( k2_funct_1(sK2) = sK3 ),
% 27.35/4.00      inference(light_normalisation,[status(thm)],[c_81362,c_12639]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_27,negated_conjecture,
% 27.35/4.00      ( k2_funct_1(sK2) != sK3 ),
% 27.35/4.00      inference(cnf_transformation,[],[f100]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(c_792,negated_conjecture,
% 27.35/4.00      ( k2_funct_1(sK2) != sK3 ),
% 27.35/4.00      inference(subtyping,[status(esa)],[c_27]) ).
% 27.35/4.00  
% 27.35/4.00  cnf(contradiction,plain,
% 27.35/4.00      ( $false ),
% 27.35/4.00      inference(minisat,[status(thm)],[c_81365,c_792]) ).
% 27.35/4.00  
% 27.35/4.00  
% 27.35/4.00  % SZS output end CNFRefutation for theBenchmark.p
% 27.35/4.00  
% 27.35/4.00  ------                               Statistics
% 27.35/4.00  
% 27.35/4.00  ------ General
% 27.35/4.00  
% 27.35/4.00  abstr_ref_over_cycles:                  0
% 27.35/4.00  abstr_ref_under_cycles:                 0
% 27.35/4.00  gc_basic_clause_elim:                   0
% 27.35/4.00  forced_gc_time:                         0
% 27.35/4.00  parsing_time:                           0.013
% 27.35/4.00  unif_index_cands_time:                  0.
% 27.35/4.00  unif_index_add_time:                    0.
% 27.35/4.00  orderings_time:                         0.
% 27.35/4.00  out_proof_time:                         0.024
% 27.35/4.00  total_time:                             3.227
% 27.35/4.00  num_of_symbols:                         58
% 27.35/4.00  num_of_terms:                           93590
% 27.35/4.00  
% 27.35/4.00  ------ Preprocessing
% 27.35/4.00  
% 27.35/4.00  num_of_splits:                          0
% 27.35/4.00  num_of_split_atoms:                     0
% 27.35/4.00  num_of_reused_defs:                     0
% 27.35/4.00  num_eq_ax_congr_red:                    14
% 27.35/4.00  num_of_sem_filtered_clauses:            1
% 27.35/4.00  num_of_subtypes:                        3
% 27.35/4.00  monotx_restored_types:                  1
% 27.35/4.00  sat_num_of_epr_types:                   0
% 27.35/4.00  sat_num_of_non_cyclic_types:            0
% 27.35/4.00  sat_guarded_non_collapsed_types:        0
% 27.35/4.00  num_pure_diseq_elim:                    0
% 27.35/4.00  simp_replaced_by:                       0
% 27.35/4.00  res_preprocessed:                       168
% 27.35/4.00  prep_upred:                             0
% 27.35/4.00  prep_unflattend:                        14
% 27.35/4.00  smt_new_axioms:                         0
% 27.35/4.00  pred_elim_cands:                        4
% 27.35/4.00  pred_elim:                              3
% 27.35/4.00  pred_elim_cl:                           5
% 27.35/4.00  pred_elim_cycles:                       6
% 27.35/4.00  merged_defs:                            0
% 27.35/4.00  merged_defs_ncl:                        0
% 27.35/4.00  bin_hyper_res:                          0
% 27.35/4.00  prep_cycles:                            4
% 27.35/4.00  pred_elim_time:                         0.003
% 27.35/4.00  splitting_time:                         0.
% 27.35/4.00  sem_filter_time:                        0.
% 27.35/4.00  monotx_time:                            0.
% 27.35/4.00  subtype_inf_time:                       0.001
% 27.35/4.00  
% 27.35/4.00  ------ Problem properties
% 27.35/4.00  
% 27.35/4.00  clauses:                                31
% 27.35/4.00  conjectures:                            8
% 27.35/4.00  epr:                                    4
% 27.35/4.00  horn:                                   31
% 27.35/4.00  ground:                                 13
% 27.35/4.00  unary:                                  10
% 27.35/4.00  binary:                                 11
% 27.35/4.00  lits:                                   71
% 27.35/4.00  lits_eq:                                19
% 27.35/4.00  fd_pure:                                0
% 27.35/4.00  fd_pseudo:                              0
% 27.35/4.00  fd_cond:                                0
% 27.35/4.00  fd_pseudo_cond:                         0
% 27.35/4.00  ac_symbols:                             0
% 27.35/4.00  
% 27.35/4.00  ------ Propositional Solver
% 27.35/4.00  
% 27.35/4.00  prop_solver_calls:                      48
% 27.35/4.00  prop_fast_solver_calls:                 4325
% 27.35/4.00  smt_solver_calls:                       0
% 27.35/4.00  smt_fast_solver_calls:                  0
% 27.35/4.00  prop_num_of_clauses:                    29564
% 27.35/4.00  prop_preprocess_simplified:             57945
% 27.35/4.00  prop_fo_subsumed:                       909
% 27.35/4.00  prop_solver_time:                       0.
% 27.35/4.00  smt_solver_time:                        0.
% 27.35/4.00  smt_fast_solver_time:                   0.
% 27.35/4.00  prop_fast_solver_time:                  0.
% 27.35/4.00  prop_unsat_core_time:                   0.005
% 27.35/4.00  
% 27.35/4.00  ------ QBF
% 27.35/4.00  
% 27.35/4.00  qbf_q_res:                              0
% 27.35/4.00  qbf_num_tautologies:                    0
% 27.35/4.00  qbf_prep_cycles:                        0
% 27.35/4.00  
% 27.35/4.00  ------ BMC1
% 27.35/4.00  
% 27.35/4.00  bmc1_current_bound:                     -1
% 27.35/4.00  bmc1_last_solved_bound:                 -1
% 27.35/4.00  bmc1_unsat_core_size:                   -1
% 27.35/4.00  bmc1_unsat_core_parents_size:           -1
% 27.35/4.00  bmc1_merge_next_fun:                    0
% 27.35/4.00  bmc1_unsat_core_clauses_time:           0.
% 27.35/4.00  
% 27.35/4.00  ------ Instantiation
% 27.35/4.00  
% 27.35/4.00  inst_num_of_clauses:                    3796
% 27.35/4.00  inst_num_in_passive:                    643
% 27.35/4.00  inst_num_in_active:                     4031
% 27.35/4.00  inst_num_in_unprocessed:                1535
% 27.35/4.00  inst_num_of_loops:                      4629
% 27.35/4.00  inst_num_of_learning_restarts:          1
% 27.35/4.00  inst_num_moves_active_passive:          583
% 27.35/4.00  inst_lit_activity:                      0
% 27.35/4.00  inst_lit_activity_moves:                3
% 27.35/4.00  inst_num_tautologies:                   0
% 27.35/4.00  inst_num_prop_implied:                  0
% 27.35/4.00  inst_num_existing_simplified:           0
% 27.35/4.00  inst_num_eq_res_simplified:             0
% 27.35/4.00  inst_num_child_elim:                    0
% 27.35/4.00  inst_num_of_dismatching_blockings:      17950
% 27.35/4.00  inst_num_of_non_proper_insts:           14899
% 27.35/4.00  inst_num_of_duplicates:                 0
% 27.35/4.00  inst_inst_num_from_inst_to_res:         0
% 27.35/4.00  inst_dismatching_checking_time:         0.
% 27.35/4.00  
% 27.35/4.00  ------ Resolution
% 27.35/4.00  
% 27.35/4.00  res_num_of_clauses:                     50
% 27.35/4.00  res_num_in_passive:                     50
% 27.35/4.00  res_num_in_active:                      0
% 27.35/4.00  res_num_of_loops:                       172
% 27.35/4.00  res_forward_subset_subsumed:            615
% 27.35/4.00  res_backward_subset_subsumed:           22
% 27.35/4.00  res_forward_subsumed:                   0
% 27.35/4.00  res_backward_subsumed:                  0
% 27.35/4.00  res_forward_subsumption_resolution:     0
% 27.35/4.00  res_backward_subsumption_resolution:    0
% 27.35/4.00  res_clause_to_clause_subsumption:       12241
% 27.35/4.00  res_orphan_elimination:                 0
% 27.35/4.00  res_tautology_del:                      1275
% 27.35/4.00  res_num_eq_res_simplified:              0
% 27.35/4.00  res_num_sel_changes:                    0
% 27.35/4.00  res_moves_from_active_to_pass:          0
% 27.35/4.00  
% 27.35/4.00  ------ Superposition
% 27.35/4.00  
% 27.35/4.00  sup_time_total:                         0.
% 27.35/4.00  sup_time_generating:                    0.
% 27.35/4.00  sup_time_sim_full:                      0.
% 27.35/4.00  sup_time_sim_immed:                     0.
% 27.35/4.00  
% 27.35/4.00  sup_num_of_clauses:                     4232
% 27.35/4.00  sup_num_in_active:                      832
% 27.35/4.00  sup_num_in_passive:                     3400
% 27.35/4.00  sup_num_of_loops:                       925
% 27.35/4.00  sup_fw_superposition:                   2865
% 27.35/4.00  sup_bw_superposition:                   1937
% 27.35/4.00  sup_immediate_simplified:               1516
% 27.35/4.00  sup_given_eliminated:                   1
% 27.35/4.00  comparisons_done:                       0
% 27.35/4.00  comparisons_avoided:                    0
% 27.35/4.00  
% 27.35/4.00  ------ Simplifications
% 27.35/4.00  
% 27.35/4.00  
% 27.35/4.00  sim_fw_subset_subsumed:                 97
% 27.35/4.00  sim_bw_subset_subsumed:                 217
% 27.35/4.00  sim_fw_subsumed:                        23
% 27.35/4.00  sim_bw_subsumed:                        26
% 27.35/4.00  sim_fw_subsumption_res:                 0
% 27.35/4.00  sim_bw_subsumption_res:                 0
% 27.35/4.00  sim_tautology_del:                      3
% 27.35/4.00  sim_eq_tautology_del:                   146
% 27.35/4.00  sim_eq_res_simp:                        0
% 27.35/4.00  sim_fw_demodulated:                     233
% 27.35/4.00  sim_bw_demodulated:                     46
% 27.35/4.00  sim_light_normalised:                   1281
% 27.35/4.00  sim_joinable_taut:                      0
% 27.35/4.00  sim_joinable_simp:                      0
% 27.35/4.00  sim_ac_normalised:                      0
% 27.35/4.00  sim_smt_subsumption:                    0
% 27.35/4.00  
%------------------------------------------------------------------------------
