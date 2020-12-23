%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:19 EST 2020

% Result     : Theorem 7.73s
% Output     : CNFRefutation 7.73s
% Verified   : 
% Statistics : Number of formulae       :  223 (1058 expanded)
%              Number of clauses        :  126 ( 345 expanded)
%              Number of leaves         :   26 ( 237 expanded)
%              Depth                    :   25
%              Number of atoms          :  644 (6728 expanded)
%              Number of equality atoms :  282 (2564 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f24,conjecture,(
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

fof(f25,negated_conjecture,(
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
    inference(negated_conjecture,[],[f24])).

fof(f26,plain,(
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
    inference(pure_predicate_removal,[],[f25])).

fof(f52,plain,(
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
    inference(ennf_transformation,[],[f26])).

fof(f53,plain,(
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
    inference(flattening,[],[f52])).

fof(f59,plain,(
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

fof(f58,plain,
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

fof(f60,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f53,f59,f58])).

fof(f97,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f60])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f95,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f60])).

fof(f94,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f60])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

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

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f98,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f60])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f43,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f42])).

fof(f84,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f23,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f93,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f23])).

fof(f109,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f84,f93])).

fof(f100,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f60])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f107,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_partfun1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f77,f93])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f51,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f50])).

fof(f92,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f96,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f60])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f46])).

fof(f57,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f99,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f60])).

fof(f20,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f89,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f111,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f89,f93])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f49,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f48])).

fof(f91,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f78,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f108,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f78,f93])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f41,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f40])).

fof(f82,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f11,axiom,(
    ! [X0] : k4_relat_1(k6_relat_1(X0)) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0] : k4_relat_1(k6_relat_1(X0)) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f106,plain,(
    ! [X0] : k4_relat_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
    inference(definition_unfolding,[],[f76,f93,f93])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f70,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f10,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f104,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f75,f93])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f67,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f54])).

fof(f63,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f103,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1204,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1221,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2996,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1204,c_1221])).

cnf(c_45,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_1504,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2156,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1504])).

cnf(c_2157,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2156])).

cnf(c_7,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2236,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2237,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2236])).

cnf(c_3063,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2996,c_45,c_2157,c_2237])).

cnf(c_40,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1202,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_2997,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1202,c_1221])).

cnf(c_43,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_1283,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
    | ~ v1_relat_1(X0)
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1342,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1283])).

cnf(c_1514,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1342])).

cnf(c_1515,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1514])).

cnf(c_1544,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1545,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1544])).

cnf(c_3071,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2997,c_43,c_1515,c_1545])).

cnf(c_41,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1201,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_19,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1210,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1214,plain,
    ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4587,plain,
    ( k5_relat_1(k2_funct_1(X0),k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(k2_funct_1(X0),X1),X2)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1210,c_1214])).

cnf(c_21411,plain,
    ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1201,c_4587])).

cnf(c_21894,plain,
    ( v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_21411,c_43,c_1515,c_1545])).

cnf(c_21895,plain,
    ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_21894])).

cnf(c_21903,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3071,c_21895])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1209,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2136,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1202,c_1209])).

cnf(c_37,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_2137,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2136,c_37])).

cnf(c_22,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_35,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_453,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_35])).

cnf(c_454,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(unflattening,[status(thm)],[c_453])).

cnf(c_456,plain,
    ( ~ v1_relat_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_454,c_41])).

cnf(c_1197,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_456])).

cnf(c_1659,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1197,c_41,c_40,c_454,c_1514,c_1544])).

cnf(c_2140,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(demodulation,[status(thm)],[c_2137,c_1659])).

cnf(c_21910,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k6_partfun1(sK1),X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_21903,c_2140])).

cnf(c_22042,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
    inference(superposition,[status(thm)],[c_3063,c_21910])).

cnf(c_24,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_5,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_401,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_24,c_5])).

cnf(c_1200,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_401])).

cnf(c_1926,plain,
    ( r1_tarski(k1_relat_1(sK3),sK1) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1204,c_1200])).

cnf(c_2372,plain,
    ( r1_tarski(k1_relat_1(sK3),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1926,c_45,c_2157,c_2237])).

cnf(c_16,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k6_partfun1(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1213,plain,
    ( k5_relat_1(k6_partfun1(X0),X1) = X1
    | r1_tarski(k1_relat_1(X1),X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3401,plain,
    ( k5_relat_1(k6_partfun1(sK1),sK3) = sK3
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2372,c_1213])).

cnf(c_4265,plain,
    ( k5_relat_1(k6_partfun1(sK1),sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3401,c_45,c_2157,c_2237])).

cnf(c_31,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1205,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_4723,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1204,c_1205])).

cnf(c_39,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_44,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_4889,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4723,c_44])).

cnf(c_4890,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4889])).

cnf(c_4898,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1202,c_4890])).

cnf(c_27,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_36,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_422,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_36])).

cnf(c_423,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_422])).

cnf(c_28,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_58,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_425,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_423,c_58])).

cnf(c_1199,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_425])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1275,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_1801,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1199,c_41,c_40,c_39,c_38,c_58,c_423,c_1275])).

cnf(c_4899,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4898,c_1801])).

cnf(c_42,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_5298,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4899,c_42])).

cnf(c_17,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1212,plain,
    ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2804,plain,
    ( k5_relat_1(k2_funct_1(X0),k6_partfun1(k2_relat_1(k2_funct_1(X0)))) = k2_funct_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1210,c_1212])).

cnf(c_7145,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(k2_relat_1(k2_funct_1(sK2)))) = k2_funct_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1201,c_2804])).

cnf(c_20,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_481,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_35])).

cnf(c_482,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_481])).

cnf(c_484,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_482,c_41])).

cnf(c_1195,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_484])).

cnf(c_3078,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_3071,c_1195])).

cnf(c_7149,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(k1_relat_1(sK2))) = k2_funct_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7145,c_3078])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1215,plain,
    ( k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,X0))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3548,plain,
    ( k5_relat_1(k4_relat_1(sK3),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,sK3))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3063,c_1215])).

cnf(c_5307,plain,
    ( k5_relat_1(k4_relat_1(sK3),k4_relat_1(sK2)) = k4_relat_1(k5_relat_1(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_3071,c_3548])).

cnf(c_5309,plain,
    ( k5_relat_1(k4_relat_1(sK3),k4_relat_1(sK2)) = k4_relat_1(k6_partfun1(sK0)) ),
    inference(light_normalisation,[status(thm)],[c_5307,c_5298])).

cnf(c_15,plain,
    ( k4_relat_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_5310,plain,
    ( k5_relat_1(k4_relat_1(sK3),k4_relat_1(sK2)) = k6_partfun1(sK0) ),
    inference(demodulation,[status(thm)],[c_5309,c_15])).

cnf(c_10,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1216,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_5448,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1(sK0)),k2_relat_1(k4_relat_1(sK2))) = iProver_top
    | v1_relat_1(k4_relat_1(sK3)) != iProver_top
    | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5310,c_1216])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1218,plain,
    ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3076,plain,
    ( k2_relat_1(k4_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_3071,c_1218])).

cnf(c_5449,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1(sK0)),k1_relat_1(sK2)) = iProver_top
    | v1_relat_1(k4_relat_1(sK3)) != iProver_top
    | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5448,c_3076])).

cnf(c_13,plain,
    ( k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_5450,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top
    | v1_relat_1(k4_relat_1(sK3)) != iProver_top
    | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5449,c_13])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k4_relat_1(X0)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1812,plain,
    ( v1_relat_1(k4_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1835,plain,
    ( v1_relat_1(k4_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1812])).

cnf(c_2522,plain,
    ( v1_relat_1(k4_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2547,plain,
    ( v1_relat_1(k4_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2522])).

cnf(c_5595,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5450,c_43,c_45,c_1515,c_1545,c_1835,c_2157,c_2237,c_2547])).

cnf(c_1927,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1202,c_1200])).

cnf(c_2503,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1927,c_43,c_1515,c_1545])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1223,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2991,plain,
    ( k1_relat_1(sK2) = sK0
    | r1_tarski(sK0,k1_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2503,c_1223])).

cnf(c_5601,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(superposition,[status(thm)],[c_5595,c_2991])).

cnf(c_7150,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k2_funct_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7149,c_5601])).

cnf(c_15086,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7150,c_43,c_1515,c_1545])).

cnf(c_22050,plain,
    ( k2_funct_1(sK2) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_22042,c_4265,c_5298,c_15086])).

cnf(c_32,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f103])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_22050,c_32])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:06:17 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.73/1.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.73/1.48  
% 7.73/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.73/1.48  
% 7.73/1.48  ------  iProver source info
% 7.73/1.48  
% 7.73/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.73/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.73/1.48  git: non_committed_changes: false
% 7.73/1.48  git: last_make_outside_of_git: false
% 7.73/1.48  
% 7.73/1.48  ------ 
% 7.73/1.48  
% 7.73/1.48  ------ Input Options
% 7.73/1.48  
% 7.73/1.48  --out_options                           all
% 7.73/1.48  --tptp_safe_out                         true
% 7.73/1.48  --problem_path                          ""
% 7.73/1.48  --include_path                          ""
% 7.73/1.48  --clausifier                            res/vclausify_rel
% 7.73/1.48  --clausifier_options                    ""
% 7.73/1.48  --stdin                                 false
% 7.73/1.48  --stats_out                             all
% 7.73/1.48  
% 7.73/1.48  ------ General Options
% 7.73/1.48  
% 7.73/1.48  --fof                                   false
% 7.73/1.48  --time_out_real                         305.
% 7.73/1.48  --time_out_virtual                      -1.
% 7.73/1.48  --symbol_type_check                     false
% 7.73/1.48  --clausify_out                          false
% 7.73/1.48  --sig_cnt_out                           false
% 7.73/1.48  --trig_cnt_out                          false
% 7.73/1.48  --trig_cnt_out_tolerance                1.
% 7.73/1.48  --trig_cnt_out_sk_spl                   false
% 7.73/1.48  --abstr_cl_out                          false
% 7.73/1.48  
% 7.73/1.48  ------ Global Options
% 7.73/1.48  
% 7.73/1.48  --schedule                              default
% 7.73/1.48  --add_important_lit                     false
% 7.73/1.48  --prop_solver_per_cl                    1000
% 7.73/1.48  --min_unsat_core                        false
% 7.73/1.48  --soft_assumptions                      false
% 7.73/1.48  --soft_lemma_size                       3
% 7.73/1.48  --prop_impl_unit_size                   0
% 7.73/1.48  --prop_impl_unit                        []
% 7.73/1.48  --share_sel_clauses                     true
% 7.73/1.48  --reset_solvers                         false
% 7.73/1.48  --bc_imp_inh                            [conj_cone]
% 7.73/1.48  --conj_cone_tolerance                   3.
% 7.73/1.48  --extra_neg_conj                        none
% 7.73/1.48  --large_theory_mode                     true
% 7.73/1.48  --prolific_symb_bound                   200
% 7.73/1.48  --lt_threshold                          2000
% 7.73/1.48  --clause_weak_htbl                      true
% 7.73/1.48  --gc_record_bc_elim                     false
% 7.73/1.48  
% 7.73/1.48  ------ Preprocessing Options
% 7.73/1.48  
% 7.73/1.48  --preprocessing_flag                    true
% 7.73/1.48  --time_out_prep_mult                    0.1
% 7.73/1.48  --splitting_mode                        input
% 7.73/1.48  --splitting_grd                         true
% 7.73/1.48  --splitting_cvd                         false
% 7.73/1.48  --splitting_cvd_svl                     false
% 7.73/1.48  --splitting_nvd                         32
% 7.73/1.48  --sub_typing                            true
% 7.73/1.48  --prep_gs_sim                           true
% 7.73/1.48  --prep_unflatten                        true
% 7.73/1.48  --prep_res_sim                          true
% 7.73/1.48  --prep_upred                            true
% 7.73/1.48  --prep_sem_filter                       exhaustive
% 7.73/1.48  --prep_sem_filter_out                   false
% 7.73/1.48  --pred_elim                             true
% 7.73/1.48  --res_sim_input                         true
% 7.73/1.48  --eq_ax_congr_red                       true
% 7.73/1.48  --pure_diseq_elim                       true
% 7.73/1.48  --brand_transform                       false
% 7.73/1.48  --non_eq_to_eq                          false
% 7.73/1.48  --prep_def_merge                        true
% 7.73/1.48  --prep_def_merge_prop_impl              false
% 7.73/1.48  --prep_def_merge_mbd                    true
% 7.73/1.48  --prep_def_merge_tr_red                 false
% 7.73/1.48  --prep_def_merge_tr_cl                  false
% 7.73/1.48  --smt_preprocessing                     true
% 7.73/1.48  --smt_ac_axioms                         fast
% 7.73/1.48  --preprocessed_out                      false
% 7.73/1.48  --preprocessed_stats                    false
% 7.73/1.48  
% 7.73/1.48  ------ Abstraction refinement Options
% 7.73/1.48  
% 7.73/1.48  --abstr_ref                             []
% 7.73/1.48  --abstr_ref_prep                        false
% 7.73/1.48  --abstr_ref_until_sat                   false
% 7.73/1.48  --abstr_ref_sig_restrict                funpre
% 7.73/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.73/1.48  --abstr_ref_under                       []
% 7.73/1.48  
% 7.73/1.48  ------ SAT Options
% 7.73/1.48  
% 7.73/1.48  --sat_mode                              false
% 7.73/1.48  --sat_fm_restart_options                ""
% 7.73/1.48  --sat_gr_def                            false
% 7.73/1.48  --sat_epr_types                         true
% 7.73/1.48  --sat_non_cyclic_types                  false
% 7.73/1.48  --sat_finite_models                     false
% 7.73/1.48  --sat_fm_lemmas                         false
% 7.73/1.48  --sat_fm_prep                           false
% 7.73/1.48  --sat_fm_uc_incr                        true
% 7.73/1.48  --sat_out_model                         small
% 7.73/1.48  --sat_out_clauses                       false
% 7.73/1.48  
% 7.73/1.48  ------ QBF Options
% 7.73/1.48  
% 7.73/1.48  --qbf_mode                              false
% 7.73/1.48  --qbf_elim_univ                         false
% 7.73/1.48  --qbf_dom_inst                          none
% 7.73/1.48  --qbf_dom_pre_inst                      false
% 7.73/1.48  --qbf_sk_in                             false
% 7.73/1.48  --qbf_pred_elim                         true
% 7.73/1.48  --qbf_split                             512
% 7.73/1.48  
% 7.73/1.48  ------ BMC1 Options
% 7.73/1.48  
% 7.73/1.48  --bmc1_incremental                      false
% 7.73/1.48  --bmc1_axioms                           reachable_all
% 7.73/1.48  --bmc1_min_bound                        0
% 7.73/1.48  --bmc1_max_bound                        -1
% 7.73/1.48  --bmc1_max_bound_default                -1
% 7.73/1.48  --bmc1_symbol_reachability              true
% 7.73/1.48  --bmc1_property_lemmas                  false
% 7.73/1.48  --bmc1_k_induction                      false
% 7.73/1.48  --bmc1_non_equiv_states                 false
% 7.73/1.48  --bmc1_deadlock                         false
% 7.73/1.48  --bmc1_ucm                              false
% 7.73/1.48  --bmc1_add_unsat_core                   none
% 7.73/1.48  --bmc1_unsat_core_children              false
% 7.73/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.73/1.48  --bmc1_out_stat                         full
% 7.73/1.48  --bmc1_ground_init                      false
% 7.73/1.48  --bmc1_pre_inst_next_state              false
% 7.73/1.48  --bmc1_pre_inst_state                   false
% 7.73/1.48  --bmc1_pre_inst_reach_state             false
% 7.73/1.48  --bmc1_out_unsat_core                   false
% 7.73/1.48  --bmc1_aig_witness_out                  false
% 7.73/1.48  --bmc1_verbose                          false
% 7.73/1.48  --bmc1_dump_clauses_tptp                false
% 7.73/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.73/1.48  --bmc1_dump_file                        -
% 7.73/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.73/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.73/1.48  --bmc1_ucm_extend_mode                  1
% 7.73/1.48  --bmc1_ucm_init_mode                    2
% 7.73/1.48  --bmc1_ucm_cone_mode                    none
% 7.73/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.73/1.48  --bmc1_ucm_relax_model                  4
% 7.73/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.73/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.73/1.48  --bmc1_ucm_layered_model                none
% 7.73/1.48  --bmc1_ucm_max_lemma_size               10
% 7.73/1.48  
% 7.73/1.48  ------ AIG Options
% 7.73/1.48  
% 7.73/1.48  --aig_mode                              false
% 7.73/1.48  
% 7.73/1.48  ------ Instantiation Options
% 7.73/1.48  
% 7.73/1.48  --instantiation_flag                    true
% 7.73/1.48  --inst_sos_flag                         true
% 7.73/1.48  --inst_sos_phase                        true
% 7.73/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.73/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.73/1.48  --inst_lit_sel_side                     num_symb
% 7.73/1.48  --inst_solver_per_active                1400
% 7.73/1.48  --inst_solver_calls_frac                1.
% 7.73/1.48  --inst_passive_queue_type               priority_queues
% 7.73/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.73/1.48  --inst_passive_queues_freq              [25;2]
% 7.73/1.48  --inst_dismatching                      true
% 7.73/1.48  --inst_eager_unprocessed_to_passive     true
% 7.73/1.48  --inst_prop_sim_given                   true
% 7.73/1.48  --inst_prop_sim_new                     false
% 7.73/1.48  --inst_subs_new                         false
% 7.73/1.48  --inst_eq_res_simp                      false
% 7.73/1.48  --inst_subs_given                       false
% 7.73/1.48  --inst_orphan_elimination               true
% 7.73/1.48  --inst_learning_loop_flag               true
% 7.73/1.48  --inst_learning_start                   3000
% 7.73/1.48  --inst_learning_factor                  2
% 7.73/1.48  --inst_start_prop_sim_after_learn       3
% 7.73/1.48  --inst_sel_renew                        solver
% 7.73/1.48  --inst_lit_activity_flag                true
% 7.73/1.48  --inst_restr_to_given                   false
% 7.73/1.48  --inst_activity_threshold               500
% 7.73/1.48  --inst_out_proof                        true
% 7.73/1.48  
% 7.73/1.48  ------ Resolution Options
% 7.73/1.48  
% 7.73/1.48  --resolution_flag                       true
% 7.73/1.48  --res_lit_sel                           adaptive
% 7.73/1.48  --res_lit_sel_side                      none
% 7.73/1.48  --res_ordering                          kbo
% 7.73/1.48  --res_to_prop_solver                    active
% 7.73/1.48  --res_prop_simpl_new                    false
% 7.73/1.48  --res_prop_simpl_given                  true
% 7.73/1.48  --res_passive_queue_type                priority_queues
% 7.73/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.73/1.48  --res_passive_queues_freq               [15;5]
% 7.73/1.48  --res_forward_subs                      full
% 7.73/1.48  --res_backward_subs                     full
% 7.73/1.48  --res_forward_subs_resolution           true
% 7.73/1.48  --res_backward_subs_resolution          true
% 7.73/1.48  --res_orphan_elimination                true
% 7.73/1.48  --res_time_limit                        2.
% 7.73/1.48  --res_out_proof                         true
% 7.73/1.48  
% 7.73/1.48  ------ Superposition Options
% 7.73/1.48  
% 7.73/1.48  --superposition_flag                    true
% 7.73/1.48  --sup_passive_queue_type                priority_queues
% 7.73/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.73/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.73/1.48  --demod_completeness_check              fast
% 7.73/1.48  --demod_use_ground                      true
% 7.73/1.48  --sup_to_prop_solver                    passive
% 7.73/1.48  --sup_prop_simpl_new                    true
% 7.73/1.48  --sup_prop_simpl_given                  true
% 7.73/1.48  --sup_fun_splitting                     true
% 7.73/1.48  --sup_smt_interval                      50000
% 7.73/1.48  
% 7.73/1.48  ------ Superposition Simplification Setup
% 7.73/1.48  
% 7.73/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.73/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.73/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.73/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.73/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.73/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.73/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.73/1.48  --sup_immed_triv                        [TrivRules]
% 7.73/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.73/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.73/1.48  --sup_immed_bw_main                     []
% 7.73/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.73/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.73/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.73/1.48  --sup_input_bw                          []
% 7.73/1.48  
% 7.73/1.48  ------ Combination Options
% 7.73/1.48  
% 7.73/1.48  --comb_res_mult                         3
% 7.73/1.48  --comb_sup_mult                         2
% 7.73/1.48  --comb_inst_mult                        10
% 7.73/1.48  
% 7.73/1.48  ------ Debug Options
% 7.73/1.48  
% 7.73/1.48  --dbg_backtrace                         false
% 7.73/1.48  --dbg_dump_prop_clauses                 false
% 7.73/1.48  --dbg_dump_prop_clauses_file            -
% 7.73/1.48  --dbg_out_stat                          false
% 7.73/1.48  ------ Parsing...
% 7.73/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.73/1.48  
% 7.73/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.73/1.48  
% 7.73/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.73/1.48  
% 7.73/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.73/1.48  ------ Proving...
% 7.73/1.48  ------ Problem Properties 
% 7.73/1.48  
% 7.73/1.48  
% 7.73/1.48  clauses                                 36
% 7.73/1.48  conjectures                             8
% 7.73/1.48  EPR                                     6
% 7.73/1.48  Horn                                    36
% 7.73/1.48  unary                                   14
% 7.73/1.48  binary                                  10
% 7.73/1.48  lits                                    77
% 7.73/1.48  lits eq                                 21
% 7.73/1.48  fd_pure                                 0
% 7.73/1.48  fd_pseudo                               0
% 7.73/1.48  fd_cond                                 0
% 7.73/1.48  fd_pseudo_cond                          1
% 7.73/1.48  AC symbols                              0
% 7.73/1.48  
% 7.73/1.48  ------ Schedule dynamic 5 is on 
% 7.73/1.48  
% 7.73/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.73/1.48  
% 7.73/1.48  
% 7.73/1.48  ------ 
% 7.73/1.48  Current options:
% 7.73/1.48  ------ 
% 7.73/1.48  
% 7.73/1.48  ------ Input Options
% 7.73/1.48  
% 7.73/1.48  --out_options                           all
% 7.73/1.48  --tptp_safe_out                         true
% 7.73/1.48  --problem_path                          ""
% 7.73/1.48  --include_path                          ""
% 7.73/1.48  --clausifier                            res/vclausify_rel
% 7.73/1.48  --clausifier_options                    ""
% 7.73/1.48  --stdin                                 false
% 7.73/1.48  --stats_out                             all
% 7.73/1.48  
% 7.73/1.48  ------ General Options
% 7.73/1.48  
% 7.73/1.48  --fof                                   false
% 7.73/1.48  --time_out_real                         305.
% 7.73/1.48  --time_out_virtual                      -1.
% 7.73/1.48  --symbol_type_check                     false
% 7.73/1.48  --clausify_out                          false
% 7.73/1.48  --sig_cnt_out                           false
% 7.73/1.48  --trig_cnt_out                          false
% 7.73/1.48  --trig_cnt_out_tolerance                1.
% 7.73/1.48  --trig_cnt_out_sk_spl                   false
% 7.73/1.48  --abstr_cl_out                          false
% 7.73/1.48  
% 7.73/1.48  ------ Global Options
% 7.73/1.48  
% 7.73/1.48  --schedule                              default
% 7.73/1.48  --add_important_lit                     false
% 7.73/1.48  --prop_solver_per_cl                    1000
% 7.73/1.48  --min_unsat_core                        false
% 7.73/1.48  --soft_assumptions                      false
% 7.73/1.48  --soft_lemma_size                       3
% 7.73/1.48  --prop_impl_unit_size                   0
% 7.73/1.48  --prop_impl_unit                        []
% 7.73/1.48  --share_sel_clauses                     true
% 7.73/1.48  --reset_solvers                         false
% 7.73/1.48  --bc_imp_inh                            [conj_cone]
% 7.73/1.48  --conj_cone_tolerance                   3.
% 7.73/1.48  --extra_neg_conj                        none
% 7.73/1.48  --large_theory_mode                     true
% 7.73/1.48  --prolific_symb_bound                   200
% 7.73/1.48  --lt_threshold                          2000
% 7.73/1.48  --clause_weak_htbl                      true
% 7.73/1.48  --gc_record_bc_elim                     false
% 7.73/1.48  
% 7.73/1.48  ------ Preprocessing Options
% 7.73/1.48  
% 7.73/1.48  --preprocessing_flag                    true
% 7.73/1.48  --time_out_prep_mult                    0.1
% 7.73/1.48  --splitting_mode                        input
% 7.73/1.48  --splitting_grd                         true
% 7.73/1.48  --splitting_cvd                         false
% 7.73/1.48  --splitting_cvd_svl                     false
% 7.73/1.48  --splitting_nvd                         32
% 7.73/1.48  --sub_typing                            true
% 7.73/1.48  --prep_gs_sim                           true
% 7.73/1.48  --prep_unflatten                        true
% 7.73/1.48  --prep_res_sim                          true
% 7.73/1.48  --prep_upred                            true
% 7.73/1.48  --prep_sem_filter                       exhaustive
% 7.73/1.48  --prep_sem_filter_out                   false
% 7.73/1.48  --pred_elim                             true
% 7.73/1.48  --res_sim_input                         true
% 7.73/1.48  --eq_ax_congr_red                       true
% 7.73/1.48  --pure_diseq_elim                       true
% 7.73/1.48  --brand_transform                       false
% 7.73/1.48  --non_eq_to_eq                          false
% 7.73/1.48  --prep_def_merge                        true
% 7.73/1.48  --prep_def_merge_prop_impl              false
% 7.73/1.48  --prep_def_merge_mbd                    true
% 7.73/1.48  --prep_def_merge_tr_red                 false
% 7.73/1.48  --prep_def_merge_tr_cl                  false
% 7.73/1.48  --smt_preprocessing                     true
% 7.73/1.48  --smt_ac_axioms                         fast
% 7.73/1.48  --preprocessed_out                      false
% 7.73/1.48  --preprocessed_stats                    false
% 7.73/1.48  
% 7.73/1.48  ------ Abstraction refinement Options
% 7.73/1.48  
% 7.73/1.48  --abstr_ref                             []
% 7.73/1.48  --abstr_ref_prep                        false
% 7.73/1.48  --abstr_ref_until_sat                   false
% 7.73/1.48  --abstr_ref_sig_restrict                funpre
% 7.73/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.73/1.48  --abstr_ref_under                       []
% 7.73/1.48  
% 7.73/1.48  ------ SAT Options
% 7.73/1.48  
% 7.73/1.48  --sat_mode                              false
% 7.73/1.48  --sat_fm_restart_options                ""
% 7.73/1.48  --sat_gr_def                            false
% 7.73/1.48  --sat_epr_types                         true
% 7.73/1.48  --sat_non_cyclic_types                  false
% 7.73/1.48  --sat_finite_models                     false
% 7.73/1.48  --sat_fm_lemmas                         false
% 7.73/1.48  --sat_fm_prep                           false
% 7.73/1.48  --sat_fm_uc_incr                        true
% 7.73/1.48  --sat_out_model                         small
% 7.73/1.48  --sat_out_clauses                       false
% 7.73/1.48  
% 7.73/1.48  ------ QBF Options
% 7.73/1.48  
% 7.73/1.48  --qbf_mode                              false
% 7.73/1.48  --qbf_elim_univ                         false
% 7.73/1.48  --qbf_dom_inst                          none
% 7.73/1.48  --qbf_dom_pre_inst                      false
% 7.73/1.48  --qbf_sk_in                             false
% 7.73/1.48  --qbf_pred_elim                         true
% 7.73/1.48  --qbf_split                             512
% 7.73/1.48  
% 7.73/1.48  ------ BMC1 Options
% 7.73/1.48  
% 7.73/1.48  --bmc1_incremental                      false
% 7.73/1.48  --bmc1_axioms                           reachable_all
% 7.73/1.48  --bmc1_min_bound                        0
% 7.73/1.48  --bmc1_max_bound                        -1
% 7.73/1.48  --bmc1_max_bound_default                -1
% 7.73/1.48  --bmc1_symbol_reachability              true
% 7.73/1.48  --bmc1_property_lemmas                  false
% 7.73/1.48  --bmc1_k_induction                      false
% 7.73/1.48  --bmc1_non_equiv_states                 false
% 7.73/1.48  --bmc1_deadlock                         false
% 7.73/1.48  --bmc1_ucm                              false
% 7.73/1.48  --bmc1_add_unsat_core                   none
% 7.73/1.48  --bmc1_unsat_core_children              false
% 7.73/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.73/1.48  --bmc1_out_stat                         full
% 7.73/1.48  --bmc1_ground_init                      false
% 7.73/1.48  --bmc1_pre_inst_next_state              false
% 7.73/1.48  --bmc1_pre_inst_state                   false
% 7.73/1.48  --bmc1_pre_inst_reach_state             false
% 7.73/1.48  --bmc1_out_unsat_core                   false
% 7.73/1.48  --bmc1_aig_witness_out                  false
% 7.73/1.48  --bmc1_verbose                          false
% 7.73/1.48  --bmc1_dump_clauses_tptp                false
% 7.73/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.73/1.48  --bmc1_dump_file                        -
% 7.73/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.73/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.73/1.48  --bmc1_ucm_extend_mode                  1
% 7.73/1.48  --bmc1_ucm_init_mode                    2
% 7.73/1.48  --bmc1_ucm_cone_mode                    none
% 7.73/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.73/1.48  --bmc1_ucm_relax_model                  4
% 7.73/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.73/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.73/1.48  --bmc1_ucm_layered_model                none
% 7.73/1.48  --bmc1_ucm_max_lemma_size               10
% 7.73/1.48  
% 7.73/1.48  ------ AIG Options
% 7.73/1.48  
% 7.73/1.48  --aig_mode                              false
% 7.73/1.48  
% 7.73/1.48  ------ Instantiation Options
% 7.73/1.48  
% 7.73/1.48  --instantiation_flag                    true
% 7.73/1.48  --inst_sos_flag                         true
% 7.73/1.48  --inst_sos_phase                        true
% 7.73/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.73/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.73/1.48  --inst_lit_sel_side                     none
% 7.73/1.48  --inst_solver_per_active                1400
% 7.73/1.48  --inst_solver_calls_frac                1.
% 7.73/1.48  --inst_passive_queue_type               priority_queues
% 7.73/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.73/1.48  --inst_passive_queues_freq              [25;2]
% 7.73/1.48  --inst_dismatching                      true
% 7.73/1.48  --inst_eager_unprocessed_to_passive     true
% 7.73/1.48  --inst_prop_sim_given                   true
% 7.73/1.48  --inst_prop_sim_new                     false
% 7.73/1.48  --inst_subs_new                         false
% 7.73/1.48  --inst_eq_res_simp                      false
% 7.73/1.48  --inst_subs_given                       false
% 7.73/1.48  --inst_orphan_elimination               true
% 7.73/1.48  --inst_learning_loop_flag               true
% 7.73/1.48  --inst_learning_start                   3000
% 7.73/1.48  --inst_learning_factor                  2
% 7.73/1.48  --inst_start_prop_sim_after_learn       3
% 7.73/1.48  --inst_sel_renew                        solver
% 7.73/1.48  --inst_lit_activity_flag                true
% 7.73/1.48  --inst_restr_to_given                   false
% 7.73/1.48  --inst_activity_threshold               500
% 7.73/1.48  --inst_out_proof                        true
% 7.73/1.48  
% 7.73/1.48  ------ Resolution Options
% 7.73/1.48  
% 7.73/1.48  --resolution_flag                       false
% 7.73/1.48  --res_lit_sel                           adaptive
% 7.73/1.48  --res_lit_sel_side                      none
% 7.73/1.48  --res_ordering                          kbo
% 7.73/1.48  --res_to_prop_solver                    active
% 7.73/1.48  --res_prop_simpl_new                    false
% 7.73/1.48  --res_prop_simpl_given                  true
% 7.73/1.48  --res_passive_queue_type                priority_queues
% 7.73/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.73/1.48  --res_passive_queues_freq               [15;5]
% 7.73/1.48  --res_forward_subs                      full
% 7.73/1.48  --res_backward_subs                     full
% 7.73/1.48  --res_forward_subs_resolution           true
% 7.73/1.48  --res_backward_subs_resolution          true
% 7.73/1.48  --res_orphan_elimination                true
% 7.73/1.48  --res_time_limit                        2.
% 7.73/1.48  --res_out_proof                         true
% 7.73/1.48  
% 7.73/1.48  ------ Superposition Options
% 7.73/1.48  
% 7.73/1.48  --superposition_flag                    true
% 7.73/1.48  --sup_passive_queue_type                priority_queues
% 7.73/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.73/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.73/1.48  --demod_completeness_check              fast
% 7.73/1.48  --demod_use_ground                      true
% 7.73/1.48  --sup_to_prop_solver                    passive
% 7.73/1.48  --sup_prop_simpl_new                    true
% 7.73/1.48  --sup_prop_simpl_given                  true
% 7.73/1.48  --sup_fun_splitting                     true
% 7.73/1.48  --sup_smt_interval                      50000
% 7.73/1.48  
% 7.73/1.48  ------ Superposition Simplification Setup
% 7.73/1.48  
% 7.73/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.73/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.73/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.73/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.73/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.73/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.73/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.73/1.48  --sup_immed_triv                        [TrivRules]
% 7.73/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.73/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.73/1.48  --sup_immed_bw_main                     []
% 7.73/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.73/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.73/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.73/1.48  --sup_input_bw                          []
% 7.73/1.48  
% 7.73/1.48  ------ Combination Options
% 7.73/1.48  
% 7.73/1.48  --comb_res_mult                         3
% 7.73/1.48  --comb_sup_mult                         2
% 7.73/1.48  --comb_inst_mult                        10
% 7.73/1.48  
% 7.73/1.48  ------ Debug Options
% 7.73/1.48  
% 7.73/1.48  --dbg_backtrace                         false
% 7.73/1.48  --dbg_dump_prop_clauses                 false
% 7.73/1.48  --dbg_dump_prop_clauses_file            -
% 7.73/1.48  --dbg_out_stat                          false
% 7.73/1.48  
% 7.73/1.48  
% 7.73/1.48  
% 7.73/1.48  
% 7.73/1.48  ------ Proving...
% 7.73/1.48  
% 7.73/1.48  
% 7.73/1.48  % SZS status Theorem for theBenchmark.p
% 7.73/1.48  
% 7.73/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.73/1.48  
% 7.73/1.48  fof(f24,conjecture,(
% 7.73/1.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 7.73/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.48  
% 7.73/1.48  fof(f25,negated_conjecture,(
% 7.73/1.48    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 7.73/1.48    inference(negated_conjecture,[],[f24])).
% 7.73/1.48  
% 7.73/1.48  fof(f26,plain,(
% 7.73/1.48    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 7.73/1.48    inference(pure_predicate_removal,[],[f25])).
% 7.73/1.48  
% 7.73/1.48  fof(f52,plain,(
% 7.73/1.48    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 7.73/1.48    inference(ennf_transformation,[],[f26])).
% 7.73/1.48  
% 7.73/1.48  fof(f53,plain,(
% 7.73/1.48    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 7.73/1.48    inference(flattening,[],[f52])).
% 7.73/1.48  
% 7.73/1.48  fof(f59,plain,(
% 7.73/1.48    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(sK3))) )),
% 7.73/1.48    introduced(choice_axiom,[])).
% 7.73/1.48  
% 7.73/1.48  fof(f58,plain,(
% 7.73/1.48    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2))),
% 7.73/1.48    introduced(choice_axiom,[])).
% 7.73/1.48  
% 7.73/1.48  fof(f60,plain,(
% 7.73/1.48    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2)),
% 7.73/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f53,f59,f58])).
% 7.73/1.48  
% 7.73/1.48  fof(f97,plain,(
% 7.73/1.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 7.73/1.48    inference(cnf_transformation,[],[f60])).
% 7.73/1.48  
% 7.73/1.48  fof(f2,axiom,(
% 7.73/1.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 7.73/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.48  
% 7.73/1.48  fof(f28,plain,(
% 7.73/1.48    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 7.73/1.48    inference(ennf_transformation,[],[f2])).
% 7.73/1.48  
% 7.73/1.48  fof(f64,plain,(
% 7.73/1.48    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 7.73/1.48    inference(cnf_transformation,[],[f28])).
% 7.73/1.48  
% 7.73/1.48  fof(f5,axiom,(
% 7.73/1.48    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 7.73/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.48  
% 7.73/1.48  fof(f68,plain,(
% 7.73/1.48    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 7.73/1.48    inference(cnf_transformation,[],[f5])).
% 7.73/1.48  
% 7.73/1.48  fof(f95,plain,(
% 7.73/1.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 7.73/1.48    inference(cnf_transformation,[],[f60])).
% 7.73/1.48  
% 7.73/1.48  fof(f94,plain,(
% 7.73/1.48    v1_funct_1(sK2)),
% 7.73/1.48    inference(cnf_transformation,[],[f60])).
% 7.73/1.48  
% 7.73/1.48  fof(f14,axiom,(
% 7.73/1.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 7.73/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.48  
% 7.73/1.48  fof(f38,plain,(
% 7.73/1.48    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.73/1.48    inference(ennf_transformation,[],[f14])).
% 7.73/1.48  
% 7.73/1.48  fof(f39,plain,(
% 7.73/1.48    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.73/1.48    inference(flattening,[],[f38])).
% 7.73/1.48  
% 7.73/1.48  fof(f79,plain,(
% 7.73/1.48    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.73/1.48    inference(cnf_transformation,[],[f39])).
% 7.73/1.48  
% 7.73/1.48  fof(f9,axiom,(
% 7.73/1.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2))))),
% 7.73/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.48  
% 7.73/1.48  fof(f34,plain,(
% 7.73/1.48    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.73/1.48    inference(ennf_transformation,[],[f9])).
% 7.73/1.48  
% 7.73/1.48  fof(f73,plain,(
% 7.73/1.48    ( ! [X2,X0,X1] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.73/1.48    inference(cnf_transformation,[],[f34])).
% 7.73/1.48  
% 7.73/1.48  fof(f18,axiom,(
% 7.73/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 7.73/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.48  
% 7.73/1.48  fof(f45,plain,(
% 7.73/1.48    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.73/1.48    inference(ennf_transformation,[],[f18])).
% 7.73/1.48  
% 7.73/1.48  fof(f86,plain,(
% 7.73/1.48    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.73/1.48    inference(cnf_transformation,[],[f45])).
% 7.73/1.48  
% 7.73/1.48  fof(f98,plain,(
% 7.73/1.48    k2_relset_1(sK0,sK1,sK2) = sK1),
% 7.73/1.48    inference(cnf_transformation,[],[f60])).
% 7.73/1.48  
% 7.73/1.48  fof(f16,axiom,(
% 7.73/1.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 7.73/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.48  
% 7.73/1.48  fof(f42,plain,(
% 7.73/1.48    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.73/1.48    inference(ennf_transformation,[],[f16])).
% 7.73/1.48  
% 7.73/1.48  fof(f43,plain,(
% 7.73/1.48    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.73/1.48    inference(flattening,[],[f42])).
% 7.73/1.48  
% 7.73/1.48  fof(f84,plain,(
% 7.73/1.48    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.73/1.48    inference(cnf_transformation,[],[f43])).
% 7.73/1.48  
% 7.73/1.48  fof(f23,axiom,(
% 7.73/1.48    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 7.73/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.48  
% 7.73/1.48  fof(f93,plain,(
% 7.73/1.48    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 7.73/1.48    inference(cnf_transformation,[],[f23])).
% 7.73/1.48  
% 7.73/1.48  fof(f109,plain,(
% 7.73/1.48    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.73/1.48    inference(definition_unfolding,[],[f84,f93])).
% 7.73/1.48  
% 7.73/1.48  fof(f100,plain,(
% 7.73/1.48    v2_funct_1(sK2)),
% 7.73/1.48    inference(cnf_transformation,[],[f60])).
% 7.73/1.48  
% 7.73/1.48  fof(f17,axiom,(
% 7.73/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.73/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.48  
% 7.73/1.48  fof(f27,plain,(
% 7.73/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 7.73/1.48    inference(pure_predicate_removal,[],[f17])).
% 7.73/1.48  
% 7.73/1.48  fof(f44,plain,(
% 7.73/1.48    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.73/1.48    inference(ennf_transformation,[],[f27])).
% 7.73/1.48  
% 7.73/1.48  fof(f85,plain,(
% 7.73/1.48    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.73/1.48    inference(cnf_transformation,[],[f44])).
% 7.73/1.48  
% 7.73/1.48  fof(f3,axiom,(
% 7.73/1.48    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 7.73/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.48  
% 7.73/1.48  fof(f29,plain,(
% 7.73/1.48    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.73/1.48    inference(ennf_transformation,[],[f3])).
% 7.73/1.48  
% 7.73/1.48  fof(f56,plain,(
% 7.73/1.48    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.73/1.48    inference(nnf_transformation,[],[f29])).
% 7.73/1.48  
% 7.73/1.48  fof(f65,plain,(
% 7.73/1.48    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.73/1.48    inference(cnf_transformation,[],[f56])).
% 7.73/1.48  
% 7.73/1.48  fof(f12,axiom,(
% 7.73/1.48    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 7.73/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.48  
% 7.73/1.48  fof(f35,plain,(
% 7.73/1.48    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.73/1.48    inference(ennf_transformation,[],[f12])).
% 7.73/1.48  
% 7.73/1.48  fof(f36,plain,(
% 7.73/1.48    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 7.73/1.48    inference(flattening,[],[f35])).
% 7.73/1.48  
% 7.73/1.48  fof(f77,plain,(
% 7.73/1.48    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 7.73/1.48    inference(cnf_transformation,[],[f36])).
% 7.73/1.48  
% 7.73/1.48  fof(f107,plain,(
% 7.73/1.48    ( ! [X0,X1] : (k5_relat_1(k6_partfun1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 7.73/1.48    inference(definition_unfolding,[],[f77,f93])).
% 7.73/1.48  
% 7.73/1.48  fof(f22,axiom,(
% 7.73/1.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 7.73/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.48  
% 7.73/1.48  fof(f50,plain,(
% 7.73/1.48    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 7.73/1.48    inference(ennf_transformation,[],[f22])).
% 7.73/1.48  
% 7.73/1.48  fof(f51,plain,(
% 7.73/1.48    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 7.73/1.48    inference(flattening,[],[f50])).
% 7.73/1.48  
% 7.73/1.48  fof(f92,plain,(
% 7.73/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 7.73/1.48    inference(cnf_transformation,[],[f51])).
% 7.73/1.48  
% 7.73/1.48  fof(f96,plain,(
% 7.73/1.48    v1_funct_1(sK3)),
% 7.73/1.48    inference(cnf_transformation,[],[f60])).
% 7.73/1.48  
% 7.73/1.48  fof(f19,axiom,(
% 7.73/1.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 7.73/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.48  
% 7.73/1.48  fof(f46,plain,(
% 7.73/1.48    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 7.73/1.48    inference(ennf_transformation,[],[f19])).
% 7.73/1.48  
% 7.73/1.48  fof(f47,plain,(
% 7.73/1.48    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.73/1.48    inference(flattening,[],[f46])).
% 7.73/1.48  
% 7.73/1.48  fof(f57,plain,(
% 7.73/1.48    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.73/1.48    inference(nnf_transformation,[],[f47])).
% 7.73/1.48  
% 7.73/1.48  fof(f87,plain,(
% 7.73/1.48    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.73/1.48    inference(cnf_transformation,[],[f57])).
% 7.73/1.48  
% 7.73/1.48  fof(f99,plain,(
% 7.73/1.48    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 7.73/1.48    inference(cnf_transformation,[],[f60])).
% 7.73/1.48  
% 7.73/1.48  fof(f20,axiom,(
% 7.73/1.48    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 7.73/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.48  
% 7.73/1.48  fof(f89,plain,(
% 7.73/1.48    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 7.73/1.48    inference(cnf_transformation,[],[f20])).
% 7.73/1.48  
% 7.73/1.48  fof(f111,plain,(
% 7.73/1.48    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 7.73/1.48    inference(definition_unfolding,[],[f89,f93])).
% 7.73/1.48  
% 7.73/1.48  fof(f21,axiom,(
% 7.73/1.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 7.73/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.48  
% 7.73/1.48  fof(f48,plain,(
% 7.73/1.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 7.73/1.48    inference(ennf_transformation,[],[f21])).
% 7.73/1.48  
% 7.73/1.48  fof(f49,plain,(
% 7.73/1.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 7.73/1.48    inference(flattening,[],[f48])).
% 7.73/1.48  
% 7.73/1.48  fof(f91,plain,(
% 7.73/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 7.73/1.48    inference(cnf_transformation,[],[f49])).
% 7.73/1.48  
% 7.73/1.48  fof(f13,axiom,(
% 7.73/1.48    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 7.73/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.48  
% 7.73/1.48  fof(f37,plain,(
% 7.73/1.48    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 7.73/1.48    inference(ennf_transformation,[],[f13])).
% 7.73/1.48  
% 7.73/1.48  fof(f78,plain,(
% 7.73/1.48    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 7.73/1.48    inference(cnf_transformation,[],[f37])).
% 7.73/1.48  
% 7.73/1.48  fof(f108,plain,(
% 7.73/1.48    ( ! [X0] : (k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 7.73/1.48    inference(definition_unfolding,[],[f78,f93])).
% 7.73/1.48  
% 7.73/1.48  fof(f15,axiom,(
% 7.73/1.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 7.73/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.48  
% 7.73/1.48  fof(f40,plain,(
% 7.73/1.48    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.73/1.48    inference(ennf_transformation,[],[f15])).
% 7.73/1.48  
% 7.73/1.48  fof(f41,plain,(
% 7.73/1.48    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.73/1.48    inference(flattening,[],[f40])).
% 7.73/1.48  
% 7.73/1.48  fof(f82,plain,(
% 7.73/1.48    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.73/1.48    inference(cnf_transformation,[],[f41])).
% 7.73/1.48  
% 7.73/1.48  fof(f8,axiom,(
% 7.73/1.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 7.73/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.48  
% 7.73/1.48  fof(f33,plain,(
% 7.73/1.48    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.73/1.48    inference(ennf_transformation,[],[f8])).
% 7.73/1.48  
% 7.73/1.48  fof(f72,plain,(
% 7.73/1.48    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.73/1.48    inference(cnf_transformation,[],[f33])).
% 7.73/1.48  
% 7.73/1.48  fof(f11,axiom,(
% 7.73/1.48    ! [X0] : k4_relat_1(k6_relat_1(X0)) = k6_relat_1(X0)),
% 7.73/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.48  
% 7.73/1.48  fof(f76,plain,(
% 7.73/1.48    ( ! [X0] : (k4_relat_1(k6_relat_1(X0)) = k6_relat_1(X0)) )),
% 7.73/1.48    inference(cnf_transformation,[],[f11])).
% 7.73/1.48  
% 7.73/1.48  fof(f106,plain,(
% 7.73/1.48    ( ! [X0] : (k4_relat_1(k6_partfun1(X0)) = k6_partfun1(X0)) )),
% 7.73/1.48    inference(definition_unfolding,[],[f76,f93,f93])).
% 7.73/1.48  
% 7.73/1.48  fof(f7,axiom,(
% 7.73/1.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 7.73/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.48  
% 7.73/1.48  fof(f32,plain,(
% 7.73/1.48    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.73/1.48    inference(ennf_transformation,[],[f7])).
% 7.73/1.48  
% 7.73/1.48  fof(f71,plain,(
% 7.73/1.48    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.73/1.48    inference(cnf_transformation,[],[f32])).
% 7.73/1.48  
% 7.73/1.48  fof(f6,axiom,(
% 7.73/1.48    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)))),
% 7.73/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.48  
% 7.73/1.48  fof(f31,plain,(
% 7.73/1.48    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 7.73/1.48    inference(ennf_transformation,[],[f6])).
% 7.73/1.48  
% 7.73/1.48  fof(f70,plain,(
% 7.73/1.48    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 7.73/1.48    inference(cnf_transformation,[],[f31])).
% 7.73/1.48  
% 7.73/1.48  fof(f10,axiom,(
% 7.73/1.48    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 7.73/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.48  
% 7.73/1.48  fof(f75,plain,(
% 7.73/1.48    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 7.73/1.48    inference(cnf_transformation,[],[f10])).
% 7.73/1.48  
% 7.73/1.48  fof(f104,plain,(
% 7.73/1.48    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 7.73/1.48    inference(definition_unfolding,[],[f75,f93])).
% 7.73/1.48  
% 7.73/1.48  fof(f4,axiom,(
% 7.73/1.48    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 7.73/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.48  
% 7.73/1.48  fof(f30,plain,(
% 7.73/1.48    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 7.73/1.48    inference(ennf_transformation,[],[f4])).
% 7.73/1.48  
% 7.73/1.48  fof(f67,plain,(
% 7.73/1.48    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 7.73/1.48    inference(cnf_transformation,[],[f30])).
% 7.73/1.48  
% 7.73/1.48  fof(f1,axiom,(
% 7.73/1.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.73/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.48  
% 7.73/1.48  fof(f54,plain,(
% 7.73/1.48    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.73/1.48    inference(nnf_transformation,[],[f1])).
% 7.73/1.48  
% 7.73/1.48  fof(f55,plain,(
% 7.73/1.48    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.73/1.48    inference(flattening,[],[f54])).
% 7.73/1.48  
% 7.73/1.48  fof(f63,plain,(
% 7.73/1.48    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.73/1.48    inference(cnf_transformation,[],[f55])).
% 7.73/1.48  
% 7.73/1.48  fof(f103,plain,(
% 7.73/1.48    k2_funct_1(sK2) != sK3),
% 7.73/1.48    inference(cnf_transformation,[],[f60])).
% 7.73/1.48  
% 7.73/1.48  cnf(c_38,negated_conjecture,
% 7.73/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 7.73/1.48      inference(cnf_transformation,[],[f97]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_1204,plain,
% 7.73/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 7.73/1.48      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_3,plain,
% 7.73/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.73/1.48      | ~ v1_relat_1(X1)
% 7.73/1.48      | v1_relat_1(X0) ),
% 7.73/1.48      inference(cnf_transformation,[],[f64]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_1221,plain,
% 7.73/1.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.73/1.48      | v1_relat_1(X1) != iProver_top
% 7.73/1.48      | v1_relat_1(X0) = iProver_top ),
% 7.73/1.48      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_2996,plain,
% 7.73/1.48      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 7.73/1.48      | v1_relat_1(sK3) = iProver_top ),
% 7.73/1.48      inference(superposition,[status(thm)],[c_1204,c_1221]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_45,plain,
% 7.73/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 7.73/1.48      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_1504,plain,
% 7.73/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.73/1.48      | v1_relat_1(X0)
% 7.73/1.48      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 7.73/1.48      inference(instantiation,[status(thm)],[c_3]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_2156,plain,
% 7.73/1.48      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 7.73/1.48      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
% 7.73/1.48      | v1_relat_1(sK3) ),
% 7.73/1.48      inference(instantiation,[status(thm)],[c_1504]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_2157,plain,
% 7.73/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.73/1.48      | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 7.73/1.48      | v1_relat_1(sK3) = iProver_top ),
% 7.73/1.48      inference(predicate_to_equality,[status(thm)],[c_2156]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_7,plain,
% 7.73/1.48      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 7.73/1.48      inference(cnf_transformation,[],[f68]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_2236,plain,
% 7.73/1.48      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
% 7.73/1.48      inference(instantiation,[status(thm)],[c_7]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_2237,plain,
% 7.73/1.48      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
% 7.73/1.48      inference(predicate_to_equality,[status(thm)],[c_2236]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_3063,plain,
% 7.73/1.48      ( v1_relat_1(sK3) = iProver_top ),
% 7.73/1.48      inference(global_propositional_subsumption,
% 7.73/1.48                [status(thm)],
% 7.73/1.48                [c_2996,c_45,c_2157,c_2237]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_40,negated_conjecture,
% 7.73/1.48      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 7.73/1.48      inference(cnf_transformation,[],[f95]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_1202,plain,
% 7.73/1.48      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.73/1.48      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_2997,plain,
% 7.73/1.48      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 7.73/1.48      | v1_relat_1(sK2) = iProver_top ),
% 7.73/1.48      inference(superposition,[status(thm)],[c_1202,c_1221]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_43,plain,
% 7.73/1.48      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.73/1.48      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_1283,plain,
% 7.73/1.48      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
% 7.73/1.48      | ~ v1_relat_1(X0)
% 7.73/1.48      | v1_relat_1(sK2) ),
% 7.73/1.48      inference(instantiation,[status(thm)],[c_3]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_1342,plain,
% 7.73/1.48      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.73/1.48      | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
% 7.73/1.48      | v1_relat_1(sK2) ),
% 7.73/1.48      inference(instantiation,[status(thm)],[c_1283]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_1514,plain,
% 7.73/1.48      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.73/1.48      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
% 7.73/1.48      | v1_relat_1(sK2) ),
% 7.73/1.48      inference(instantiation,[status(thm)],[c_1342]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_1515,plain,
% 7.73/1.48      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.73/1.48      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 7.73/1.48      | v1_relat_1(sK2) = iProver_top ),
% 7.73/1.48      inference(predicate_to_equality,[status(thm)],[c_1514]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_1544,plain,
% 7.73/1.48      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 7.73/1.48      inference(instantiation,[status(thm)],[c_7]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_1545,plain,
% 7.73/1.48      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 7.73/1.48      inference(predicate_to_equality,[status(thm)],[c_1544]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_3071,plain,
% 7.73/1.48      ( v1_relat_1(sK2) = iProver_top ),
% 7.73/1.48      inference(global_propositional_subsumption,
% 7.73/1.48                [status(thm)],
% 7.73/1.48                [c_2997,c_43,c_1515,c_1545]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_41,negated_conjecture,
% 7.73/1.48      ( v1_funct_1(sK2) ),
% 7.73/1.48      inference(cnf_transformation,[],[f94]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_1201,plain,
% 7.73/1.48      ( v1_funct_1(sK2) = iProver_top ),
% 7.73/1.48      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_19,plain,
% 7.73/1.48      ( ~ v1_funct_1(X0)
% 7.73/1.48      | ~ v1_relat_1(X0)
% 7.73/1.48      | v1_relat_1(k2_funct_1(X0)) ),
% 7.73/1.48      inference(cnf_transformation,[],[f79]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_1210,plain,
% 7.73/1.48      ( v1_funct_1(X0) != iProver_top
% 7.73/1.48      | v1_relat_1(X0) != iProver_top
% 7.73/1.48      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 7.73/1.48      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_12,plain,
% 7.73/1.48      ( ~ v1_relat_1(X0)
% 7.73/1.48      | ~ v1_relat_1(X1)
% 7.73/1.48      | ~ v1_relat_1(X2)
% 7.73/1.48      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ),
% 7.73/1.48      inference(cnf_transformation,[],[f73]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_1214,plain,
% 7.73/1.48      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
% 7.73/1.48      | v1_relat_1(X0) != iProver_top
% 7.73/1.48      | v1_relat_1(X1) != iProver_top
% 7.73/1.48      | v1_relat_1(X2) != iProver_top ),
% 7.73/1.48      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_4587,plain,
% 7.73/1.48      ( k5_relat_1(k2_funct_1(X0),k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(k2_funct_1(X0),X1),X2)
% 7.73/1.48      | v1_funct_1(X0) != iProver_top
% 7.73/1.48      | v1_relat_1(X0) != iProver_top
% 7.73/1.48      | v1_relat_1(X1) != iProver_top
% 7.73/1.48      | v1_relat_1(X2) != iProver_top ),
% 7.73/1.48      inference(superposition,[status(thm)],[c_1210,c_1214]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_21411,plain,
% 7.73/1.48      ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1))
% 7.73/1.48      | v1_relat_1(X0) != iProver_top
% 7.73/1.48      | v1_relat_1(X1) != iProver_top
% 7.73/1.48      | v1_relat_1(sK2) != iProver_top ),
% 7.73/1.48      inference(superposition,[status(thm)],[c_1201,c_4587]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_21894,plain,
% 7.73/1.48      ( v1_relat_1(X1) != iProver_top
% 7.73/1.48      | v1_relat_1(X0) != iProver_top
% 7.73/1.48      | k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1)) ),
% 7.73/1.48      inference(global_propositional_subsumption,
% 7.73/1.48                [status(thm)],
% 7.73/1.48                [c_21411,c_43,c_1515,c_1545]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_21895,plain,
% 7.73/1.48      ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1))
% 7.73/1.48      | v1_relat_1(X0) != iProver_top
% 7.73/1.48      | v1_relat_1(X1) != iProver_top ),
% 7.73/1.48      inference(renaming,[status(thm)],[c_21894]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_21903,plain,
% 7.73/1.48      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),X0)
% 7.73/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.73/1.48      inference(superposition,[status(thm)],[c_3071,c_21895]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_25,plain,
% 7.73/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.73/1.48      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 7.73/1.48      inference(cnf_transformation,[],[f86]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_1209,plain,
% 7.73/1.48      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 7.73/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.73/1.48      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_2136,plain,
% 7.73/1.48      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 7.73/1.48      inference(superposition,[status(thm)],[c_1202,c_1209]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_37,negated_conjecture,
% 7.73/1.48      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 7.73/1.48      inference(cnf_transformation,[],[f98]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_2137,plain,
% 7.73/1.48      ( k2_relat_1(sK2) = sK1 ),
% 7.73/1.48      inference(light_normalisation,[status(thm)],[c_2136,c_37]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_22,plain,
% 7.73/1.48      ( ~ v2_funct_1(X0)
% 7.73/1.48      | ~ v1_funct_1(X0)
% 7.73/1.48      | ~ v1_relat_1(X0)
% 7.73/1.48      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
% 7.73/1.48      inference(cnf_transformation,[],[f109]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_35,negated_conjecture,
% 7.73/1.48      ( v2_funct_1(sK2) ),
% 7.73/1.48      inference(cnf_transformation,[],[f100]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_453,plain,
% 7.73/1.48      ( ~ v1_funct_1(X0)
% 7.73/1.48      | ~ v1_relat_1(X0)
% 7.73/1.48      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
% 7.73/1.48      | sK2 != X0 ),
% 7.73/1.48      inference(resolution_lifted,[status(thm)],[c_22,c_35]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_454,plain,
% 7.73/1.48      ( ~ v1_funct_1(sK2)
% 7.73/1.48      | ~ v1_relat_1(sK2)
% 7.73/1.48      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 7.73/1.48      inference(unflattening,[status(thm)],[c_453]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_456,plain,
% 7.73/1.48      ( ~ v1_relat_1(sK2)
% 7.73/1.48      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 7.73/1.48      inference(global_propositional_subsumption,
% 7.73/1.48                [status(thm)],
% 7.73/1.48                [c_454,c_41]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_1197,plain,
% 7.73/1.48      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
% 7.73/1.48      | v1_relat_1(sK2) != iProver_top ),
% 7.73/1.48      inference(predicate_to_equality,[status(thm)],[c_456]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_1659,plain,
% 7.73/1.48      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 7.73/1.48      inference(global_propositional_subsumption,
% 7.73/1.48                [status(thm)],
% 7.73/1.48                [c_1197,c_41,c_40,c_454,c_1514,c_1544]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_2140,plain,
% 7.73/1.48      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
% 7.73/1.48      inference(demodulation,[status(thm)],[c_2137,c_1659]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_21910,plain,
% 7.73/1.48      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k6_partfun1(sK1),X0)
% 7.73/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.73/1.48      inference(light_normalisation,[status(thm)],[c_21903,c_2140]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_22042,plain,
% 7.73/1.48      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
% 7.73/1.48      inference(superposition,[status(thm)],[c_3063,c_21910]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_24,plain,
% 7.73/1.48      ( v4_relat_1(X0,X1)
% 7.73/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.73/1.48      inference(cnf_transformation,[],[f85]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_5,plain,
% 7.73/1.48      ( ~ v4_relat_1(X0,X1)
% 7.73/1.48      | r1_tarski(k1_relat_1(X0),X1)
% 7.73/1.48      | ~ v1_relat_1(X0) ),
% 7.73/1.48      inference(cnf_transformation,[],[f65]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_401,plain,
% 7.73/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.73/1.48      | r1_tarski(k1_relat_1(X0),X1)
% 7.73/1.48      | ~ v1_relat_1(X0) ),
% 7.73/1.48      inference(resolution,[status(thm)],[c_24,c_5]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_1200,plain,
% 7.73/1.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.73/1.48      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 7.73/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.73/1.48      inference(predicate_to_equality,[status(thm)],[c_401]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_1926,plain,
% 7.73/1.48      ( r1_tarski(k1_relat_1(sK3),sK1) = iProver_top
% 7.73/1.48      | v1_relat_1(sK3) != iProver_top ),
% 7.73/1.48      inference(superposition,[status(thm)],[c_1204,c_1200]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_2372,plain,
% 7.73/1.48      ( r1_tarski(k1_relat_1(sK3),sK1) = iProver_top ),
% 7.73/1.48      inference(global_propositional_subsumption,
% 7.73/1.48                [status(thm)],
% 7.73/1.48                [c_1926,c_45,c_2157,c_2237]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_16,plain,
% 7.73/1.48      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 7.73/1.48      | ~ v1_relat_1(X0)
% 7.73/1.48      | k5_relat_1(k6_partfun1(X1),X0) = X0 ),
% 7.73/1.48      inference(cnf_transformation,[],[f107]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_1213,plain,
% 7.73/1.48      ( k5_relat_1(k6_partfun1(X0),X1) = X1
% 7.73/1.48      | r1_tarski(k1_relat_1(X1),X0) != iProver_top
% 7.73/1.48      | v1_relat_1(X1) != iProver_top ),
% 7.73/1.48      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_3401,plain,
% 7.73/1.48      ( k5_relat_1(k6_partfun1(sK1),sK3) = sK3
% 7.73/1.48      | v1_relat_1(sK3) != iProver_top ),
% 7.73/1.48      inference(superposition,[status(thm)],[c_2372,c_1213]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_4265,plain,
% 7.73/1.48      ( k5_relat_1(k6_partfun1(sK1),sK3) = sK3 ),
% 7.73/1.48      inference(global_propositional_subsumption,
% 7.73/1.48                [status(thm)],
% 7.73/1.48                [c_3401,c_45,c_2157,c_2237]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_31,plain,
% 7.73/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.73/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.73/1.48      | ~ v1_funct_1(X0)
% 7.73/1.48      | ~ v1_funct_1(X3)
% 7.73/1.48      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 7.73/1.48      inference(cnf_transformation,[],[f92]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_1205,plain,
% 7.73/1.48      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 7.73/1.48      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 7.73/1.48      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.73/1.48      | v1_funct_1(X5) != iProver_top
% 7.73/1.48      | v1_funct_1(X4) != iProver_top ),
% 7.73/1.48      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_4723,plain,
% 7.73/1.48      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 7.73/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.73/1.48      | v1_funct_1(X2) != iProver_top
% 7.73/1.48      | v1_funct_1(sK3) != iProver_top ),
% 7.73/1.48      inference(superposition,[status(thm)],[c_1204,c_1205]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_39,negated_conjecture,
% 7.73/1.48      ( v1_funct_1(sK3) ),
% 7.73/1.48      inference(cnf_transformation,[],[f96]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_44,plain,
% 7.73/1.48      ( v1_funct_1(sK3) = iProver_top ),
% 7.73/1.48      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_4889,plain,
% 7.73/1.48      ( v1_funct_1(X2) != iProver_top
% 7.73/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.73/1.48      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 7.73/1.48      inference(global_propositional_subsumption,
% 7.73/1.48                [status(thm)],
% 7.73/1.48                [c_4723,c_44]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_4890,plain,
% 7.73/1.48      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 7.73/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.73/1.48      | v1_funct_1(X2) != iProver_top ),
% 7.73/1.48      inference(renaming,[status(thm)],[c_4889]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_4898,plain,
% 7.73/1.48      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 7.73/1.48      | v1_funct_1(sK2) != iProver_top ),
% 7.73/1.48      inference(superposition,[status(thm)],[c_1202,c_4890]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_27,plain,
% 7.73/1.48      ( ~ r2_relset_1(X0,X1,X2,X3)
% 7.73/1.48      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.73/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.73/1.48      | X3 = X2 ),
% 7.73/1.48      inference(cnf_transformation,[],[f87]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_36,negated_conjecture,
% 7.73/1.48      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 7.73/1.48      inference(cnf_transformation,[],[f99]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_422,plain,
% 7.73/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.73/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.73/1.48      | X3 = X0
% 7.73/1.48      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 7.73/1.48      | k6_partfun1(sK0) != X3
% 7.73/1.48      | sK0 != X2
% 7.73/1.48      | sK0 != X1 ),
% 7.73/1.48      inference(resolution_lifted,[status(thm)],[c_27,c_36]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_423,plain,
% 7.73/1.48      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.73/1.48      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.73/1.48      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.73/1.48      inference(unflattening,[status(thm)],[c_422]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_28,plain,
% 7.73/1.48      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 7.73/1.48      inference(cnf_transformation,[],[f111]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_58,plain,
% 7.73/1.48      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 7.73/1.48      inference(instantiation,[status(thm)],[c_28]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_425,plain,
% 7.73/1.48      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.73/1.48      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.73/1.48      inference(global_propositional_subsumption,
% 7.73/1.48                [status(thm)],
% 7.73/1.48                [c_423,c_58]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_1199,plain,
% 7.73/1.48      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.73/1.48      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 7.73/1.48      inference(predicate_to_equality,[status(thm)],[c_425]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_29,plain,
% 7.73/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.73/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.73/1.48      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.73/1.48      | ~ v1_funct_1(X0)
% 7.73/1.48      | ~ v1_funct_1(X3) ),
% 7.73/1.48      inference(cnf_transformation,[],[f91]) ).
% 7.73/1.48  
% 7.73/1.48  cnf(c_1275,plain,
% 7.73/1.48      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.73/1.48      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 7.73/1.49      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.73/1.49      | ~ v1_funct_1(sK3)
% 7.73/1.49      | ~ v1_funct_1(sK2) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_29]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_1801,plain,
% 7.73/1.49      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.73/1.49      inference(global_propositional_subsumption,
% 7.73/1.49                [status(thm)],
% 7.73/1.49                [c_1199,c_41,c_40,c_39,c_38,c_58,c_423,c_1275]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_4899,plain,
% 7.73/1.49      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 7.73/1.49      | v1_funct_1(sK2) != iProver_top ),
% 7.73/1.49      inference(light_normalisation,[status(thm)],[c_4898,c_1801]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_42,plain,
% 7.73/1.49      ( v1_funct_1(sK2) = iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_5298,plain,
% 7.73/1.49      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 7.73/1.49      inference(global_propositional_subsumption,
% 7.73/1.49                [status(thm)],
% 7.73/1.49                [c_4899,c_42]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_17,plain,
% 7.73/1.49      ( ~ v1_relat_1(X0)
% 7.73/1.49      | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ),
% 7.73/1.49      inference(cnf_transformation,[],[f108]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_1212,plain,
% 7.73/1.49      ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
% 7.73/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2804,plain,
% 7.73/1.49      ( k5_relat_1(k2_funct_1(X0),k6_partfun1(k2_relat_1(k2_funct_1(X0)))) = k2_funct_1(X0)
% 7.73/1.49      | v1_funct_1(X0) != iProver_top
% 7.73/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.73/1.49      inference(superposition,[status(thm)],[c_1210,c_1212]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_7145,plain,
% 7.73/1.49      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(k2_relat_1(k2_funct_1(sK2)))) = k2_funct_1(sK2)
% 7.73/1.49      | v1_relat_1(sK2) != iProver_top ),
% 7.73/1.49      inference(superposition,[status(thm)],[c_1201,c_2804]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_20,plain,
% 7.73/1.49      ( ~ v2_funct_1(X0)
% 7.73/1.49      | ~ v1_funct_1(X0)
% 7.73/1.49      | ~ v1_relat_1(X0)
% 7.73/1.49      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 7.73/1.49      inference(cnf_transformation,[],[f82]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_481,plain,
% 7.73/1.49      ( ~ v1_funct_1(X0)
% 7.73/1.49      | ~ v1_relat_1(X0)
% 7.73/1.49      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 7.73/1.49      | sK2 != X0 ),
% 7.73/1.49      inference(resolution_lifted,[status(thm)],[c_20,c_35]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_482,plain,
% 7.73/1.49      ( ~ v1_funct_1(sK2)
% 7.73/1.49      | ~ v1_relat_1(sK2)
% 7.73/1.49      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 7.73/1.49      inference(unflattening,[status(thm)],[c_481]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_484,plain,
% 7.73/1.49      ( ~ v1_relat_1(sK2)
% 7.73/1.49      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 7.73/1.49      inference(global_propositional_subsumption,
% 7.73/1.49                [status(thm)],
% 7.73/1.49                [c_482,c_41]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_1195,plain,
% 7.73/1.49      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 7.73/1.49      | v1_relat_1(sK2) != iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_484]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_3078,plain,
% 7.73/1.49      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 7.73/1.49      inference(superposition,[status(thm)],[c_3071,c_1195]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_7149,plain,
% 7.73/1.49      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(k1_relat_1(sK2))) = k2_funct_1(sK2)
% 7.73/1.49      | v1_relat_1(sK2) != iProver_top ),
% 7.73/1.49      inference(light_normalisation,[status(thm)],[c_7145,c_3078]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_11,plain,
% 7.73/1.49      ( ~ v1_relat_1(X0)
% 7.73/1.49      | ~ v1_relat_1(X1)
% 7.73/1.49      | k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1)) ),
% 7.73/1.49      inference(cnf_transformation,[],[f72]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_1215,plain,
% 7.73/1.49      ( k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,X0))
% 7.73/1.49      | v1_relat_1(X1) != iProver_top
% 7.73/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_3548,plain,
% 7.73/1.49      ( k5_relat_1(k4_relat_1(sK3),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,sK3))
% 7.73/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.73/1.49      inference(superposition,[status(thm)],[c_3063,c_1215]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_5307,plain,
% 7.73/1.49      ( k5_relat_1(k4_relat_1(sK3),k4_relat_1(sK2)) = k4_relat_1(k5_relat_1(sK2,sK3)) ),
% 7.73/1.49      inference(superposition,[status(thm)],[c_3071,c_3548]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_5309,plain,
% 7.73/1.49      ( k5_relat_1(k4_relat_1(sK3),k4_relat_1(sK2)) = k4_relat_1(k6_partfun1(sK0)) ),
% 7.73/1.49      inference(light_normalisation,[status(thm)],[c_5307,c_5298]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_15,plain,
% 7.73/1.49      ( k4_relat_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
% 7.73/1.49      inference(cnf_transformation,[],[f106]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_5310,plain,
% 7.73/1.49      ( k5_relat_1(k4_relat_1(sK3),k4_relat_1(sK2)) = k6_partfun1(sK0) ),
% 7.73/1.49      inference(demodulation,[status(thm)],[c_5309,c_15]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_10,plain,
% 7.73/1.49      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
% 7.73/1.49      | ~ v1_relat_1(X0)
% 7.73/1.49      | ~ v1_relat_1(X1) ),
% 7.73/1.49      inference(cnf_transformation,[],[f71]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_1216,plain,
% 7.73/1.49      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
% 7.73/1.49      | v1_relat_1(X0) != iProver_top
% 7.73/1.49      | v1_relat_1(X1) != iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_5448,plain,
% 7.73/1.49      ( r1_tarski(k2_relat_1(k6_partfun1(sK0)),k2_relat_1(k4_relat_1(sK2))) = iProver_top
% 7.73/1.49      | v1_relat_1(k4_relat_1(sK3)) != iProver_top
% 7.73/1.49      | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
% 7.73/1.49      inference(superposition,[status(thm)],[c_5310,c_1216]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_8,plain,
% 7.73/1.49      ( ~ v1_relat_1(X0) | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
% 7.73/1.49      inference(cnf_transformation,[],[f70]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_1218,plain,
% 7.73/1.49      ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
% 7.73/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_3076,plain,
% 7.73/1.49      ( k2_relat_1(k4_relat_1(sK2)) = k1_relat_1(sK2) ),
% 7.73/1.49      inference(superposition,[status(thm)],[c_3071,c_1218]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_5449,plain,
% 7.73/1.49      ( r1_tarski(k2_relat_1(k6_partfun1(sK0)),k1_relat_1(sK2)) = iProver_top
% 7.73/1.49      | v1_relat_1(k4_relat_1(sK3)) != iProver_top
% 7.73/1.49      | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
% 7.73/1.49      inference(light_normalisation,[status(thm)],[c_5448,c_3076]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_13,plain,
% 7.73/1.49      ( k2_relat_1(k6_partfun1(X0)) = X0 ),
% 7.73/1.49      inference(cnf_transformation,[],[f104]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_5450,plain,
% 7.73/1.49      ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top
% 7.73/1.49      | v1_relat_1(k4_relat_1(sK3)) != iProver_top
% 7.73/1.49      | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
% 7.73/1.49      inference(demodulation,[status(thm)],[c_5449,c_13]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_6,plain,
% 7.73/1.49      ( ~ v1_relat_1(X0) | v1_relat_1(k4_relat_1(X0)) ),
% 7.73/1.49      inference(cnf_transformation,[],[f67]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_1812,plain,
% 7.73/1.49      ( v1_relat_1(k4_relat_1(sK2)) | ~ v1_relat_1(sK2) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_6]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_1835,plain,
% 7.73/1.49      ( v1_relat_1(k4_relat_1(sK2)) = iProver_top
% 7.73/1.49      | v1_relat_1(sK2) != iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_1812]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2522,plain,
% 7.73/1.49      ( v1_relat_1(k4_relat_1(sK3)) | ~ v1_relat_1(sK3) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_6]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2547,plain,
% 7.73/1.49      ( v1_relat_1(k4_relat_1(sK3)) = iProver_top
% 7.73/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_2522]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_5595,plain,
% 7.73/1.49      ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top ),
% 7.73/1.49      inference(global_propositional_subsumption,
% 7.73/1.49                [status(thm)],
% 7.73/1.49                [c_5450,c_43,c_45,c_1515,c_1545,c_1835,c_2157,c_2237,
% 7.73/1.49                 c_2547]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_1927,plain,
% 7.73/1.49      ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top
% 7.73/1.49      | v1_relat_1(sK2) != iProver_top ),
% 7.73/1.49      inference(superposition,[status(thm)],[c_1202,c_1200]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2503,plain,
% 7.73/1.49      ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
% 7.73/1.49      inference(global_propositional_subsumption,
% 7.73/1.49                [status(thm)],
% 7.73/1.49                [c_1927,c_43,c_1515,c_1545]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_0,plain,
% 7.73/1.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.73/1.49      inference(cnf_transformation,[],[f63]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_1223,plain,
% 7.73/1.49      ( X0 = X1
% 7.73/1.49      | r1_tarski(X0,X1) != iProver_top
% 7.73/1.49      | r1_tarski(X1,X0) != iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2991,plain,
% 7.73/1.49      ( k1_relat_1(sK2) = sK0
% 7.73/1.49      | r1_tarski(sK0,k1_relat_1(sK2)) != iProver_top ),
% 7.73/1.49      inference(superposition,[status(thm)],[c_2503,c_1223]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_5601,plain,
% 7.73/1.49      ( k1_relat_1(sK2) = sK0 ),
% 7.73/1.49      inference(superposition,[status(thm)],[c_5595,c_2991]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_7150,plain,
% 7.73/1.49      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k2_funct_1(sK2)
% 7.73/1.49      | v1_relat_1(sK2) != iProver_top ),
% 7.73/1.49      inference(demodulation,[status(thm)],[c_7149,c_5601]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_15086,plain,
% 7.73/1.49      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k2_funct_1(sK2) ),
% 7.73/1.49      inference(global_propositional_subsumption,
% 7.73/1.49                [status(thm)],
% 7.73/1.49                [c_7150,c_43,c_1515,c_1545]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_22050,plain,
% 7.73/1.49      ( k2_funct_1(sK2) = sK3 ),
% 7.73/1.49      inference(light_normalisation,
% 7.73/1.49                [status(thm)],
% 7.73/1.49                [c_22042,c_4265,c_5298,c_15086]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_32,negated_conjecture,
% 7.73/1.49      ( k2_funct_1(sK2) != sK3 ),
% 7.73/1.49      inference(cnf_transformation,[],[f103]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(contradiction,plain,
% 7.73/1.49      ( $false ),
% 7.73/1.49      inference(minisat,[status(thm)],[c_22050,c_32]) ).
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.73/1.49  
% 7.73/1.49  ------                               Statistics
% 7.73/1.49  
% 7.73/1.49  ------ General
% 7.73/1.49  
% 7.73/1.49  abstr_ref_over_cycles:                  0
% 7.73/1.49  abstr_ref_under_cycles:                 0
% 7.73/1.49  gc_basic_clause_elim:                   0
% 7.73/1.49  forced_gc_time:                         0
% 7.73/1.49  parsing_time:                           0.01
% 7.73/1.49  unif_index_cands_time:                  0.
% 7.73/1.49  unif_index_add_time:                    0.
% 7.73/1.49  orderings_time:                         0.
% 7.73/1.49  out_proof_time:                         0.014
% 7.73/1.49  total_time:                             0.686
% 7.73/1.49  num_of_symbols:                         53
% 7.73/1.49  num_of_terms:                           31759
% 7.73/1.49  
% 7.73/1.49  ------ Preprocessing
% 7.73/1.49  
% 7.73/1.49  num_of_splits:                          0
% 7.73/1.49  num_of_split_atoms:                     0
% 7.73/1.49  num_of_reused_defs:                     0
% 7.73/1.49  num_eq_ax_congr_red:                    2
% 7.73/1.49  num_of_sem_filtered_clauses:            1
% 7.73/1.49  num_of_subtypes:                        0
% 7.73/1.49  monotx_restored_types:                  0
% 7.73/1.49  sat_num_of_epr_types:                   0
% 7.73/1.49  sat_num_of_non_cyclic_types:            0
% 7.73/1.49  sat_guarded_non_collapsed_types:        0
% 7.73/1.49  num_pure_diseq_elim:                    0
% 7.73/1.49  simp_replaced_by:                       0
% 7.73/1.49  res_preprocessed:                       182
% 7.73/1.49  prep_upred:                             0
% 7.73/1.49  prep_unflattend:                        12
% 7.73/1.49  smt_new_axioms:                         0
% 7.73/1.49  pred_elim_cands:                        4
% 7.73/1.49  pred_elim:                              3
% 7.73/1.49  pred_elim_cl:                           5
% 7.73/1.49  pred_elim_cycles:                       5
% 7.73/1.49  merged_defs:                            0
% 7.73/1.49  merged_defs_ncl:                        0
% 7.73/1.49  bin_hyper_res:                          0
% 7.73/1.49  prep_cycles:                            4
% 7.73/1.49  pred_elim_time:                         0.003
% 7.73/1.49  splitting_time:                         0.
% 7.73/1.49  sem_filter_time:                        0.
% 7.73/1.49  monotx_time:                            0.
% 7.73/1.49  subtype_inf_time:                       0.
% 7.73/1.49  
% 7.73/1.49  ------ Problem properties
% 7.73/1.49  
% 7.73/1.49  clauses:                                36
% 7.73/1.49  conjectures:                            8
% 7.73/1.49  epr:                                    6
% 7.73/1.49  horn:                                   36
% 7.73/1.49  ground:                                 13
% 7.73/1.49  unary:                                  14
% 7.73/1.49  binary:                                 10
% 7.73/1.49  lits:                                   77
% 7.73/1.49  lits_eq:                                21
% 7.73/1.49  fd_pure:                                0
% 7.73/1.49  fd_pseudo:                              0
% 7.73/1.49  fd_cond:                                0
% 7.73/1.49  fd_pseudo_cond:                         1
% 7.73/1.49  ac_symbols:                             0
% 7.73/1.49  
% 7.73/1.49  ------ Propositional Solver
% 7.73/1.49  
% 7.73/1.49  prop_solver_calls:                      35
% 7.73/1.49  prop_fast_solver_calls:                 1822
% 7.73/1.49  smt_solver_calls:                       0
% 7.73/1.49  smt_fast_solver_calls:                  0
% 7.73/1.49  prop_num_of_clauses:                    12227
% 7.73/1.49  prop_preprocess_simplified:             20846
% 7.73/1.49  prop_fo_subsumed:                       189
% 7.73/1.49  prop_solver_time:                       0.
% 7.73/1.49  smt_solver_time:                        0.
% 7.73/1.49  smt_fast_solver_time:                   0.
% 7.73/1.49  prop_fast_solver_time:                  0.
% 7.73/1.49  prop_unsat_core_time:                   0.001
% 7.73/1.49  
% 7.73/1.49  ------ QBF
% 7.73/1.49  
% 7.73/1.49  qbf_q_res:                              0
% 7.73/1.49  qbf_num_tautologies:                    0
% 7.73/1.49  qbf_prep_cycles:                        0
% 7.73/1.49  
% 7.73/1.49  ------ BMC1
% 7.73/1.49  
% 7.73/1.49  bmc1_current_bound:                     -1
% 7.73/1.49  bmc1_last_solved_bound:                 -1
% 7.73/1.49  bmc1_unsat_core_size:                   -1
% 7.73/1.49  bmc1_unsat_core_parents_size:           -1
% 7.73/1.49  bmc1_merge_next_fun:                    0
% 7.73/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.73/1.49  
% 7.73/1.49  ------ Instantiation
% 7.73/1.49  
% 7.73/1.49  inst_num_of_clauses:                    3263
% 7.73/1.49  inst_num_in_passive:                    304
% 7.73/1.49  inst_num_in_active:                     1679
% 7.73/1.49  inst_num_in_unprocessed:                1280
% 7.73/1.49  inst_num_of_loops:                      1790
% 7.73/1.49  inst_num_of_learning_restarts:          0
% 7.73/1.49  inst_num_moves_active_passive:          107
% 7.73/1.49  inst_lit_activity:                      0
% 7.73/1.49  inst_lit_activity_moves:                2
% 7.73/1.49  inst_num_tautologies:                   0
% 7.73/1.49  inst_num_prop_implied:                  0
% 7.73/1.49  inst_num_existing_simplified:           0
% 7.73/1.49  inst_num_eq_res_simplified:             0
% 7.73/1.49  inst_num_child_elim:                    0
% 7.73/1.49  inst_num_of_dismatching_blockings:      767
% 7.73/1.49  inst_num_of_non_proper_insts:           3162
% 7.73/1.49  inst_num_of_duplicates:                 0
% 7.73/1.49  inst_inst_num_from_inst_to_res:         0
% 7.73/1.49  inst_dismatching_checking_time:         0.
% 7.73/1.49  
% 7.73/1.49  ------ Resolution
% 7.73/1.49  
% 7.73/1.49  res_num_of_clauses:                     0
% 7.73/1.49  res_num_in_passive:                     0
% 7.73/1.49  res_num_in_active:                      0
% 7.73/1.49  res_num_of_loops:                       186
% 7.73/1.49  res_forward_subset_subsumed:            307
% 7.73/1.49  res_backward_subset_subsumed:           0
% 7.73/1.49  res_forward_subsumed:                   0
% 7.73/1.49  res_backward_subsumed:                  0
% 7.73/1.49  res_forward_subsumption_resolution:     0
% 7.73/1.49  res_backward_subsumption_resolution:    0
% 7.73/1.49  res_clause_to_clause_subsumption:       3088
% 7.73/1.49  res_orphan_elimination:                 0
% 7.73/1.49  res_tautology_del:                      335
% 7.73/1.49  res_num_eq_res_simplified:              0
% 7.73/1.49  res_num_sel_changes:                    0
% 7.73/1.49  res_moves_from_active_to_pass:          0
% 7.73/1.49  
% 7.73/1.49  ------ Superposition
% 7.73/1.49  
% 7.73/1.49  sup_time_total:                         0.
% 7.73/1.49  sup_time_generating:                    0.
% 7.73/1.49  sup_time_sim_full:                      0.
% 7.73/1.49  sup_time_sim_immed:                     0.
% 7.73/1.49  
% 7.73/1.49  sup_num_of_clauses:                     928
% 7.73/1.49  sup_num_in_active:                      315
% 7.73/1.49  sup_num_in_passive:                     613
% 7.73/1.49  sup_num_of_loops:                       357
% 7.73/1.49  sup_fw_superposition:                   807
% 7.73/1.49  sup_bw_superposition:                   412
% 7.73/1.49  sup_immediate_simplified:               595
% 7.73/1.49  sup_given_eliminated:                   6
% 7.73/1.49  comparisons_done:                       0
% 7.73/1.49  comparisons_avoided:                    0
% 7.73/1.49  
% 7.73/1.49  ------ Simplifications
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  sim_fw_subset_subsumed:                 31
% 7.73/1.49  sim_bw_subset_subsumed:                 70
% 7.73/1.49  sim_fw_subsumed:                        69
% 7.73/1.49  sim_bw_subsumed:                        5
% 7.73/1.49  sim_fw_subsumption_res:                 0
% 7.73/1.49  sim_bw_subsumption_res:                 0
% 7.73/1.49  sim_tautology_del:                      8
% 7.73/1.49  sim_eq_tautology_del:                   156
% 7.73/1.49  sim_eq_res_simp:                        0
% 7.73/1.49  sim_fw_demodulated:                     158
% 7.73/1.49  sim_bw_demodulated:                     21
% 7.73/1.49  sim_light_normalised:                   613
% 7.73/1.49  sim_joinable_taut:                      0
% 7.73/1.49  sim_joinable_simp:                      0
% 7.73/1.49  sim_ac_normalised:                      0
% 7.73/1.49  sim_smt_subsumption:                    0
% 7.73/1.49  
%------------------------------------------------------------------------------
