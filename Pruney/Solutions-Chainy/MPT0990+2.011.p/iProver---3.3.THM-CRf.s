%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:58 EST 2020

% Result     : Theorem 7.77s
% Output     : CNFRefutation 7.77s
% Verified   : 
% Statistics : Number of formulae       :  226 (2055 expanded)
%              Number of clauses        :  136 ( 628 expanded)
%              Number of leaves         :   26 ( 507 expanded)
%              Depth                    :   22
%              Number of atoms          :  780 (15401 expanded)
%              Number of equality atoms :  365 (5475 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,conjecture,(
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

fof(f22,negated_conjecture,(
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
    inference(negated_conjecture,[],[f21])).

fof(f47,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f48,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f47])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
     => ( k2_funct_1(X2) != sK3
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & v2_funct_1(X2)
        & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0))
        & k2_relset_1(X0,X1,X2) = X1
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(sK3,X1,X0)
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( k2_funct_1(X2) != X3
            & k1_xboole_0 != X1
            & k1_xboole_0 != X0
            & v2_funct_1(X2)
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & k2_relset_1(X0,X1,X2) = X1
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k2_funct_1(sK2) != X3
          & k1_xboole_0 != sK1
          & k1_xboole_0 != sK0
          & v2_funct_1(sK2)
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & k2_relset_1(sK0,sK1,sK2) = sK1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( k2_funct_1(sK2) != sK3
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & v2_funct_1(sK2)
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & k2_relset_1(sK0,sK1,sK2) = sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f48,f54,f53])).

fof(f89,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f55])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f86,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f55])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f90,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f55])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f84,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f43])).

fof(f81,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f87,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f39])).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f91,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f55])).

fof(f16,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f19,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f82,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f19])).

fof(f101,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f78,f82])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f41])).

fof(f80,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f6,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f97,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f64,f82])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f49])).

fof(f58,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f61,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => ( v2_funct_1(X0)
              & v2_funct_1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X0)
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
              & k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f100,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f71,f82])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
           => k2_relset_1(X0,X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f45])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f85,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f88,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f35,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f72,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f102,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f7,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f98,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f67,f82])).

fof(f95,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_712,plain,
    ( X0 != X1
    | k2_funct_1(X0) = k2_funct_1(X1) ),
    theory(equality)).

cnf(c_16528,plain,
    ( k2_funct_1(sK2) = k2_funct_1(k2_funct_1(sK3))
    | sK2 != k2_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_712])).

cnf(c_702,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1278,plain,
    ( k2_funct_1(sK2) != X0
    | k2_funct_1(sK2) = sK3
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_702])).

cnf(c_13603,plain,
    ( k2_funct_1(sK2) != k2_funct_1(k2_funct_1(sK3))
    | k2_funct_1(sK2) = sK3
    | sK3 != k2_funct_1(k2_funct_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_1278])).

cnf(c_1853,plain,
    ( X0 != X1
    | sK2 != X1
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_702])).

cnf(c_3332,plain,
    ( X0 != sK2
    | sK2 = X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1853])).

cnf(c_4382,plain,
    ( k2_funct_1(X0) != sK2
    | sK2 = k2_funct_1(X0)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_3332])).

cnf(c_13102,plain,
    ( k2_funct_1(sK3) != sK2
    | sK2 = k2_funct_1(sK3)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_4382])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1214,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v4_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_4,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_372,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_18,c_4])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_376,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_372,c_17])).

cnf(c_377,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_376])).

cnf(c_1208,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_377])).

cnf(c_2753,plain,
    ( r1_tarski(k1_relat_1(sK3),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1214,c_1208])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1211,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1220,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2250,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1211,c_1220])).

cnf(c_32,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_2251,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2250,c_32])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1226,plain,
    ( k9_relat_1(X0,k10_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4169,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
    | r1_tarski(X0,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2251,c_1226])).

cnf(c_38,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_39,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_41,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_1626,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1627,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1626])).

cnf(c_4405,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4169,c_39,c_41,c_1627])).

cnf(c_4412,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(sK3))) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2753,c_4405])).

cnf(c_1221,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2243,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1214,c_1221])).

cnf(c_2244,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1211,c_1221])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1230,plain,
    ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2866,plain,
    ( k10_relat_1(sK2,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(sK2,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2244,c_1230])).

cnf(c_3625,plain,
    ( k10_relat_1(sK2,k1_relat_1(sK3)) = k1_relat_1(k5_relat_1(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_2243,c_2866])).

cnf(c_4414,plain,
    ( k9_relat_1(sK2,k1_relat_1(k5_relat_1(sK2,sK3))) = k1_relat_1(sK3) ),
    inference(light_normalisation,[status(thm)],[c_4412,c_3625])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1216,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_4762,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1214,c_1216])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_42,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_4883,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4762,c_42])).

cnf(c_4884,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4883])).

cnf(c_4892,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1211,c_4884])).

cnf(c_21,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_31,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_430,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_31])).

cnf(c_431,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_430])).

cnf(c_22,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_60,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_433,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_431,c_60])).

cnf(c_1206,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_433])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1288,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_1874,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1206,c_38,c_36,c_35,c_33,c_60,c_431,c_1288])).

cnf(c_4893,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4892,c_1874])).

cnf(c_5081,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4893,c_39])).

cnf(c_11305,plain,
    ( k9_relat_1(sK2,k1_relat_1(k6_partfun1(sK0))) = k1_relat_1(sK3) ),
    inference(light_normalisation,[status(thm)],[c_4414,c_4414,c_5081])).

cnf(c_9,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_7,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1229,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5086,plain,
    ( r1_tarski(k1_relat_1(k6_partfun1(sK0)),k1_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5081,c_1229])).

cnf(c_5087,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5086,c_9])).

cnf(c_44,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_1323,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1425,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1323])).

cnf(c_1426,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1425])).

cnf(c_5238,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5087,c_41,c_44,c_1426,c_1627])).

cnf(c_2754,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1211,c_1208])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1233,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3030,plain,
    ( k1_relat_1(sK2) = sK0
    | r1_tarski(sK0,k1_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2754,c_1233])).

cnf(c_5244,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(superposition,[status(thm)],[c_5238,c_3030])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1231,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2485,plain,
    ( k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2244,c_1231])).

cnf(c_2486,plain,
    ( k9_relat_1(sK2,k1_relat_1(sK2)) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2485,c_2251])).

cnf(c_7849,plain,
    ( k9_relat_1(sK2,sK0) = sK1 ),
    inference(demodulation,[status(thm)],[c_5244,c_2486])).

cnf(c_11306,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(demodulation,[status(thm)],[c_11305,c_9,c_7849])).

cnf(c_13,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | v2_funct_1(X1)
    | ~ v2_funct_1(k5_relat_1(X0,X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k2_relat_1(X0) != k1_relat_1(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1225,plain,
    ( k2_relat_1(X0) != k1_relat_1(X1)
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k5_relat_1(X0,X1)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4862,plain,
    ( k1_relat_1(X0) != sK1
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k5_relat_1(sK2,X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2251,c_1225])).

cnf(c_5065,plain,
    ( v1_relat_1(X0) != iProver_top
    | v2_funct_1(k5_relat_1(sK2,X0)) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | k1_relat_1(X0) != sK1
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4862,c_39,c_41,c_1627])).

cnf(c_5066,plain,
    ( k1_relat_1(X0) != sK1
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k5_relat_1(sK2,X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5065])).

cnf(c_11324,plain,
    ( v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_11306,c_5066])).

cnf(c_11326,plain,
    ( v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11324,c_5081])).

cnf(c_15,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k2_relat_1(X0) != k1_relat_1(X1) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1223,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k2_relat_1(X0) != k1_relat_1(X1)
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v2_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_5085,plain,
    ( k2_funct_1(sK3) = sK2
    | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5081,c_1223])).

cnf(c_2249,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1214,c_1220])).

cnf(c_26,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_444,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,X2,X0) = X2
    | k6_partfun1(X2) != k6_partfun1(sK0)
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_31])).

cnf(c_445,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0
    | k6_partfun1(sK0) != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_444])).

cnf(c_528,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_445])).

cnf(c_1205,plain,
    ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X0,sK0,X2) = sK0
    | v1_funct_2(X2,X0,sK0) != iProver_top
    | v1_funct_2(X1,sK0,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_528])).

cnf(c_1605,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1205])).

cnf(c_37,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_40,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_43,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_1972,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1605,c_39,c_40,c_41,c_42,c_43,c_44])).

cnf(c_2252,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_2249,c_1972])).

cnf(c_5088,plain,
    ( k2_funct_1(sK3) = sK2
    | k6_partfun1(sK0) != k6_partfun1(sK0)
    | k1_relat_1(sK3) != sK1
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5085,c_2251,c_2252])).

cnf(c_5089,plain,
    ( k2_funct_1(sK3) = sK2
    | k1_relat_1(sK3) != sK1
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5088])).

cnf(c_6478,plain,
    ( k2_funct_1(sK3) = sK2
    | k1_relat_1(sK3) != sK1
    | v2_funct_1(sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5089,c_39,c_41,c_42,c_44,c_1426,c_1627])).

cnf(c_1212,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_16,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1222,plain,
    ( k2_funct_1(k2_funct_1(X0)) = X0
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4158,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1212,c_1222])).

cnf(c_1959,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k2_funct_1(k2_funct_1(sK3)) = sK3 ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1960,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1959])).

cnf(c_4355,plain,
    ( v2_funct_1(sK3) != iProver_top
    | k2_funct_1(k2_funct_1(sK3)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4158,c_42,c_44,c_1426,c_1960])).

cnf(c_4356,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3
    | v2_funct_1(sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_4355])).

cnf(c_1343,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_702])).

cnf(c_1618,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1343])).

cnf(c_2139,plain,
    ( k2_funct_1(X0) != sK3
    | sK3 = k2_funct_1(X0)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1618])).

cnf(c_3795,plain,
    ( k2_funct_1(k2_funct_1(sK3)) != sK3
    | sK3 = k2_funct_1(k2_funct_1(sK3))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2139])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_2069,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1479,plain,
    ( ~ r1_tarski(X0,sK2)
    | ~ r1_tarski(sK2,X0)
    | X0 = sK2 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1753,plain,
    ( ~ r1_tarski(sK2,sK2)
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1479])).

cnf(c_701,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1686,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_701])).

cnf(c_10,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_93,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_95,plain,
    ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_93])).

cnf(c_27,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f95])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_16528,c_13603,c_13102,c_11326,c_11306,c_6478,c_4356,c_3795,c_2069,c_1753,c_1686,c_1426,c_95,c_27,c_44,c_42])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:41:00 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.77/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.77/1.49  
% 7.77/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.77/1.49  
% 7.77/1.49  ------  iProver source info
% 7.77/1.49  
% 7.77/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.77/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.77/1.49  git: non_committed_changes: false
% 7.77/1.49  git: last_make_outside_of_git: false
% 7.77/1.49  
% 7.77/1.49  ------ 
% 7.77/1.49  
% 7.77/1.49  ------ Input Options
% 7.77/1.49  
% 7.77/1.49  --out_options                           all
% 7.77/1.49  --tptp_safe_out                         true
% 7.77/1.49  --problem_path                          ""
% 7.77/1.49  --include_path                          ""
% 7.77/1.49  --clausifier                            res/vclausify_rel
% 7.77/1.49  --clausifier_options                    ""
% 7.77/1.49  --stdin                                 false
% 7.77/1.49  --stats_out                             all
% 7.77/1.49  
% 7.77/1.49  ------ General Options
% 7.77/1.49  
% 7.77/1.49  --fof                                   false
% 7.77/1.49  --time_out_real                         305.
% 7.77/1.49  --time_out_virtual                      -1.
% 7.77/1.49  --symbol_type_check                     false
% 7.77/1.49  --clausify_out                          false
% 7.77/1.49  --sig_cnt_out                           false
% 7.77/1.49  --trig_cnt_out                          false
% 7.77/1.49  --trig_cnt_out_tolerance                1.
% 7.77/1.49  --trig_cnt_out_sk_spl                   false
% 7.77/1.49  --abstr_cl_out                          false
% 7.77/1.49  
% 7.77/1.49  ------ Global Options
% 7.77/1.49  
% 7.77/1.49  --schedule                              default
% 7.77/1.49  --add_important_lit                     false
% 7.77/1.49  --prop_solver_per_cl                    1000
% 7.77/1.49  --min_unsat_core                        false
% 7.77/1.49  --soft_assumptions                      false
% 7.77/1.49  --soft_lemma_size                       3
% 7.77/1.49  --prop_impl_unit_size                   0
% 7.77/1.49  --prop_impl_unit                        []
% 7.77/1.49  --share_sel_clauses                     true
% 7.77/1.49  --reset_solvers                         false
% 7.77/1.49  --bc_imp_inh                            [conj_cone]
% 7.77/1.49  --conj_cone_tolerance                   3.
% 7.77/1.49  --extra_neg_conj                        none
% 7.77/1.49  --large_theory_mode                     true
% 7.77/1.49  --prolific_symb_bound                   200
% 7.77/1.49  --lt_threshold                          2000
% 7.77/1.49  --clause_weak_htbl                      true
% 7.77/1.49  --gc_record_bc_elim                     false
% 7.77/1.49  
% 7.77/1.49  ------ Preprocessing Options
% 7.77/1.49  
% 7.77/1.49  --preprocessing_flag                    true
% 7.77/1.49  --time_out_prep_mult                    0.1
% 7.77/1.49  --splitting_mode                        input
% 7.77/1.49  --splitting_grd                         true
% 7.77/1.49  --splitting_cvd                         false
% 7.77/1.49  --splitting_cvd_svl                     false
% 7.77/1.49  --splitting_nvd                         32
% 7.77/1.49  --sub_typing                            true
% 7.77/1.49  --prep_gs_sim                           true
% 7.77/1.49  --prep_unflatten                        true
% 7.77/1.49  --prep_res_sim                          true
% 7.77/1.49  --prep_upred                            true
% 7.77/1.49  --prep_sem_filter                       exhaustive
% 7.77/1.49  --prep_sem_filter_out                   false
% 7.77/1.49  --pred_elim                             true
% 7.77/1.49  --res_sim_input                         true
% 7.77/1.49  --eq_ax_congr_red                       true
% 7.77/1.49  --pure_diseq_elim                       true
% 7.77/1.49  --brand_transform                       false
% 7.77/1.49  --non_eq_to_eq                          false
% 7.77/1.49  --prep_def_merge                        true
% 7.77/1.49  --prep_def_merge_prop_impl              false
% 7.77/1.49  --prep_def_merge_mbd                    true
% 7.77/1.49  --prep_def_merge_tr_red                 false
% 7.77/1.49  --prep_def_merge_tr_cl                  false
% 7.77/1.49  --smt_preprocessing                     true
% 7.77/1.49  --smt_ac_axioms                         fast
% 7.77/1.49  --preprocessed_out                      false
% 7.77/1.49  --preprocessed_stats                    false
% 7.77/1.49  
% 7.77/1.49  ------ Abstraction refinement Options
% 7.77/1.49  
% 7.77/1.49  --abstr_ref                             []
% 7.77/1.49  --abstr_ref_prep                        false
% 7.77/1.49  --abstr_ref_until_sat                   false
% 7.77/1.49  --abstr_ref_sig_restrict                funpre
% 7.77/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.77/1.49  --abstr_ref_under                       []
% 7.77/1.49  
% 7.77/1.49  ------ SAT Options
% 7.77/1.49  
% 7.77/1.49  --sat_mode                              false
% 7.77/1.49  --sat_fm_restart_options                ""
% 7.77/1.49  --sat_gr_def                            false
% 7.77/1.49  --sat_epr_types                         true
% 7.77/1.49  --sat_non_cyclic_types                  false
% 7.77/1.49  --sat_finite_models                     false
% 7.77/1.49  --sat_fm_lemmas                         false
% 7.77/1.49  --sat_fm_prep                           false
% 7.77/1.49  --sat_fm_uc_incr                        true
% 7.77/1.49  --sat_out_model                         small
% 7.77/1.49  --sat_out_clauses                       false
% 7.77/1.49  
% 7.77/1.49  ------ QBF Options
% 7.77/1.49  
% 7.77/1.49  --qbf_mode                              false
% 7.77/1.49  --qbf_elim_univ                         false
% 7.77/1.49  --qbf_dom_inst                          none
% 7.77/1.49  --qbf_dom_pre_inst                      false
% 7.77/1.49  --qbf_sk_in                             false
% 7.77/1.49  --qbf_pred_elim                         true
% 7.77/1.49  --qbf_split                             512
% 7.77/1.49  
% 7.77/1.49  ------ BMC1 Options
% 7.77/1.49  
% 7.77/1.49  --bmc1_incremental                      false
% 7.77/1.49  --bmc1_axioms                           reachable_all
% 7.77/1.49  --bmc1_min_bound                        0
% 7.77/1.49  --bmc1_max_bound                        -1
% 7.77/1.49  --bmc1_max_bound_default                -1
% 7.77/1.49  --bmc1_symbol_reachability              true
% 7.77/1.49  --bmc1_property_lemmas                  false
% 7.77/1.49  --bmc1_k_induction                      false
% 7.77/1.49  --bmc1_non_equiv_states                 false
% 7.77/1.49  --bmc1_deadlock                         false
% 7.77/1.49  --bmc1_ucm                              false
% 7.77/1.49  --bmc1_add_unsat_core                   none
% 7.77/1.49  --bmc1_unsat_core_children              false
% 7.77/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.77/1.49  --bmc1_out_stat                         full
% 7.77/1.49  --bmc1_ground_init                      false
% 7.77/1.49  --bmc1_pre_inst_next_state              false
% 7.77/1.49  --bmc1_pre_inst_state                   false
% 7.77/1.49  --bmc1_pre_inst_reach_state             false
% 7.77/1.49  --bmc1_out_unsat_core                   false
% 7.77/1.49  --bmc1_aig_witness_out                  false
% 7.77/1.49  --bmc1_verbose                          false
% 7.77/1.49  --bmc1_dump_clauses_tptp                false
% 7.77/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.77/1.49  --bmc1_dump_file                        -
% 7.77/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.77/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.77/1.49  --bmc1_ucm_extend_mode                  1
% 7.77/1.49  --bmc1_ucm_init_mode                    2
% 7.77/1.49  --bmc1_ucm_cone_mode                    none
% 7.77/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.77/1.49  --bmc1_ucm_relax_model                  4
% 7.77/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.77/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.77/1.49  --bmc1_ucm_layered_model                none
% 7.77/1.49  --bmc1_ucm_max_lemma_size               10
% 7.77/1.49  
% 7.77/1.49  ------ AIG Options
% 7.77/1.49  
% 7.77/1.49  --aig_mode                              false
% 7.77/1.49  
% 7.77/1.49  ------ Instantiation Options
% 7.77/1.49  
% 7.77/1.49  --instantiation_flag                    true
% 7.77/1.49  --inst_sos_flag                         true
% 7.77/1.49  --inst_sos_phase                        true
% 7.77/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.77/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.77/1.49  --inst_lit_sel_side                     num_symb
% 7.77/1.49  --inst_solver_per_active                1400
% 7.77/1.49  --inst_solver_calls_frac                1.
% 7.77/1.49  --inst_passive_queue_type               priority_queues
% 7.77/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.77/1.49  --inst_passive_queues_freq              [25;2]
% 7.77/1.49  --inst_dismatching                      true
% 7.77/1.49  --inst_eager_unprocessed_to_passive     true
% 7.77/1.49  --inst_prop_sim_given                   true
% 7.77/1.49  --inst_prop_sim_new                     false
% 7.77/1.49  --inst_subs_new                         false
% 7.77/1.49  --inst_eq_res_simp                      false
% 7.77/1.49  --inst_subs_given                       false
% 7.77/1.49  --inst_orphan_elimination               true
% 7.77/1.49  --inst_learning_loop_flag               true
% 7.77/1.49  --inst_learning_start                   3000
% 7.77/1.49  --inst_learning_factor                  2
% 7.77/1.49  --inst_start_prop_sim_after_learn       3
% 7.77/1.49  --inst_sel_renew                        solver
% 7.77/1.49  --inst_lit_activity_flag                true
% 7.77/1.49  --inst_restr_to_given                   false
% 7.77/1.49  --inst_activity_threshold               500
% 7.77/1.49  --inst_out_proof                        true
% 7.77/1.49  
% 7.77/1.49  ------ Resolution Options
% 7.77/1.49  
% 7.77/1.49  --resolution_flag                       true
% 7.77/1.49  --res_lit_sel                           adaptive
% 7.77/1.49  --res_lit_sel_side                      none
% 7.77/1.49  --res_ordering                          kbo
% 7.77/1.49  --res_to_prop_solver                    active
% 7.77/1.49  --res_prop_simpl_new                    false
% 7.77/1.49  --res_prop_simpl_given                  true
% 7.77/1.49  --res_passive_queue_type                priority_queues
% 7.77/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.77/1.49  --res_passive_queues_freq               [15;5]
% 7.77/1.49  --res_forward_subs                      full
% 7.77/1.49  --res_backward_subs                     full
% 7.77/1.49  --res_forward_subs_resolution           true
% 7.77/1.49  --res_backward_subs_resolution          true
% 7.77/1.49  --res_orphan_elimination                true
% 7.77/1.49  --res_time_limit                        2.
% 7.77/1.49  --res_out_proof                         true
% 7.77/1.49  
% 7.77/1.49  ------ Superposition Options
% 7.77/1.49  
% 7.77/1.49  --superposition_flag                    true
% 7.77/1.49  --sup_passive_queue_type                priority_queues
% 7.77/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.77/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.77/1.49  --demod_completeness_check              fast
% 7.77/1.49  --demod_use_ground                      true
% 7.77/1.49  --sup_to_prop_solver                    passive
% 7.77/1.49  --sup_prop_simpl_new                    true
% 7.77/1.49  --sup_prop_simpl_given                  true
% 7.77/1.49  --sup_fun_splitting                     true
% 7.77/1.49  --sup_smt_interval                      50000
% 7.77/1.49  
% 7.77/1.49  ------ Superposition Simplification Setup
% 7.77/1.49  
% 7.77/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.77/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.77/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.77/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.77/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.77/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.77/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.77/1.49  --sup_immed_triv                        [TrivRules]
% 7.77/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.77/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.77/1.49  --sup_immed_bw_main                     []
% 7.77/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.77/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.77/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.77/1.49  --sup_input_bw                          []
% 7.77/1.49  
% 7.77/1.49  ------ Combination Options
% 7.77/1.49  
% 7.77/1.49  --comb_res_mult                         3
% 7.77/1.49  --comb_sup_mult                         2
% 7.77/1.49  --comb_inst_mult                        10
% 7.77/1.49  
% 7.77/1.49  ------ Debug Options
% 7.77/1.49  
% 7.77/1.49  --dbg_backtrace                         false
% 7.77/1.49  --dbg_dump_prop_clauses                 false
% 7.77/1.49  --dbg_dump_prop_clauses_file            -
% 7.77/1.49  --dbg_out_stat                          false
% 7.77/1.49  ------ Parsing...
% 7.77/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.77/1.49  
% 7.77/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.77/1.49  
% 7.77/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.77/1.49  
% 7.77/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.77/1.49  ------ Proving...
% 7.77/1.49  ------ Problem Properties 
% 7.77/1.49  
% 7.77/1.49  
% 7.77/1.49  clauses                                 35
% 7.77/1.49  conjectures                             11
% 7.77/1.49  EPR                                     9
% 7.77/1.49  Horn                                    35
% 7.77/1.49  unary                                   17
% 7.77/1.49  binary                                  5
% 7.77/1.49  lits                                    97
% 7.77/1.49  lits eq                                 23
% 7.77/1.49  fd_pure                                 0
% 7.77/1.49  fd_pseudo                               0
% 7.77/1.49  fd_cond                                 0
% 7.77/1.49  fd_pseudo_cond                          2
% 7.77/1.49  AC symbols                              0
% 7.77/1.49  
% 7.77/1.49  ------ Schedule dynamic 5 is on 
% 7.77/1.49  
% 7.77/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.77/1.49  
% 7.77/1.49  
% 7.77/1.49  ------ 
% 7.77/1.49  Current options:
% 7.77/1.49  ------ 
% 7.77/1.49  
% 7.77/1.49  ------ Input Options
% 7.77/1.49  
% 7.77/1.49  --out_options                           all
% 7.77/1.49  --tptp_safe_out                         true
% 7.77/1.49  --problem_path                          ""
% 7.77/1.49  --include_path                          ""
% 7.77/1.49  --clausifier                            res/vclausify_rel
% 7.77/1.49  --clausifier_options                    ""
% 7.77/1.49  --stdin                                 false
% 7.77/1.49  --stats_out                             all
% 7.77/1.49  
% 7.77/1.49  ------ General Options
% 7.77/1.49  
% 7.77/1.49  --fof                                   false
% 7.77/1.49  --time_out_real                         305.
% 7.77/1.49  --time_out_virtual                      -1.
% 7.77/1.49  --symbol_type_check                     false
% 7.77/1.49  --clausify_out                          false
% 7.77/1.49  --sig_cnt_out                           false
% 7.77/1.49  --trig_cnt_out                          false
% 7.77/1.49  --trig_cnt_out_tolerance                1.
% 7.77/1.49  --trig_cnt_out_sk_spl                   false
% 7.77/1.49  --abstr_cl_out                          false
% 7.77/1.49  
% 7.77/1.49  ------ Global Options
% 7.77/1.49  
% 7.77/1.49  --schedule                              default
% 7.77/1.49  --add_important_lit                     false
% 7.77/1.49  --prop_solver_per_cl                    1000
% 7.77/1.49  --min_unsat_core                        false
% 7.77/1.49  --soft_assumptions                      false
% 7.77/1.49  --soft_lemma_size                       3
% 7.77/1.49  --prop_impl_unit_size                   0
% 7.77/1.49  --prop_impl_unit                        []
% 7.77/1.49  --share_sel_clauses                     true
% 7.77/1.49  --reset_solvers                         false
% 7.77/1.49  --bc_imp_inh                            [conj_cone]
% 7.77/1.49  --conj_cone_tolerance                   3.
% 7.77/1.49  --extra_neg_conj                        none
% 7.77/1.49  --large_theory_mode                     true
% 7.77/1.49  --prolific_symb_bound                   200
% 7.77/1.49  --lt_threshold                          2000
% 7.77/1.49  --clause_weak_htbl                      true
% 7.77/1.49  --gc_record_bc_elim                     false
% 7.77/1.49  
% 7.77/1.49  ------ Preprocessing Options
% 7.77/1.49  
% 7.77/1.49  --preprocessing_flag                    true
% 7.77/1.49  --time_out_prep_mult                    0.1
% 7.77/1.49  --splitting_mode                        input
% 7.77/1.49  --splitting_grd                         true
% 7.77/1.49  --splitting_cvd                         false
% 7.77/1.49  --splitting_cvd_svl                     false
% 7.77/1.49  --splitting_nvd                         32
% 7.77/1.49  --sub_typing                            true
% 7.77/1.49  --prep_gs_sim                           true
% 7.77/1.49  --prep_unflatten                        true
% 7.77/1.49  --prep_res_sim                          true
% 7.77/1.49  --prep_upred                            true
% 7.77/1.49  --prep_sem_filter                       exhaustive
% 7.77/1.49  --prep_sem_filter_out                   false
% 7.77/1.49  --pred_elim                             true
% 7.77/1.49  --res_sim_input                         true
% 7.77/1.49  --eq_ax_congr_red                       true
% 7.77/1.49  --pure_diseq_elim                       true
% 7.77/1.49  --brand_transform                       false
% 7.77/1.49  --non_eq_to_eq                          false
% 7.77/1.49  --prep_def_merge                        true
% 7.77/1.49  --prep_def_merge_prop_impl              false
% 7.77/1.49  --prep_def_merge_mbd                    true
% 7.77/1.49  --prep_def_merge_tr_red                 false
% 7.77/1.49  --prep_def_merge_tr_cl                  false
% 7.77/1.49  --smt_preprocessing                     true
% 7.77/1.49  --smt_ac_axioms                         fast
% 7.77/1.49  --preprocessed_out                      false
% 7.77/1.49  --preprocessed_stats                    false
% 7.77/1.49  
% 7.77/1.49  ------ Abstraction refinement Options
% 7.77/1.49  
% 7.77/1.49  --abstr_ref                             []
% 7.77/1.49  --abstr_ref_prep                        false
% 7.77/1.49  --abstr_ref_until_sat                   false
% 7.77/1.49  --abstr_ref_sig_restrict                funpre
% 7.77/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.77/1.49  --abstr_ref_under                       []
% 7.77/1.49  
% 7.77/1.49  ------ SAT Options
% 7.77/1.49  
% 7.77/1.49  --sat_mode                              false
% 7.77/1.49  --sat_fm_restart_options                ""
% 7.77/1.49  --sat_gr_def                            false
% 7.77/1.49  --sat_epr_types                         true
% 7.77/1.49  --sat_non_cyclic_types                  false
% 7.77/1.49  --sat_finite_models                     false
% 7.77/1.49  --sat_fm_lemmas                         false
% 7.77/1.49  --sat_fm_prep                           false
% 7.77/1.49  --sat_fm_uc_incr                        true
% 7.77/1.49  --sat_out_model                         small
% 7.77/1.49  --sat_out_clauses                       false
% 7.77/1.49  
% 7.77/1.49  ------ QBF Options
% 7.77/1.49  
% 7.77/1.49  --qbf_mode                              false
% 7.77/1.49  --qbf_elim_univ                         false
% 7.77/1.49  --qbf_dom_inst                          none
% 7.77/1.49  --qbf_dom_pre_inst                      false
% 7.77/1.49  --qbf_sk_in                             false
% 7.77/1.49  --qbf_pred_elim                         true
% 7.77/1.49  --qbf_split                             512
% 7.77/1.49  
% 7.77/1.49  ------ BMC1 Options
% 7.77/1.49  
% 7.77/1.49  --bmc1_incremental                      false
% 7.77/1.49  --bmc1_axioms                           reachable_all
% 7.77/1.49  --bmc1_min_bound                        0
% 7.77/1.49  --bmc1_max_bound                        -1
% 7.77/1.49  --bmc1_max_bound_default                -1
% 7.77/1.49  --bmc1_symbol_reachability              true
% 7.77/1.49  --bmc1_property_lemmas                  false
% 7.77/1.49  --bmc1_k_induction                      false
% 7.77/1.49  --bmc1_non_equiv_states                 false
% 7.77/1.49  --bmc1_deadlock                         false
% 7.77/1.49  --bmc1_ucm                              false
% 7.77/1.49  --bmc1_add_unsat_core                   none
% 7.77/1.49  --bmc1_unsat_core_children              false
% 7.77/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.77/1.49  --bmc1_out_stat                         full
% 7.77/1.49  --bmc1_ground_init                      false
% 7.77/1.49  --bmc1_pre_inst_next_state              false
% 7.77/1.49  --bmc1_pre_inst_state                   false
% 7.77/1.49  --bmc1_pre_inst_reach_state             false
% 7.77/1.49  --bmc1_out_unsat_core                   false
% 7.77/1.49  --bmc1_aig_witness_out                  false
% 7.77/1.49  --bmc1_verbose                          false
% 7.77/1.49  --bmc1_dump_clauses_tptp                false
% 7.77/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.77/1.49  --bmc1_dump_file                        -
% 7.77/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.77/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.77/1.49  --bmc1_ucm_extend_mode                  1
% 7.77/1.49  --bmc1_ucm_init_mode                    2
% 7.77/1.49  --bmc1_ucm_cone_mode                    none
% 7.77/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.77/1.49  --bmc1_ucm_relax_model                  4
% 7.77/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.77/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.77/1.49  --bmc1_ucm_layered_model                none
% 7.77/1.49  --bmc1_ucm_max_lemma_size               10
% 7.77/1.49  
% 7.77/1.49  ------ AIG Options
% 7.77/1.49  
% 7.77/1.49  --aig_mode                              false
% 7.77/1.49  
% 7.77/1.49  ------ Instantiation Options
% 7.77/1.49  
% 7.77/1.49  --instantiation_flag                    true
% 7.77/1.49  --inst_sos_flag                         true
% 7.77/1.49  --inst_sos_phase                        true
% 7.77/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.77/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.77/1.49  --inst_lit_sel_side                     none
% 7.77/1.49  --inst_solver_per_active                1400
% 7.77/1.49  --inst_solver_calls_frac                1.
% 7.77/1.49  --inst_passive_queue_type               priority_queues
% 7.77/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.77/1.49  --inst_passive_queues_freq              [25;2]
% 7.77/1.49  --inst_dismatching                      true
% 7.77/1.49  --inst_eager_unprocessed_to_passive     true
% 7.77/1.49  --inst_prop_sim_given                   true
% 7.77/1.49  --inst_prop_sim_new                     false
% 7.77/1.49  --inst_subs_new                         false
% 7.77/1.49  --inst_eq_res_simp                      false
% 7.77/1.49  --inst_subs_given                       false
% 7.77/1.49  --inst_orphan_elimination               true
% 7.77/1.49  --inst_learning_loop_flag               true
% 7.77/1.49  --inst_learning_start                   3000
% 7.77/1.49  --inst_learning_factor                  2
% 7.77/1.49  --inst_start_prop_sim_after_learn       3
% 7.77/1.49  --inst_sel_renew                        solver
% 7.77/1.49  --inst_lit_activity_flag                true
% 7.77/1.49  --inst_restr_to_given                   false
% 7.77/1.49  --inst_activity_threshold               500
% 7.77/1.49  --inst_out_proof                        true
% 7.77/1.49  
% 7.77/1.49  ------ Resolution Options
% 7.77/1.49  
% 7.77/1.49  --resolution_flag                       false
% 7.77/1.49  --res_lit_sel                           adaptive
% 7.77/1.49  --res_lit_sel_side                      none
% 7.77/1.49  --res_ordering                          kbo
% 7.77/1.49  --res_to_prop_solver                    active
% 7.77/1.49  --res_prop_simpl_new                    false
% 7.77/1.49  --res_prop_simpl_given                  true
% 7.77/1.49  --res_passive_queue_type                priority_queues
% 7.77/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.77/1.49  --res_passive_queues_freq               [15;5]
% 7.77/1.49  --res_forward_subs                      full
% 7.77/1.49  --res_backward_subs                     full
% 7.77/1.49  --res_forward_subs_resolution           true
% 7.77/1.49  --res_backward_subs_resolution          true
% 7.77/1.49  --res_orphan_elimination                true
% 7.77/1.49  --res_time_limit                        2.
% 7.77/1.49  --res_out_proof                         true
% 7.77/1.49  
% 7.77/1.49  ------ Superposition Options
% 7.77/1.49  
% 7.77/1.49  --superposition_flag                    true
% 7.77/1.49  --sup_passive_queue_type                priority_queues
% 7.77/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.77/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.77/1.49  --demod_completeness_check              fast
% 7.77/1.49  --demod_use_ground                      true
% 7.77/1.49  --sup_to_prop_solver                    passive
% 7.77/1.49  --sup_prop_simpl_new                    true
% 7.77/1.49  --sup_prop_simpl_given                  true
% 7.77/1.49  --sup_fun_splitting                     true
% 7.77/1.49  --sup_smt_interval                      50000
% 7.77/1.49  
% 7.77/1.49  ------ Superposition Simplification Setup
% 7.77/1.49  
% 7.77/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.77/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.77/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.77/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.77/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.77/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.77/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.77/1.49  --sup_immed_triv                        [TrivRules]
% 7.77/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.77/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.77/1.49  --sup_immed_bw_main                     []
% 7.77/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.77/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.77/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.77/1.49  --sup_input_bw                          []
% 7.77/1.49  
% 7.77/1.49  ------ Combination Options
% 7.77/1.49  
% 7.77/1.49  --comb_res_mult                         3
% 7.77/1.49  --comb_sup_mult                         2
% 7.77/1.49  --comb_inst_mult                        10
% 7.77/1.49  
% 7.77/1.49  ------ Debug Options
% 7.77/1.49  
% 7.77/1.49  --dbg_backtrace                         false
% 7.77/1.49  --dbg_dump_prop_clauses                 false
% 7.77/1.49  --dbg_dump_prop_clauses_file            -
% 7.77/1.49  --dbg_out_stat                          false
% 7.77/1.49  
% 7.77/1.49  
% 7.77/1.49  
% 7.77/1.49  
% 7.77/1.49  ------ Proving...
% 7.77/1.49  
% 7.77/1.49  
% 7.77/1.49  % SZS status Theorem for theBenchmark.p
% 7.77/1.49  
% 7.77/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.77/1.49  
% 7.77/1.49  fof(f21,conjecture,(
% 7.77/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 7.77/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.49  
% 7.77/1.49  fof(f22,negated_conjecture,(
% 7.77/1.49    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 7.77/1.49    inference(negated_conjecture,[],[f21])).
% 7.77/1.49  
% 7.77/1.49  fof(f47,plain,(
% 7.77/1.49    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 7.77/1.49    inference(ennf_transformation,[],[f22])).
% 7.77/1.49  
% 7.77/1.49  fof(f48,plain,(
% 7.77/1.49    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 7.77/1.49    inference(flattening,[],[f47])).
% 7.77/1.49  
% 7.77/1.49  fof(f54,plain,(
% 7.77/1.49    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 7.77/1.49    introduced(choice_axiom,[])).
% 7.77/1.49  
% 7.77/1.49  fof(f53,plain,(
% 7.77/1.49    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 7.77/1.49    introduced(choice_axiom,[])).
% 7.77/1.49  
% 7.77/1.49  fof(f55,plain,(
% 7.77/1.49    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 7.77/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f48,f54,f53])).
% 7.77/1.49  
% 7.77/1.49  fof(f89,plain,(
% 7.77/1.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 7.77/1.49    inference(cnf_transformation,[],[f55])).
% 7.77/1.49  
% 7.77/1.49  fof(f13,axiom,(
% 7.77/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.77/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.49  
% 7.77/1.49  fof(f23,plain,(
% 7.77/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 7.77/1.49    inference(pure_predicate_removal,[],[f13])).
% 7.77/1.49  
% 7.77/1.49  fof(f37,plain,(
% 7.77/1.49    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.77/1.49    inference(ennf_transformation,[],[f23])).
% 7.77/1.49  
% 7.77/1.49  fof(f74,plain,(
% 7.77/1.49    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.77/1.49    inference(cnf_transformation,[],[f37])).
% 7.77/1.49  
% 7.77/1.49  fof(f2,axiom,(
% 7.77/1.49    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 7.77/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.49  
% 7.77/1.49  fof(f24,plain,(
% 7.77/1.49    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.77/1.49    inference(ennf_transformation,[],[f2])).
% 7.77/1.49  
% 7.77/1.49  fof(f51,plain,(
% 7.77/1.49    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.77/1.49    inference(nnf_transformation,[],[f24])).
% 7.77/1.49  
% 7.77/1.49  fof(f59,plain,(
% 7.77/1.49    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.77/1.49    inference(cnf_transformation,[],[f51])).
% 7.77/1.49  
% 7.77/1.49  fof(f12,axiom,(
% 7.77/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.77/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.49  
% 7.77/1.49  fof(f36,plain,(
% 7.77/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.77/1.49    inference(ennf_transformation,[],[f12])).
% 7.77/1.49  
% 7.77/1.49  fof(f73,plain,(
% 7.77/1.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.77/1.49    inference(cnf_transformation,[],[f36])).
% 7.77/1.49  
% 7.77/1.49  fof(f86,plain,(
% 7.77/1.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 7.77/1.49    inference(cnf_transformation,[],[f55])).
% 7.77/1.49  
% 7.77/1.49  fof(f14,axiom,(
% 7.77/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 7.77/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.49  
% 7.77/1.49  fof(f38,plain,(
% 7.77/1.49    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.77/1.49    inference(ennf_transformation,[],[f14])).
% 7.77/1.49  
% 7.77/1.49  fof(f75,plain,(
% 7.77/1.49    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.77/1.49    inference(cnf_transformation,[],[f38])).
% 7.77/1.49  
% 7.77/1.49  fof(f90,plain,(
% 7.77/1.49    k2_relset_1(sK0,sK1,sK2) = sK1),
% 7.77/1.49    inference(cnf_transformation,[],[f55])).
% 7.77/1.49  
% 7.77/1.49  fof(f8,axiom,(
% 7.77/1.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 7.77/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.49  
% 7.77/1.49  fof(f28,plain,(
% 7.77/1.49    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 7.77/1.49    inference(ennf_transformation,[],[f8])).
% 7.77/1.49  
% 7.77/1.49  fof(f29,plain,(
% 7.77/1.49    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.77/1.49    inference(flattening,[],[f28])).
% 7.77/1.49  
% 7.77/1.49  fof(f68,plain,(
% 7.77/1.49    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.77/1.49    inference(cnf_transformation,[],[f29])).
% 7.77/1.49  
% 7.77/1.49  fof(f84,plain,(
% 7.77/1.49    v1_funct_1(sK2)),
% 7.77/1.49    inference(cnf_transformation,[],[f55])).
% 7.77/1.49  
% 7.77/1.49  fof(f4,axiom,(
% 7.77/1.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 7.77/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.49  
% 7.77/1.49  fof(f26,plain,(
% 7.77/1.49    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.77/1.49    inference(ennf_transformation,[],[f4])).
% 7.77/1.49  
% 7.77/1.49  fof(f62,plain,(
% 7.77/1.49    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.77/1.49    inference(cnf_transformation,[],[f26])).
% 7.77/1.49  
% 7.77/1.49  fof(f18,axiom,(
% 7.77/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 7.77/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.49  
% 7.77/1.49  fof(f43,plain,(
% 7.77/1.49    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 7.77/1.49    inference(ennf_transformation,[],[f18])).
% 7.77/1.49  
% 7.77/1.49  fof(f44,plain,(
% 7.77/1.49    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 7.77/1.49    inference(flattening,[],[f43])).
% 7.77/1.49  
% 7.77/1.49  fof(f81,plain,(
% 7.77/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 7.77/1.49    inference(cnf_transformation,[],[f44])).
% 7.77/1.49  
% 7.77/1.49  fof(f87,plain,(
% 7.77/1.49    v1_funct_1(sK3)),
% 7.77/1.49    inference(cnf_transformation,[],[f55])).
% 7.77/1.49  
% 7.77/1.49  fof(f15,axiom,(
% 7.77/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 7.77/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.49  
% 7.77/1.49  fof(f39,plain,(
% 7.77/1.49    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 7.77/1.49    inference(ennf_transformation,[],[f15])).
% 7.77/1.49  
% 7.77/1.49  fof(f40,plain,(
% 7.77/1.49    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.77/1.49    inference(flattening,[],[f39])).
% 7.77/1.49  
% 7.77/1.49  fof(f52,plain,(
% 7.77/1.49    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.77/1.49    inference(nnf_transformation,[],[f40])).
% 7.77/1.49  
% 7.77/1.49  fof(f76,plain,(
% 7.77/1.49    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.77/1.49    inference(cnf_transformation,[],[f52])).
% 7.77/1.49  
% 7.77/1.49  fof(f91,plain,(
% 7.77/1.49    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 7.77/1.49    inference(cnf_transformation,[],[f55])).
% 7.77/1.49  
% 7.77/1.49  fof(f16,axiom,(
% 7.77/1.49    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 7.77/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.49  
% 7.77/1.49  fof(f78,plain,(
% 7.77/1.49    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 7.77/1.49    inference(cnf_transformation,[],[f16])).
% 7.77/1.49  
% 7.77/1.49  fof(f19,axiom,(
% 7.77/1.49    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 7.77/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.49  
% 7.77/1.49  fof(f82,plain,(
% 7.77/1.49    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 7.77/1.49    inference(cnf_transformation,[],[f19])).
% 7.77/1.49  
% 7.77/1.49  fof(f101,plain,(
% 7.77/1.49    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 7.77/1.49    inference(definition_unfolding,[],[f78,f82])).
% 7.77/1.49  
% 7.77/1.49  fof(f17,axiom,(
% 7.77/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 7.77/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.49  
% 7.77/1.49  fof(f41,plain,(
% 7.77/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 7.77/1.49    inference(ennf_transformation,[],[f17])).
% 7.77/1.49  
% 7.77/1.49  fof(f42,plain,(
% 7.77/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 7.77/1.49    inference(flattening,[],[f41])).
% 7.77/1.49  
% 7.77/1.49  fof(f80,plain,(
% 7.77/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 7.77/1.49    inference(cnf_transformation,[],[f42])).
% 7.77/1.49  
% 7.77/1.49  fof(f6,axiom,(
% 7.77/1.49    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 7.77/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.49  
% 7.77/1.49  fof(f64,plain,(
% 7.77/1.49    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 7.77/1.49    inference(cnf_transformation,[],[f6])).
% 7.77/1.49  
% 7.77/1.49  fof(f97,plain,(
% 7.77/1.49    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 7.77/1.49    inference(definition_unfolding,[],[f64,f82])).
% 7.77/1.49  
% 7.77/1.49  fof(f5,axiom,(
% 7.77/1.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 7.77/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.49  
% 7.77/1.49  fof(f27,plain,(
% 7.77/1.49    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.77/1.49    inference(ennf_transformation,[],[f5])).
% 7.77/1.49  
% 7.77/1.49  fof(f63,plain,(
% 7.77/1.49    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.77/1.49    inference(cnf_transformation,[],[f27])).
% 7.77/1.49  
% 7.77/1.49  fof(f1,axiom,(
% 7.77/1.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.77/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.49  
% 7.77/1.49  fof(f49,plain,(
% 7.77/1.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.77/1.49    inference(nnf_transformation,[],[f1])).
% 7.77/1.49  
% 7.77/1.49  fof(f50,plain,(
% 7.77/1.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.77/1.49    inference(flattening,[],[f49])).
% 7.77/1.49  
% 7.77/1.49  fof(f58,plain,(
% 7.77/1.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.77/1.49    inference(cnf_transformation,[],[f50])).
% 7.77/1.49  
% 7.77/1.49  fof(f3,axiom,(
% 7.77/1.49    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 7.77/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.49  
% 7.77/1.49  fof(f25,plain,(
% 7.77/1.49    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 7.77/1.49    inference(ennf_transformation,[],[f3])).
% 7.77/1.49  
% 7.77/1.49  fof(f61,plain,(
% 7.77/1.49    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 7.77/1.49    inference(cnf_transformation,[],[f25])).
% 7.77/1.49  
% 7.77/1.49  fof(f9,axiom,(
% 7.77/1.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 7.77/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.49  
% 7.77/1.49  fof(f30,plain,(
% 7.77/1.49    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.77/1.49    inference(ennf_transformation,[],[f9])).
% 7.77/1.49  
% 7.77/1.49  fof(f31,plain,(
% 7.77/1.49    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.77/1.49    inference(flattening,[],[f30])).
% 7.77/1.49  
% 7.77/1.49  fof(f70,plain,(
% 7.77/1.49    ( ! [X0,X1] : (v2_funct_1(X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.77/1.49    inference(cnf_transformation,[],[f31])).
% 7.77/1.49  
% 7.77/1.49  fof(f10,axiom,(
% 7.77/1.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 7.77/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.49  
% 7.77/1.49  fof(f32,plain,(
% 7.77/1.49    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.77/1.49    inference(ennf_transformation,[],[f10])).
% 7.77/1.49  
% 7.77/1.49  fof(f33,plain,(
% 7.77/1.49    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.77/1.49    inference(flattening,[],[f32])).
% 7.77/1.49  
% 7.77/1.49  fof(f71,plain,(
% 7.77/1.49    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.77/1.49    inference(cnf_transformation,[],[f33])).
% 7.77/1.49  
% 7.77/1.49  fof(f100,plain,(
% 7.77/1.49    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.77/1.49    inference(definition_unfolding,[],[f71,f82])).
% 7.77/1.49  
% 7.77/1.49  fof(f20,axiom,(
% 7.77/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 7.77/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.49  
% 7.77/1.49  fof(f45,plain,(
% 7.77/1.49    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 7.77/1.49    inference(ennf_transformation,[],[f20])).
% 7.77/1.49  
% 7.77/1.49  fof(f46,plain,(
% 7.77/1.49    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.77/1.49    inference(flattening,[],[f45])).
% 7.77/1.49  
% 7.77/1.49  fof(f83,plain,(
% 7.77/1.49    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.77/1.49    inference(cnf_transformation,[],[f46])).
% 7.77/1.49  
% 7.77/1.49  fof(f85,plain,(
% 7.77/1.49    v1_funct_2(sK2,sK0,sK1)),
% 7.77/1.49    inference(cnf_transformation,[],[f55])).
% 7.77/1.49  
% 7.77/1.49  fof(f88,plain,(
% 7.77/1.49    v1_funct_2(sK3,sK1,sK0)),
% 7.77/1.49    inference(cnf_transformation,[],[f55])).
% 7.77/1.49  
% 7.77/1.49  fof(f11,axiom,(
% 7.77/1.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 7.77/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.49  
% 7.77/1.49  fof(f34,plain,(
% 7.77/1.49    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.77/1.49    inference(ennf_transformation,[],[f11])).
% 7.77/1.49  
% 7.77/1.49  fof(f35,plain,(
% 7.77/1.49    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.77/1.49    inference(flattening,[],[f34])).
% 7.77/1.49  
% 7.77/1.49  fof(f72,plain,(
% 7.77/1.49    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.77/1.49    inference(cnf_transformation,[],[f35])).
% 7.77/1.49  
% 7.77/1.49  fof(f57,plain,(
% 7.77/1.49    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 7.77/1.49    inference(cnf_transformation,[],[f50])).
% 7.77/1.49  
% 7.77/1.49  fof(f102,plain,(
% 7.77/1.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.77/1.49    inference(equality_resolution,[],[f57])).
% 7.77/1.49  
% 7.77/1.49  fof(f7,axiom,(
% 7.77/1.49    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 7.77/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.49  
% 7.77/1.49  fof(f67,plain,(
% 7.77/1.49    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 7.77/1.49    inference(cnf_transformation,[],[f7])).
% 7.77/1.49  
% 7.77/1.49  fof(f98,plain,(
% 7.77/1.49    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 7.77/1.49    inference(definition_unfolding,[],[f67,f82])).
% 7.77/1.49  
% 7.77/1.49  fof(f95,plain,(
% 7.77/1.49    k2_funct_1(sK2) != sK3),
% 7.77/1.49    inference(cnf_transformation,[],[f55])).
% 7.77/1.49  
% 7.77/1.49  cnf(c_712,plain,
% 7.77/1.49      ( X0 != X1 | k2_funct_1(X0) = k2_funct_1(X1) ),
% 7.77/1.49      theory(equality) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_16528,plain,
% 7.77/1.49      ( k2_funct_1(sK2) = k2_funct_1(k2_funct_1(sK3))
% 7.77/1.49      | sK2 != k2_funct_1(sK3) ),
% 7.77/1.49      inference(instantiation,[status(thm)],[c_712]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_702,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_1278,plain,
% 7.77/1.49      ( k2_funct_1(sK2) != X0 | k2_funct_1(sK2) = sK3 | sK3 != X0 ),
% 7.77/1.49      inference(instantiation,[status(thm)],[c_702]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_13603,plain,
% 7.77/1.49      ( k2_funct_1(sK2) != k2_funct_1(k2_funct_1(sK3))
% 7.77/1.49      | k2_funct_1(sK2) = sK3
% 7.77/1.49      | sK3 != k2_funct_1(k2_funct_1(sK3)) ),
% 7.77/1.49      inference(instantiation,[status(thm)],[c_1278]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_1853,plain,
% 7.77/1.49      ( X0 != X1 | sK2 != X1 | sK2 = X0 ),
% 7.77/1.49      inference(instantiation,[status(thm)],[c_702]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_3332,plain,
% 7.77/1.49      ( X0 != sK2 | sK2 = X0 | sK2 != sK2 ),
% 7.77/1.49      inference(instantiation,[status(thm)],[c_1853]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_4382,plain,
% 7.77/1.49      ( k2_funct_1(X0) != sK2 | sK2 = k2_funct_1(X0) | sK2 != sK2 ),
% 7.77/1.49      inference(instantiation,[status(thm)],[c_3332]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_13102,plain,
% 7.77/1.49      ( k2_funct_1(sK3) != sK2 | sK2 = k2_funct_1(sK3) | sK2 != sK2 ),
% 7.77/1.49      inference(instantiation,[status(thm)],[c_4382]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_33,negated_conjecture,
% 7.77/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 7.77/1.49      inference(cnf_transformation,[],[f89]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_1214,plain,
% 7.77/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 7.77/1.49      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_18,plain,
% 7.77/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.77/1.49      | v4_relat_1(X0,X1) ),
% 7.77/1.49      inference(cnf_transformation,[],[f74]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_4,plain,
% 7.77/1.49      ( ~ v4_relat_1(X0,X1)
% 7.77/1.49      | r1_tarski(k1_relat_1(X0),X1)
% 7.77/1.49      | ~ v1_relat_1(X0) ),
% 7.77/1.49      inference(cnf_transformation,[],[f59]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_372,plain,
% 7.77/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.77/1.49      | r1_tarski(k1_relat_1(X0),X1)
% 7.77/1.49      | ~ v1_relat_1(X0) ),
% 7.77/1.49      inference(resolution,[status(thm)],[c_18,c_4]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_17,plain,
% 7.77/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.77/1.49      | v1_relat_1(X0) ),
% 7.77/1.49      inference(cnf_transformation,[],[f73]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_376,plain,
% 7.77/1.49      ( r1_tarski(k1_relat_1(X0),X1)
% 7.77/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.77/1.49      inference(global_propositional_subsumption,
% 7.77/1.49                [status(thm)],
% 7.77/1.49                [c_372,c_17]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_377,plain,
% 7.77/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.77/1.49      | r1_tarski(k1_relat_1(X0),X1) ),
% 7.77/1.49      inference(renaming,[status(thm)],[c_376]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_1208,plain,
% 7.77/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.77/1.49      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 7.77/1.49      inference(predicate_to_equality,[status(thm)],[c_377]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_2753,plain,
% 7.77/1.49      ( r1_tarski(k1_relat_1(sK3),sK1) = iProver_top ),
% 7.77/1.49      inference(superposition,[status(thm)],[c_1214,c_1208]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_36,negated_conjecture,
% 7.77/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 7.77/1.49      inference(cnf_transformation,[],[f86]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_1211,plain,
% 7.77/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.77/1.49      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_19,plain,
% 7.77/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.77/1.49      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 7.77/1.49      inference(cnf_transformation,[],[f75]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_1220,plain,
% 7.77/1.49      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 7.77/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.77/1.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_2250,plain,
% 7.77/1.49      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 7.77/1.49      inference(superposition,[status(thm)],[c_1211,c_1220]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_32,negated_conjecture,
% 7.77/1.49      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 7.77/1.49      inference(cnf_transformation,[],[f90]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_2251,plain,
% 7.77/1.49      ( k2_relat_1(sK2) = sK1 ),
% 7.77/1.49      inference(light_normalisation,[status(thm)],[c_2250,c_32]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_12,plain,
% 7.77/1.49      ( ~ r1_tarski(X0,k2_relat_1(X1))
% 7.77/1.49      | ~ v1_funct_1(X1)
% 7.77/1.49      | ~ v1_relat_1(X1)
% 7.77/1.49      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
% 7.77/1.49      inference(cnf_transformation,[],[f68]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_1226,plain,
% 7.77/1.49      ( k9_relat_1(X0,k10_relat_1(X0,X1)) = X1
% 7.77/1.49      | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
% 7.77/1.49      | v1_funct_1(X0) != iProver_top
% 7.77/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.77/1.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_4169,plain,
% 7.77/1.49      ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
% 7.77/1.49      | r1_tarski(X0,sK1) != iProver_top
% 7.77/1.49      | v1_funct_1(sK2) != iProver_top
% 7.77/1.49      | v1_relat_1(sK2) != iProver_top ),
% 7.77/1.49      inference(superposition,[status(thm)],[c_2251,c_1226]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_38,negated_conjecture,
% 7.77/1.49      ( v1_funct_1(sK2) ),
% 7.77/1.49      inference(cnf_transformation,[],[f84]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_39,plain,
% 7.77/1.49      ( v1_funct_1(sK2) = iProver_top ),
% 7.77/1.49      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_41,plain,
% 7.77/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.77/1.49      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_1626,plain,
% 7.77/1.49      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.77/1.49      | v1_relat_1(sK2) ),
% 7.77/1.49      inference(instantiation,[status(thm)],[c_17]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_1627,plain,
% 7.77/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.77/1.49      | v1_relat_1(sK2) = iProver_top ),
% 7.77/1.49      inference(predicate_to_equality,[status(thm)],[c_1626]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_4405,plain,
% 7.77/1.49      ( k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
% 7.77/1.49      | r1_tarski(X0,sK1) != iProver_top ),
% 7.77/1.49      inference(global_propositional_subsumption,
% 7.77/1.49                [status(thm)],
% 7.77/1.49                [c_4169,c_39,c_41,c_1627]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_4412,plain,
% 7.77/1.49      ( k9_relat_1(sK2,k10_relat_1(sK2,k1_relat_1(sK3))) = k1_relat_1(sK3) ),
% 7.77/1.49      inference(superposition,[status(thm)],[c_2753,c_4405]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_1221,plain,
% 7.77/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.77/1.49      | v1_relat_1(X0) = iProver_top ),
% 7.77/1.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_2243,plain,
% 7.77/1.49      ( v1_relat_1(sK3) = iProver_top ),
% 7.77/1.49      inference(superposition,[status(thm)],[c_1214,c_1221]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_2244,plain,
% 7.77/1.49      ( v1_relat_1(sK2) = iProver_top ),
% 7.77/1.49      inference(superposition,[status(thm)],[c_1211,c_1221]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_6,plain,
% 7.77/1.49      ( ~ v1_relat_1(X0)
% 7.77/1.49      | ~ v1_relat_1(X1)
% 7.77/1.49      | k10_relat_1(X1,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(X1,X0)) ),
% 7.77/1.49      inference(cnf_transformation,[],[f62]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_1230,plain,
% 7.77/1.49      ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
% 7.77/1.49      | v1_relat_1(X1) != iProver_top
% 7.77/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.77/1.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_2866,plain,
% 7.77/1.49      ( k10_relat_1(sK2,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(sK2,X0))
% 7.77/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.77/1.49      inference(superposition,[status(thm)],[c_2244,c_1230]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_3625,plain,
% 7.77/1.49      ( k10_relat_1(sK2,k1_relat_1(sK3)) = k1_relat_1(k5_relat_1(sK2,sK3)) ),
% 7.77/1.49      inference(superposition,[status(thm)],[c_2243,c_2866]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_4414,plain,
% 7.77/1.49      ( k9_relat_1(sK2,k1_relat_1(k5_relat_1(sK2,sK3))) = k1_relat_1(sK3) ),
% 7.77/1.49      inference(light_normalisation,[status(thm)],[c_4412,c_3625]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_25,plain,
% 7.77/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.77/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.77/1.49      | ~ v1_funct_1(X0)
% 7.77/1.49      | ~ v1_funct_1(X3)
% 7.77/1.49      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 7.77/1.49      inference(cnf_transformation,[],[f81]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_1216,plain,
% 7.77/1.49      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 7.77/1.49      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 7.77/1.49      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.77/1.49      | v1_funct_1(X4) != iProver_top
% 7.77/1.49      | v1_funct_1(X5) != iProver_top ),
% 7.77/1.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_4762,plain,
% 7.77/1.49      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 7.77/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.77/1.49      | v1_funct_1(X2) != iProver_top
% 7.77/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.77/1.49      inference(superposition,[status(thm)],[c_1214,c_1216]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_35,negated_conjecture,
% 7.77/1.49      ( v1_funct_1(sK3) ),
% 7.77/1.49      inference(cnf_transformation,[],[f87]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_42,plain,
% 7.77/1.49      ( v1_funct_1(sK3) = iProver_top ),
% 7.77/1.49      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_4883,plain,
% 7.77/1.49      ( v1_funct_1(X2) != iProver_top
% 7.77/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.77/1.49      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 7.77/1.49      inference(global_propositional_subsumption,
% 7.77/1.49                [status(thm)],
% 7.77/1.49                [c_4762,c_42]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_4884,plain,
% 7.77/1.49      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 7.77/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.77/1.49      | v1_funct_1(X2) != iProver_top ),
% 7.77/1.49      inference(renaming,[status(thm)],[c_4883]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_4892,plain,
% 7.77/1.49      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 7.77/1.49      | v1_funct_1(sK2) != iProver_top ),
% 7.77/1.49      inference(superposition,[status(thm)],[c_1211,c_4884]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_21,plain,
% 7.77/1.49      ( ~ r2_relset_1(X0,X1,X2,X3)
% 7.77/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.77/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.77/1.49      | X3 = X2 ),
% 7.77/1.49      inference(cnf_transformation,[],[f76]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_31,negated_conjecture,
% 7.77/1.49      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 7.77/1.49      inference(cnf_transformation,[],[f91]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_430,plain,
% 7.77/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.77/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.77/1.49      | X3 = X0
% 7.77/1.49      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 7.77/1.49      | k6_partfun1(sK0) != X3
% 7.77/1.49      | sK0 != X2
% 7.77/1.49      | sK0 != X1 ),
% 7.77/1.49      inference(resolution_lifted,[status(thm)],[c_21,c_31]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_431,plain,
% 7.77/1.49      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.77/1.49      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.77/1.49      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.77/1.49      inference(unflattening,[status(thm)],[c_430]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_22,plain,
% 7.77/1.49      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 7.77/1.49      inference(cnf_transformation,[],[f101]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_60,plain,
% 7.77/1.49      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 7.77/1.49      inference(instantiation,[status(thm)],[c_22]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_433,plain,
% 7.77/1.49      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.77/1.49      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.77/1.49      inference(global_propositional_subsumption,
% 7.77/1.49                [status(thm)],
% 7.77/1.49                [c_431,c_60]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_1206,plain,
% 7.77/1.49      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.77/1.49      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 7.77/1.49      inference(predicate_to_equality,[status(thm)],[c_433]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_23,plain,
% 7.77/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.77/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.77/1.49      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.77/1.49      | ~ v1_funct_1(X0)
% 7.77/1.49      | ~ v1_funct_1(X3) ),
% 7.77/1.49      inference(cnf_transformation,[],[f80]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_1288,plain,
% 7.77/1.49      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.77/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 7.77/1.49      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.77/1.49      | ~ v1_funct_1(sK3)
% 7.77/1.49      | ~ v1_funct_1(sK2) ),
% 7.77/1.49      inference(instantiation,[status(thm)],[c_23]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_1874,plain,
% 7.77/1.49      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.77/1.49      inference(global_propositional_subsumption,
% 7.77/1.49                [status(thm)],
% 7.77/1.49                [c_1206,c_38,c_36,c_35,c_33,c_60,c_431,c_1288]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_4893,plain,
% 7.77/1.49      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 7.77/1.49      | v1_funct_1(sK2) != iProver_top ),
% 7.77/1.49      inference(light_normalisation,[status(thm)],[c_4892,c_1874]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_5081,plain,
% 7.77/1.49      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 7.77/1.49      inference(global_propositional_subsumption,
% 7.77/1.49                [status(thm)],
% 7.77/1.49                [c_4893,c_39]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_11305,plain,
% 7.77/1.49      ( k9_relat_1(sK2,k1_relat_1(k6_partfun1(sK0))) = k1_relat_1(sK3) ),
% 7.77/1.49      inference(light_normalisation,[status(thm)],[c_4414,c_4414,c_5081]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_9,plain,
% 7.77/1.49      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 7.77/1.49      inference(cnf_transformation,[],[f97]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_7,plain,
% 7.77/1.49      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
% 7.77/1.49      | ~ v1_relat_1(X1)
% 7.77/1.49      | ~ v1_relat_1(X0) ),
% 7.77/1.49      inference(cnf_transformation,[],[f63]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_1229,plain,
% 7.77/1.49      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) = iProver_top
% 7.77/1.49      | v1_relat_1(X0) != iProver_top
% 7.77/1.49      | v1_relat_1(X1) != iProver_top ),
% 7.77/1.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_5086,plain,
% 7.77/1.49      ( r1_tarski(k1_relat_1(k6_partfun1(sK0)),k1_relat_1(sK2)) = iProver_top
% 7.77/1.49      | v1_relat_1(sK3) != iProver_top
% 7.77/1.49      | v1_relat_1(sK2) != iProver_top ),
% 7.77/1.49      inference(superposition,[status(thm)],[c_5081,c_1229]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_5087,plain,
% 7.77/1.49      ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top
% 7.77/1.49      | v1_relat_1(sK3) != iProver_top
% 7.77/1.49      | v1_relat_1(sK2) != iProver_top ),
% 7.77/1.49      inference(demodulation,[status(thm)],[c_5086,c_9]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_44,plain,
% 7.77/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 7.77/1.49      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_1323,plain,
% 7.77/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.77/1.49      | v1_relat_1(sK3) ),
% 7.77/1.49      inference(instantiation,[status(thm)],[c_17]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_1425,plain,
% 7.77/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 7.77/1.49      | v1_relat_1(sK3) ),
% 7.77/1.49      inference(instantiation,[status(thm)],[c_1323]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_1426,plain,
% 7.77/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.77/1.49      | v1_relat_1(sK3) = iProver_top ),
% 7.77/1.49      inference(predicate_to_equality,[status(thm)],[c_1425]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_5238,plain,
% 7.77/1.49      ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top ),
% 7.77/1.49      inference(global_propositional_subsumption,
% 7.77/1.49                [status(thm)],
% 7.77/1.49                [c_5087,c_41,c_44,c_1426,c_1627]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_2754,plain,
% 7.77/1.49      ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
% 7.77/1.49      inference(superposition,[status(thm)],[c_1211,c_1208]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_0,plain,
% 7.77/1.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.77/1.49      inference(cnf_transformation,[],[f58]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_1233,plain,
% 7.77/1.49      ( X0 = X1
% 7.77/1.49      | r1_tarski(X0,X1) != iProver_top
% 7.77/1.49      | r1_tarski(X1,X0) != iProver_top ),
% 7.77/1.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_3030,plain,
% 7.77/1.49      ( k1_relat_1(sK2) = sK0
% 7.77/1.49      | r1_tarski(sK0,k1_relat_1(sK2)) != iProver_top ),
% 7.77/1.49      inference(superposition,[status(thm)],[c_2754,c_1233]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_5244,plain,
% 7.77/1.49      ( k1_relat_1(sK2) = sK0 ),
% 7.77/1.49      inference(superposition,[status(thm)],[c_5238,c_3030]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_5,plain,
% 7.77/1.49      ( ~ v1_relat_1(X0)
% 7.77/1.49      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 7.77/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_1231,plain,
% 7.77/1.49      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
% 7.77/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.77/1.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_2485,plain,
% 7.77/1.49      ( k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
% 7.77/1.49      inference(superposition,[status(thm)],[c_2244,c_1231]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_2486,plain,
% 7.77/1.49      ( k9_relat_1(sK2,k1_relat_1(sK2)) = sK1 ),
% 7.77/1.49      inference(light_normalisation,[status(thm)],[c_2485,c_2251]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_7849,plain,
% 7.77/1.49      ( k9_relat_1(sK2,sK0) = sK1 ),
% 7.77/1.49      inference(demodulation,[status(thm)],[c_5244,c_2486]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_11306,plain,
% 7.77/1.49      ( k1_relat_1(sK3) = sK1 ),
% 7.77/1.49      inference(demodulation,[status(thm)],[c_11305,c_9,c_7849]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_13,plain,
% 7.77/1.49      ( ~ v1_funct_1(X0)
% 7.77/1.49      | ~ v1_funct_1(X1)
% 7.77/1.49      | v2_funct_1(X1)
% 7.77/1.49      | ~ v2_funct_1(k5_relat_1(X0,X1))
% 7.77/1.49      | ~ v1_relat_1(X0)
% 7.77/1.49      | ~ v1_relat_1(X1)
% 7.77/1.49      | k2_relat_1(X0) != k1_relat_1(X1) ),
% 7.77/1.49      inference(cnf_transformation,[],[f70]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_1225,plain,
% 7.77/1.49      ( k2_relat_1(X0) != k1_relat_1(X1)
% 7.77/1.49      | v1_funct_1(X0) != iProver_top
% 7.77/1.49      | v1_funct_1(X1) != iProver_top
% 7.77/1.49      | v2_funct_1(X1) = iProver_top
% 7.77/1.49      | v2_funct_1(k5_relat_1(X0,X1)) != iProver_top
% 7.77/1.49      | v1_relat_1(X0) != iProver_top
% 7.77/1.49      | v1_relat_1(X1) != iProver_top ),
% 7.77/1.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_4862,plain,
% 7.77/1.49      ( k1_relat_1(X0) != sK1
% 7.77/1.49      | v1_funct_1(X0) != iProver_top
% 7.77/1.49      | v1_funct_1(sK2) != iProver_top
% 7.77/1.49      | v2_funct_1(X0) = iProver_top
% 7.77/1.49      | v2_funct_1(k5_relat_1(sK2,X0)) != iProver_top
% 7.77/1.49      | v1_relat_1(X0) != iProver_top
% 7.77/1.49      | v1_relat_1(sK2) != iProver_top ),
% 7.77/1.49      inference(superposition,[status(thm)],[c_2251,c_1225]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_5065,plain,
% 7.77/1.49      ( v1_relat_1(X0) != iProver_top
% 7.77/1.49      | v2_funct_1(k5_relat_1(sK2,X0)) != iProver_top
% 7.77/1.49      | v2_funct_1(X0) = iProver_top
% 7.77/1.49      | k1_relat_1(X0) != sK1
% 7.77/1.49      | v1_funct_1(X0) != iProver_top ),
% 7.77/1.49      inference(global_propositional_subsumption,
% 7.77/1.49                [status(thm)],
% 7.77/1.49                [c_4862,c_39,c_41,c_1627]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_5066,plain,
% 7.77/1.49      ( k1_relat_1(X0) != sK1
% 7.77/1.49      | v1_funct_1(X0) != iProver_top
% 7.77/1.49      | v2_funct_1(X0) = iProver_top
% 7.77/1.49      | v2_funct_1(k5_relat_1(sK2,X0)) != iProver_top
% 7.77/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.77/1.49      inference(renaming,[status(thm)],[c_5065]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_11324,plain,
% 7.77/1.49      ( v1_funct_1(sK3) != iProver_top
% 7.77/1.49      | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
% 7.77/1.49      | v2_funct_1(sK3) = iProver_top
% 7.77/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.77/1.49      inference(superposition,[status(thm)],[c_11306,c_5066]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_11326,plain,
% 7.77/1.49      ( v1_funct_1(sK3) != iProver_top
% 7.77/1.49      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 7.77/1.49      | v2_funct_1(sK3) = iProver_top
% 7.77/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.77/1.49      inference(light_normalisation,[status(thm)],[c_11324,c_5081]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_15,plain,
% 7.77/1.49      ( ~ v1_funct_1(X0)
% 7.77/1.49      | ~ v1_funct_1(X1)
% 7.77/1.49      | ~ v2_funct_1(X1)
% 7.77/1.49      | ~ v1_relat_1(X0)
% 7.77/1.49      | ~ v1_relat_1(X1)
% 7.77/1.49      | k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 7.77/1.49      | k2_funct_1(X1) = X0
% 7.77/1.49      | k2_relat_1(X0) != k1_relat_1(X1) ),
% 7.77/1.49      inference(cnf_transformation,[],[f100]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_1223,plain,
% 7.77/1.49      ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 7.77/1.49      | k2_funct_1(X1) = X0
% 7.77/1.49      | k2_relat_1(X0) != k1_relat_1(X1)
% 7.77/1.49      | v1_funct_1(X0) != iProver_top
% 7.77/1.49      | v1_funct_1(X1) != iProver_top
% 7.77/1.49      | v2_funct_1(X1) != iProver_top
% 7.77/1.49      | v1_relat_1(X0) != iProver_top
% 7.77/1.49      | v1_relat_1(X1) != iProver_top ),
% 7.77/1.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_5085,plain,
% 7.77/1.49      ( k2_funct_1(sK3) = sK2
% 7.77/1.49      | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
% 7.77/1.49      | k2_relat_1(sK2) != k1_relat_1(sK3)
% 7.77/1.49      | v1_funct_1(sK3) != iProver_top
% 7.77/1.49      | v1_funct_1(sK2) != iProver_top
% 7.77/1.49      | v2_funct_1(sK3) != iProver_top
% 7.77/1.49      | v1_relat_1(sK3) != iProver_top
% 7.77/1.49      | v1_relat_1(sK2) != iProver_top ),
% 7.77/1.49      inference(superposition,[status(thm)],[c_5081,c_1223]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_2249,plain,
% 7.77/1.49      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 7.77/1.49      inference(superposition,[status(thm)],[c_1214,c_1220]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_26,plain,
% 7.77/1.49      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 7.77/1.49      | ~ v1_funct_2(X2,X0,X1)
% 7.77/1.49      | ~ v1_funct_2(X3,X1,X0)
% 7.77/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 7.77/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.77/1.49      | ~ v1_funct_1(X2)
% 7.77/1.49      | ~ v1_funct_1(X3)
% 7.77/1.49      | k2_relset_1(X1,X0,X3) = X0 ),
% 7.77/1.49      inference(cnf_transformation,[],[f83]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_444,plain,
% 7.77/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.77/1.49      | ~ v1_funct_2(X3,X2,X1)
% 7.77/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 7.77/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.77/1.49      | ~ v1_funct_1(X0)
% 7.77/1.49      | ~ v1_funct_1(X3)
% 7.77/1.49      | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.77/1.49      | k2_relset_1(X1,X2,X0) = X2
% 7.77/1.49      | k6_partfun1(X2) != k6_partfun1(sK0)
% 7.77/1.49      | sK0 != X2 ),
% 7.77/1.49      inference(resolution_lifted,[status(thm)],[c_26,c_31]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_445,plain,
% 7.77/1.49      ( ~ v1_funct_2(X0,X1,sK0)
% 7.77/1.49      | ~ v1_funct_2(X2,sK0,X1)
% 7.77/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 7.77/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 7.77/1.49      | ~ v1_funct_1(X0)
% 7.77/1.49      | ~ v1_funct_1(X2)
% 7.77/1.49      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.77/1.49      | k2_relset_1(X1,sK0,X0) = sK0
% 7.77/1.49      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 7.77/1.49      inference(unflattening,[status(thm)],[c_444]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_528,plain,
% 7.77/1.49      ( ~ v1_funct_2(X0,X1,sK0)
% 7.77/1.49      | ~ v1_funct_2(X2,sK0,X1)
% 7.77/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 7.77/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 7.77/1.49      | ~ v1_funct_1(X0)
% 7.77/1.49      | ~ v1_funct_1(X2)
% 7.77/1.49      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.77/1.49      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 7.77/1.49      inference(equality_resolution_simp,[status(thm)],[c_445]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_1205,plain,
% 7.77/1.49      ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.77/1.49      | k2_relset_1(X0,sK0,X2) = sK0
% 7.77/1.49      | v1_funct_2(X2,X0,sK0) != iProver_top
% 7.77/1.49      | v1_funct_2(X1,sK0,X0) != iProver_top
% 7.77/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 7.77/1.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 7.77/1.49      | v1_funct_1(X1) != iProver_top
% 7.77/1.49      | v1_funct_1(X2) != iProver_top ),
% 7.77/1.49      inference(predicate_to_equality,[status(thm)],[c_528]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_1605,plain,
% 7.77/1.49      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 7.77/1.49      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 7.77/1.49      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 7.77/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.77/1.49      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.77/1.49      | v1_funct_1(sK3) != iProver_top
% 7.77/1.49      | v1_funct_1(sK2) != iProver_top ),
% 7.77/1.49      inference(equality_resolution,[status(thm)],[c_1205]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_37,negated_conjecture,
% 7.77/1.49      ( v1_funct_2(sK2,sK0,sK1) ),
% 7.77/1.49      inference(cnf_transformation,[],[f85]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_40,plain,
% 7.77/1.49      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 7.77/1.49      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_34,negated_conjecture,
% 7.77/1.49      ( v1_funct_2(sK3,sK1,sK0) ),
% 7.77/1.49      inference(cnf_transformation,[],[f88]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_43,plain,
% 7.77/1.49      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 7.77/1.49      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_1972,plain,
% 7.77/1.49      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 7.77/1.49      inference(global_propositional_subsumption,
% 7.77/1.49                [status(thm)],
% 7.77/1.49                [c_1605,c_39,c_40,c_41,c_42,c_43,c_44]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_2252,plain,
% 7.77/1.49      ( k2_relat_1(sK3) = sK0 ),
% 7.77/1.49      inference(light_normalisation,[status(thm)],[c_2249,c_1972]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_5088,plain,
% 7.77/1.49      ( k2_funct_1(sK3) = sK2
% 7.77/1.49      | k6_partfun1(sK0) != k6_partfun1(sK0)
% 7.77/1.49      | k1_relat_1(sK3) != sK1
% 7.77/1.49      | v1_funct_1(sK3) != iProver_top
% 7.77/1.49      | v1_funct_1(sK2) != iProver_top
% 7.77/1.49      | v2_funct_1(sK3) != iProver_top
% 7.77/1.49      | v1_relat_1(sK3) != iProver_top
% 7.77/1.49      | v1_relat_1(sK2) != iProver_top ),
% 7.77/1.49      inference(light_normalisation,[status(thm)],[c_5085,c_2251,c_2252]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_5089,plain,
% 7.77/1.49      ( k2_funct_1(sK3) = sK2
% 7.77/1.49      | k1_relat_1(sK3) != sK1
% 7.77/1.49      | v1_funct_1(sK3) != iProver_top
% 7.77/1.49      | v1_funct_1(sK2) != iProver_top
% 7.77/1.49      | v2_funct_1(sK3) != iProver_top
% 7.77/1.49      | v1_relat_1(sK3) != iProver_top
% 7.77/1.49      | v1_relat_1(sK2) != iProver_top ),
% 7.77/1.49      inference(equality_resolution_simp,[status(thm)],[c_5088]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_6478,plain,
% 7.77/1.49      ( k2_funct_1(sK3) = sK2
% 7.77/1.49      | k1_relat_1(sK3) != sK1
% 7.77/1.49      | v2_funct_1(sK3) != iProver_top ),
% 7.77/1.49      inference(global_propositional_subsumption,
% 7.77/1.49                [status(thm)],
% 7.77/1.49                [c_5089,c_39,c_41,c_42,c_44,c_1426,c_1627]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_1212,plain,
% 7.77/1.49      ( v1_funct_1(sK3) = iProver_top ),
% 7.77/1.49      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_16,plain,
% 7.77/1.49      ( ~ v1_funct_1(X0)
% 7.77/1.49      | ~ v2_funct_1(X0)
% 7.77/1.49      | ~ v1_relat_1(X0)
% 7.77/1.49      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 7.77/1.49      inference(cnf_transformation,[],[f72]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_1222,plain,
% 7.77/1.49      ( k2_funct_1(k2_funct_1(X0)) = X0
% 7.77/1.49      | v1_funct_1(X0) != iProver_top
% 7.77/1.49      | v2_funct_1(X0) != iProver_top
% 7.77/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.77/1.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_4158,plain,
% 7.77/1.49      ( k2_funct_1(k2_funct_1(sK3)) = sK3
% 7.77/1.49      | v2_funct_1(sK3) != iProver_top
% 7.77/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.77/1.49      inference(superposition,[status(thm)],[c_1212,c_1222]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_1959,plain,
% 7.77/1.49      ( ~ v1_funct_1(sK3)
% 7.77/1.49      | ~ v2_funct_1(sK3)
% 7.77/1.49      | ~ v1_relat_1(sK3)
% 7.77/1.49      | k2_funct_1(k2_funct_1(sK3)) = sK3 ),
% 7.77/1.49      inference(instantiation,[status(thm)],[c_16]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_1960,plain,
% 7.77/1.49      ( k2_funct_1(k2_funct_1(sK3)) = sK3
% 7.77/1.49      | v1_funct_1(sK3) != iProver_top
% 7.77/1.49      | v2_funct_1(sK3) != iProver_top
% 7.77/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.77/1.49      inference(predicate_to_equality,[status(thm)],[c_1959]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_4355,plain,
% 7.77/1.49      ( v2_funct_1(sK3) != iProver_top
% 7.77/1.49      | k2_funct_1(k2_funct_1(sK3)) = sK3 ),
% 7.77/1.49      inference(global_propositional_subsumption,
% 7.77/1.49                [status(thm)],
% 7.77/1.49                [c_4158,c_42,c_44,c_1426,c_1960]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_4356,plain,
% 7.77/1.49      ( k2_funct_1(k2_funct_1(sK3)) = sK3
% 7.77/1.49      | v2_funct_1(sK3) != iProver_top ),
% 7.77/1.49      inference(renaming,[status(thm)],[c_4355]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_1343,plain,
% 7.77/1.49      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 7.77/1.49      inference(instantiation,[status(thm)],[c_702]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_1618,plain,
% 7.77/1.49      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 7.77/1.49      inference(instantiation,[status(thm)],[c_1343]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_2139,plain,
% 7.77/1.49      ( k2_funct_1(X0) != sK3 | sK3 = k2_funct_1(X0) | sK3 != sK3 ),
% 7.77/1.49      inference(instantiation,[status(thm)],[c_1618]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_3795,plain,
% 7.77/1.49      ( k2_funct_1(k2_funct_1(sK3)) != sK3
% 7.77/1.49      | sK3 = k2_funct_1(k2_funct_1(sK3))
% 7.77/1.49      | sK3 != sK3 ),
% 7.77/1.49      inference(instantiation,[status(thm)],[c_2139]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_1,plain,
% 7.77/1.49      ( r1_tarski(X0,X0) ),
% 7.77/1.49      inference(cnf_transformation,[],[f102]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_2069,plain,
% 7.77/1.49      ( r1_tarski(sK2,sK2) ),
% 7.77/1.49      inference(instantiation,[status(thm)],[c_1]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_1479,plain,
% 7.77/1.49      ( ~ r1_tarski(X0,sK2) | ~ r1_tarski(sK2,X0) | X0 = sK2 ),
% 7.77/1.49      inference(instantiation,[status(thm)],[c_0]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_1753,plain,
% 7.77/1.49      ( ~ r1_tarski(sK2,sK2) | sK2 = sK2 ),
% 7.77/1.49      inference(instantiation,[status(thm)],[c_1479]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_701,plain,( X0 = X0 ),theory(equality) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_1686,plain,
% 7.77/1.49      ( sK3 = sK3 ),
% 7.77/1.49      inference(instantiation,[status(thm)],[c_701]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_10,plain,
% 7.77/1.49      ( v2_funct_1(k6_partfun1(X0)) ),
% 7.77/1.49      inference(cnf_transformation,[],[f98]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_93,plain,
% 7.77/1.49      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 7.77/1.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_95,plain,
% 7.77/1.49      ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
% 7.77/1.49      inference(instantiation,[status(thm)],[c_93]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(c_27,negated_conjecture,
% 7.77/1.49      ( k2_funct_1(sK2) != sK3 ),
% 7.77/1.49      inference(cnf_transformation,[],[f95]) ).
% 7.77/1.49  
% 7.77/1.49  cnf(contradiction,plain,
% 7.77/1.49      ( $false ),
% 7.77/1.49      inference(minisat,
% 7.77/1.49                [status(thm)],
% 7.77/1.49                [c_16528,c_13603,c_13102,c_11326,c_11306,c_6478,c_4356,
% 7.77/1.49                 c_3795,c_2069,c_1753,c_1686,c_1426,c_95,c_27,c_44,c_42]) ).
% 7.77/1.49  
% 7.77/1.49  
% 7.77/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.77/1.49  
% 7.77/1.49  ------                               Statistics
% 7.77/1.49  
% 7.77/1.49  ------ General
% 7.77/1.49  
% 7.77/1.49  abstr_ref_over_cycles:                  0
% 7.77/1.49  abstr_ref_under_cycles:                 0
% 7.77/1.49  gc_basic_clause_elim:                   0
% 7.77/1.49  forced_gc_time:                         0
% 7.77/1.49  parsing_time:                           0.04
% 7.77/1.49  unif_index_cands_time:                  0.
% 7.77/1.49  unif_index_add_time:                    0.
% 7.77/1.49  orderings_time:                         0.
% 7.77/1.49  out_proof_time:                         0.015
% 7.77/1.49  total_time:                             0.611
% 7.77/1.49  num_of_symbols:                         55
% 7.77/1.49  num_of_terms:                           22879
% 7.77/1.49  
% 7.77/1.49  ------ Preprocessing
% 7.77/1.49  
% 7.77/1.49  num_of_splits:                          0
% 7.77/1.49  num_of_split_atoms:                     0
% 7.77/1.49  num_of_reused_defs:                     0
% 7.77/1.49  num_eq_ax_congr_red:                    14
% 7.77/1.49  num_of_sem_filtered_clauses:            1
% 7.77/1.49  num_of_subtypes:                        0
% 7.77/1.49  monotx_restored_types:                  0
% 7.77/1.49  sat_num_of_epr_types:                   0
% 7.77/1.49  sat_num_of_non_cyclic_types:            0
% 7.77/1.49  sat_guarded_non_collapsed_types:        0
% 7.77/1.49  num_pure_diseq_elim:                    0
% 7.77/1.49  simp_replaced_by:                       0
% 7.77/1.49  res_preprocessed:                       180
% 7.77/1.49  prep_upred:                             0
% 7.77/1.49  prep_unflattend:                        12
% 7.77/1.49  smt_new_axioms:                         0
% 7.77/1.49  pred_elim_cands:                        6
% 7.77/1.49  pred_elim:                              2
% 7.77/1.49  pred_elim_cl:                           3
% 7.77/1.49  pred_elim_cycles:                       4
% 7.77/1.49  merged_defs:                            0
% 7.77/1.49  merged_defs_ncl:                        0
% 7.77/1.49  bin_hyper_res:                          0
% 7.77/1.49  prep_cycles:                            4
% 7.77/1.49  pred_elim_time:                         0.005
% 7.77/1.49  splitting_time:                         0.
% 7.77/1.49  sem_filter_time:                        0.
% 7.77/1.49  monotx_time:                            0.
% 7.77/1.49  subtype_inf_time:                       0.
% 7.77/1.49  
% 7.77/1.49  ------ Problem properties
% 7.77/1.49  
% 7.77/1.49  clauses:                                35
% 7.77/1.49  conjectures:                            11
% 7.77/1.49  epr:                                    9
% 7.77/1.49  horn:                                   35
% 7.77/1.49  ground:                                 12
% 7.77/1.49  unary:                                  17
% 7.77/1.49  binary:                                 5
% 7.77/1.49  lits:                                   97
% 7.77/1.49  lits_eq:                                23
% 7.77/1.49  fd_pure:                                0
% 7.77/1.49  fd_pseudo:                              0
% 7.77/1.49  fd_cond:                                0
% 7.77/1.49  fd_pseudo_cond:                         2
% 7.77/1.49  ac_symbols:                             0
% 7.77/1.49  
% 7.77/1.49  ------ Propositional Solver
% 7.77/1.49  
% 7.77/1.49  prop_solver_calls:                      34
% 7.77/1.49  prop_fast_solver_calls:                 1839
% 7.77/1.49  smt_solver_calls:                       0
% 7.77/1.49  smt_fast_solver_calls:                  0
% 7.77/1.49  prop_num_of_clauses:                    8693
% 7.77/1.49  prop_preprocess_simplified:             18173
% 7.77/1.49  prop_fo_subsumed:                       151
% 7.77/1.49  prop_solver_time:                       0.
% 7.77/1.49  smt_solver_time:                        0.
% 7.77/1.49  smt_fast_solver_time:                   0.
% 7.77/1.49  prop_fast_solver_time:                  0.
% 7.77/1.49  prop_unsat_core_time:                   0.001
% 7.77/1.49  
% 7.77/1.49  ------ QBF
% 7.77/1.49  
% 7.77/1.49  qbf_q_res:                              0
% 7.77/1.49  qbf_num_tautologies:                    0
% 7.77/1.49  qbf_prep_cycles:                        0
% 7.77/1.49  
% 7.77/1.49  ------ BMC1
% 7.77/1.49  
% 7.77/1.49  bmc1_current_bound:                     -1
% 7.77/1.49  bmc1_last_solved_bound:                 -1
% 7.77/1.49  bmc1_unsat_core_size:                   -1
% 7.77/1.49  bmc1_unsat_core_parents_size:           -1
% 7.77/1.49  bmc1_merge_next_fun:                    0
% 7.77/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.77/1.49  
% 7.77/1.49  ------ Instantiation
% 7.77/1.49  
% 7.77/1.49  inst_num_of_clauses:                    2325
% 7.77/1.49  inst_num_in_passive:                    1074
% 7.77/1.49  inst_num_in_active:                     1071
% 7.77/1.49  inst_num_in_unprocessed:                179
% 7.77/1.49  inst_num_of_loops:                      1198
% 7.77/1.49  inst_num_of_learning_restarts:          0
% 7.77/1.49  inst_num_moves_active_passive:          122
% 7.77/1.49  inst_lit_activity:                      0
% 7.77/1.49  inst_lit_activity_moves:                1
% 7.77/1.49  inst_num_tautologies:                   0
% 7.77/1.49  inst_num_prop_implied:                  0
% 7.77/1.49  inst_num_existing_simplified:           0
% 7.77/1.49  inst_num_eq_res_simplified:             0
% 7.77/1.49  inst_num_child_elim:                    0
% 7.77/1.49  inst_num_of_dismatching_blockings:      604
% 7.77/1.49  inst_num_of_non_proper_insts:           2295
% 7.77/1.49  inst_num_of_duplicates:                 0
% 7.77/1.49  inst_inst_num_from_inst_to_res:         0
% 7.77/1.49  inst_dismatching_checking_time:         0.
% 7.77/1.49  
% 7.77/1.49  ------ Resolution
% 7.77/1.49  
% 7.77/1.49  res_num_of_clauses:                     0
% 7.77/1.49  res_num_in_passive:                     0
% 7.77/1.49  res_num_in_active:                      0
% 7.77/1.49  res_num_of_loops:                       184
% 7.77/1.49  res_forward_subset_subsumed:            148
% 7.77/1.49  res_backward_subset_subsumed:           0
% 7.77/1.49  res_forward_subsumed:                   0
% 7.77/1.49  res_backward_subsumed:                  0
% 7.77/1.49  res_forward_subsumption_resolution:     1
% 7.77/1.49  res_backward_subsumption_resolution:    0
% 7.77/1.49  res_clause_to_clause_subsumption:       1328
% 7.77/1.49  res_orphan_elimination:                 0
% 7.77/1.49  res_tautology_del:                      143
% 7.77/1.49  res_num_eq_res_simplified:              1
% 7.77/1.49  res_num_sel_changes:                    0
% 7.77/1.49  res_moves_from_active_to_pass:          0
% 7.77/1.49  
% 7.77/1.49  ------ Superposition
% 7.77/1.49  
% 7.77/1.49  sup_time_total:                         0.
% 7.77/1.49  sup_time_generating:                    0.
% 7.77/1.49  sup_time_sim_full:                      0.
% 7.77/1.49  sup_time_sim_immed:                     0.
% 7.77/1.49  
% 7.77/1.49  sup_num_of_clauses:                     514
% 7.77/1.49  sup_num_in_active:                      197
% 7.77/1.49  sup_num_in_passive:                     317
% 7.77/1.49  sup_num_of_loops:                       238
% 7.77/1.49  sup_fw_superposition:                   332
% 7.77/1.49  sup_bw_superposition:                   294
% 7.77/1.49  sup_immediate_simplified:               250
% 7.77/1.49  sup_given_eliminated:                   1
% 7.77/1.49  comparisons_done:                       0
% 7.77/1.49  comparisons_avoided:                    0
% 7.77/1.49  
% 7.77/1.49  ------ Simplifications
% 7.77/1.49  
% 7.77/1.49  
% 7.77/1.49  sim_fw_subset_subsumed:                 22
% 7.77/1.49  sim_bw_subset_subsumed:                 35
% 7.77/1.49  sim_fw_subsumed:                        46
% 7.77/1.49  sim_bw_subsumed:                        7
% 7.77/1.49  sim_fw_subsumption_res:                 0
% 7.77/1.49  sim_bw_subsumption_res:                 0
% 7.77/1.49  sim_tautology_del:                      0
% 7.77/1.49  sim_eq_tautology_del:                   21
% 7.77/1.49  sim_eq_res_simp:                        2
% 7.77/1.49  sim_fw_demodulated:                     36
% 7.77/1.49  sim_bw_demodulated:                     30
% 7.77/1.49  sim_light_normalised:                   180
% 7.77/1.49  sim_joinable_taut:                      0
% 7.77/1.49  sim_joinable_simp:                      0
% 7.77/1.49  sim_ac_normalised:                      0
% 7.77/1.49  sim_smt_subsumption:                    0
% 7.77/1.49  
%------------------------------------------------------------------------------
