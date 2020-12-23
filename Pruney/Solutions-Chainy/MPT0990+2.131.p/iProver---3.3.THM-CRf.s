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
% DateTime   : Thu Dec  3 12:03:24 EST 2020

% Result     : Theorem 55.64s
% Output     : CNFRefutation 55.64s
% Verified   : 
% Statistics : Number of formulae       :  223 (2601 expanded)
%              Number of clauses        :  133 ( 827 expanded)
%              Number of leaves         :   24 ( 651 expanded)
%              Depth                    :   25
%              Number of atoms          :  846 (21132 expanded)
%              Number of equality atoms :  402 (7789 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   2 average)

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f55,plain,(
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
    inference(ennf_transformation,[],[f23])).

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
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f55])).

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

fof(f62,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f56,f61,f60])).

fof(f102,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f62])).

fof(f105,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f62])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f50,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f49])).

fof(f93,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f103,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f62])).

fof(f100,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f62])).

fof(f107,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f62])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f48,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f47])).

fof(f92,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f41])).

fof(f57,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f14,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f82,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f19,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f94,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f19])).

fof(f117,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f82,f94])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
              & k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f116,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f77,f94])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
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
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f45])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f89,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f20,axiom,(
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

fof(f51,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f52,plain,(
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
    inference(flattening,[],[f51])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_funct_2(X3,X0)
      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f101,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f62])).

fof(f104,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f62])).

fof(f15,axiom,(
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

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f58,plain,(
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
    inference(nnf_transformation,[],[f44])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f109,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f62])).

fof(f106,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f62])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f53])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f28,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f66,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f108,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f62])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f34,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f73,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f6,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f112,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f70,f94])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => ( v2_funct_1(X0)
              & v2_funct_1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X0)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f65,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f111,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_45,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1894,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_42,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1897,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_30,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1904,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_6327,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1897,c_1904])).

cnf(c_44,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_51,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_6595,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6327,c_51])).

cnf(c_6596,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_6595])).

cnf(c_6604,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1894,c_6596])).

cnf(c_47,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_48,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_6694,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6604,c_48])).

cnf(c_40,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1898,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_6696,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6694,c_1898])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1906,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_6698,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_6694,c_1906])).

cnf(c_50,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_53,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_10906,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6698,c_48,c_50,c_51,c_53])).

cnf(c_18,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1914,plain,
    ( X0 = X1
    | r2_relset_1(X2,X3,X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_10918,plain,
    ( k5_relat_1(sK2,sK3) = X0
    | r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_10906,c_1914])).

cnf(c_17235,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6696,c_10918])).

cnf(c_19,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_2239,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_2240,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2239])).

cnf(c_17805,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17235,c_2240])).

cnf(c_14,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
    | k1_relat_1(X0) != k2_relat_1(X1)
    | k2_funct_1(X0) = X1 ),
    inference(cnf_transformation,[],[f116])).

cnf(c_1917,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k1_relat_1(X1) != k2_relat_1(X0)
    | k2_funct_1(X1) = X0
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_17827,plain,
    ( k1_relat_1(sK3) != k2_relat_1(sK2)
    | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
    | k2_funct_1(sK3) = sK2
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_17805,c_1917])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1931,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3742,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1897,c_1931])).

cnf(c_2054,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
    | ~ v1_relat_1(X0)
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2262,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2054])).

cnf(c_2812,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2262])).

cnf(c_2813,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2812])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_3282,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3283,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3282])).

cnf(c_4218,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3742,c_53,c_2813,c_3283])).

cnf(c_27,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_31,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | v2_funct_2(X3,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_535,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v5_relat_1(X4,X5)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X4)
    | X3 != X4
    | X0 != X5
    | k2_relat_1(X4) = X5 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_31])).

cnf(c_536,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v5_relat_1(X3,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X3)
    | k2_relat_1(X3) = X0 ),
    inference(unflattening,[status(thm)],[c_535])).

cnf(c_15,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_560,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X3)
    | k2_relat_1(X3) = X0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_536,c_15])).

cnf(c_1891,plain,
    ( k2_relat_1(X0) = X1
    | r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X0),k6_partfun1(X1)) != iProver_top
    | v1_funct_2(X3,X1,X2) != iProver_top
    | v1_funct_2(X0,X2,X1) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_560])).

cnf(c_2711,plain,
    ( k2_relat_1(sK3) = sK0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1898,c_1891])).

cnf(c_46,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_49,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_43,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_52,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_2775,plain,
    ( k2_relat_1(sK3) = sK0
    | v1_relat_1(sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2711,c_48,c_49,c_50,c_51,c_52,c_53])).

cnf(c_4223,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(superposition,[status(thm)],[c_4218,c_2775])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1907,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_5771,plain,
    ( k1_relset_1(sK1,sK0,sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1897,c_1907])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1916,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3171,plain,
    ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1897,c_1916])).

cnf(c_5776,plain,
    ( k1_relat_1(sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5771,c_3171])).

cnf(c_38,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1234,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1271,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1234])).

cnf(c_1235,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2035,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1235])).

cnf(c_2036,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2035])).

cnf(c_13198,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5776,c_52,c_38,c_1271,c_2036])).

cnf(c_41,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f106])).

cnf(c_33,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1902,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_4515,plain,
    ( v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_41,c_1902])).

cnf(c_1892,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_3,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1928,plain,
    ( k2_funct_1(X0) = k4_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3928,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1892,c_1928])).

cnf(c_39,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_55,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_1930,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3743,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1894,c_1931])).

cnf(c_4225,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1930,c_3743])).

cnf(c_4415,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3928,c_55,c_4225])).

cnf(c_4516,plain,
    ( v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4515,c_4415])).

cnf(c_5269,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4516,c_48,c_49,c_50,c_55])).

cnf(c_5773,plain,
    ( k1_relset_1(sK1,sK0,k4_relat_1(sK2)) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(k4_relat_1(sK2),sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5269,c_1907])).

cnf(c_5274,plain,
    ( k1_relset_1(sK1,sK0,k4_relat_1(sK2)) = k1_relat_1(k4_relat_1(sK2)) ),
    inference(superposition,[status(thm)],[c_5269,c_1916])).

cnf(c_5774,plain,
    ( k1_relat_1(k4_relat_1(sK2)) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(k4_relat_1(sK2),sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5773,c_5274])).

cnf(c_34,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1901,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | v1_funct_2(k2_funct_1(X2),X1,X0) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_3830,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0) = iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_41,c_1901])).

cnf(c_4073,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3830,c_48,c_49,c_50,c_55])).

cnf(c_4417,plain,
    ( v1_funct_2(k4_relat_1(sK2),sK1,sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4415,c_4073])).

cnf(c_14265,plain,
    ( k1_relat_1(k4_relat_1(sK2)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5774,c_38,c_1271,c_2036,c_4417])).

cnf(c_11,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1920,plain,
    ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4923,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1892,c_1920])).

cnf(c_4925,plain,
    ( k1_relat_1(k4_relat_1(sK2)) = k2_relat_1(sK2)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4923,c_4415])).

cnf(c_6943,plain,
    ( k1_relat_1(k4_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4925,c_55,c_4225])).

cnf(c_14267,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(demodulation,[status(thm)],[c_14265,c_6943])).

cnf(c_17828,plain,
    ( k6_partfun1(sK0) != k6_partfun1(sK0)
    | k2_funct_1(sK3) = sK2
    | sK1 != sK1
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_17827,c_4223,c_13198,c_14267])).

cnf(c_17829,plain,
    ( k2_funct_1(sK3) = sK2
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_17828])).

cnf(c_6,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_1925,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_8,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | v2_funct_1(X0)
    | ~ v2_funct_1(k5_relat_1(X1,X0))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_relat_1(X0) != k2_relat_1(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1923,plain,
    ( k1_relat_1(X0) != k2_relat_1(X1)
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k5_relat_1(X1,X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_13205,plain,
    ( k2_relat_1(X0) != sK1
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_13198,c_1923])).

cnf(c_103407,plain,
    ( v1_relat_1(X0) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
    | k2_relat_1(X0) != sK1
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13205,c_51,c_53,c_2813,c_3283])).

cnf(c_103408,plain,
    ( k2_relat_1(X0) != sK1
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_103407])).

cnf(c_103413,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_14267,c_103408])).

cnf(c_103418,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_103413,c_17805])).

cnf(c_111490,plain,
    ( v2_funct_1(sK3) = iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_103418,c_48,c_4225])).

cnf(c_111491,plain,
    ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_111490])).

cnf(c_111494,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1925,c_111491])).

cnf(c_165238,plain,
    ( k2_funct_1(sK3) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_17829,c_48,c_51,c_53,c_2813,c_3283,c_4225,c_111494])).

cnf(c_1895,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_3927,plain,
    ( k2_funct_1(sK3) = k4_relat_1(sK3)
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1895,c_1928])).

cnf(c_4410,plain,
    ( v2_funct_1(sK3) != iProver_top
    | k2_funct_1(sK3) = k4_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3927,c_53,c_2813,c_3283])).

cnf(c_4411,plain,
    ( k2_funct_1(sK3) = k4_relat_1(sK3)
    | v2_funct_1(sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_4410])).

cnf(c_111501,plain,
    ( k2_funct_1(sK3) = k4_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_111494,c_4411])).

cnf(c_165240,plain,
    ( k4_relat_1(sK3) = sK2 ),
    inference(demodulation,[status(thm)],[c_165238,c_111501])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | k4_relat_1(k4_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1929,plain,
    ( k4_relat_1(k4_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4222,plain,
    ( k4_relat_1(k4_relat_1(sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_4218,c_1929])).

cnf(c_165926,plain,
    ( k4_relat_1(sK2) = sK3 ),
    inference(demodulation,[status(thm)],[c_165240,c_4222])).

cnf(c_36,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f111])).

cnf(c_4419,plain,
    ( k4_relat_1(sK2) != sK3 ),
    inference(demodulation,[status(thm)],[c_4415,c_36])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_165926,c_4419])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:18:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 55.64/7.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 55.64/7.49  
% 55.64/7.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 55.64/7.49  
% 55.64/7.49  ------  iProver source info
% 55.64/7.49  
% 55.64/7.49  git: date: 2020-06-30 10:37:57 +0100
% 55.64/7.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 55.64/7.49  git: non_committed_changes: false
% 55.64/7.49  git: last_make_outside_of_git: false
% 55.64/7.49  
% 55.64/7.49  ------ 
% 55.64/7.49  
% 55.64/7.49  ------ Input Options
% 55.64/7.49  
% 55.64/7.49  --out_options                           all
% 55.64/7.49  --tptp_safe_out                         true
% 55.64/7.49  --problem_path                          ""
% 55.64/7.49  --include_path                          ""
% 55.64/7.49  --clausifier                            res/vclausify_rel
% 55.64/7.49  --clausifier_options                    ""
% 55.64/7.49  --stdin                                 false
% 55.64/7.49  --stats_out                             all
% 55.64/7.49  
% 55.64/7.49  ------ General Options
% 55.64/7.49  
% 55.64/7.49  --fof                                   false
% 55.64/7.49  --time_out_real                         305.
% 55.64/7.49  --time_out_virtual                      -1.
% 55.64/7.49  --symbol_type_check                     false
% 55.64/7.49  --clausify_out                          false
% 55.64/7.49  --sig_cnt_out                           false
% 55.64/7.49  --trig_cnt_out                          false
% 55.64/7.49  --trig_cnt_out_tolerance                1.
% 55.64/7.49  --trig_cnt_out_sk_spl                   false
% 55.64/7.49  --abstr_cl_out                          false
% 55.64/7.49  
% 55.64/7.49  ------ Global Options
% 55.64/7.49  
% 55.64/7.49  --schedule                              default
% 55.64/7.49  --add_important_lit                     false
% 55.64/7.49  --prop_solver_per_cl                    1000
% 55.64/7.49  --min_unsat_core                        false
% 55.64/7.49  --soft_assumptions                      false
% 55.64/7.49  --soft_lemma_size                       3
% 55.64/7.49  --prop_impl_unit_size                   0
% 55.64/7.49  --prop_impl_unit                        []
% 55.64/7.49  --share_sel_clauses                     true
% 55.64/7.49  --reset_solvers                         false
% 55.64/7.49  --bc_imp_inh                            [conj_cone]
% 55.64/7.49  --conj_cone_tolerance                   3.
% 55.64/7.49  --extra_neg_conj                        none
% 55.64/7.49  --large_theory_mode                     true
% 55.64/7.49  --prolific_symb_bound                   200
% 55.64/7.49  --lt_threshold                          2000
% 55.64/7.49  --clause_weak_htbl                      true
% 55.64/7.49  --gc_record_bc_elim                     false
% 55.64/7.49  
% 55.64/7.49  ------ Preprocessing Options
% 55.64/7.49  
% 55.64/7.49  --preprocessing_flag                    true
% 55.64/7.49  --time_out_prep_mult                    0.1
% 55.64/7.49  --splitting_mode                        input
% 55.64/7.49  --splitting_grd                         true
% 55.64/7.49  --splitting_cvd                         false
% 55.64/7.49  --splitting_cvd_svl                     false
% 55.64/7.49  --splitting_nvd                         32
% 55.64/7.49  --sub_typing                            true
% 55.64/7.49  --prep_gs_sim                           true
% 55.64/7.49  --prep_unflatten                        true
% 55.64/7.49  --prep_res_sim                          true
% 55.64/7.49  --prep_upred                            true
% 55.64/7.49  --prep_sem_filter                       exhaustive
% 55.64/7.49  --prep_sem_filter_out                   false
% 55.64/7.49  --pred_elim                             true
% 55.64/7.49  --res_sim_input                         true
% 55.64/7.49  --eq_ax_congr_red                       true
% 55.64/7.49  --pure_diseq_elim                       true
% 55.64/7.49  --brand_transform                       false
% 55.64/7.49  --non_eq_to_eq                          false
% 55.64/7.49  --prep_def_merge                        true
% 55.64/7.49  --prep_def_merge_prop_impl              false
% 55.64/7.49  --prep_def_merge_mbd                    true
% 55.64/7.49  --prep_def_merge_tr_red                 false
% 55.64/7.49  --prep_def_merge_tr_cl                  false
% 55.64/7.49  --smt_preprocessing                     true
% 55.64/7.49  --smt_ac_axioms                         fast
% 55.64/7.49  --preprocessed_out                      false
% 55.64/7.49  --preprocessed_stats                    false
% 55.64/7.49  
% 55.64/7.49  ------ Abstraction refinement Options
% 55.64/7.49  
% 55.64/7.49  --abstr_ref                             []
% 55.64/7.49  --abstr_ref_prep                        false
% 55.64/7.49  --abstr_ref_until_sat                   false
% 55.64/7.49  --abstr_ref_sig_restrict                funpre
% 55.64/7.49  --abstr_ref_af_restrict_to_split_sk     false
% 55.64/7.49  --abstr_ref_under                       []
% 55.64/7.49  
% 55.64/7.49  ------ SAT Options
% 55.64/7.49  
% 55.64/7.49  --sat_mode                              false
% 55.64/7.49  --sat_fm_restart_options                ""
% 55.64/7.49  --sat_gr_def                            false
% 55.64/7.49  --sat_epr_types                         true
% 55.64/7.49  --sat_non_cyclic_types                  false
% 55.64/7.49  --sat_finite_models                     false
% 55.64/7.49  --sat_fm_lemmas                         false
% 55.64/7.49  --sat_fm_prep                           false
% 55.64/7.49  --sat_fm_uc_incr                        true
% 55.64/7.49  --sat_out_model                         small
% 55.64/7.49  --sat_out_clauses                       false
% 55.64/7.49  
% 55.64/7.49  ------ QBF Options
% 55.64/7.49  
% 55.64/7.49  --qbf_mode                              false
% 55.64/7.49  --qbf_elim_univ                         false
% 55.64/7.49  --qbf_dom_inst                          none
% 55.64/7.49  --qbf_dom_pre_inst                      false
% 55.64/7.49  --qbf_sk_in                             false
% 55.64/7.49  --qbf_pred_elim                         true
% 55.64/7.49  --qbf_split                             512
% 55.64/7.49  
% 55.64/7.49  ------ BMC1 Options
% 55.64/7.49  
% 55.64/7.49  --bmc1_incremental                      false
% 55.64/7.49  --bmc1_axioms                           reachable_all
% 55.64/7.49  --bmc1_min_bound                        0
% 55.64/7.49  --bmc1_max_bound                        -1
% 55.64/7.49  --bmc1_max_bound_default                -1
% 55.64/7.49  --bmc1_symbol_reachability              true
% 55.64/7.49  --bmc1_property_lemmas                  false
% 55.64/7.49  --bmc1_k_induction                      false
% 55.64/7.49  --bmc1_non_equiv_states                 false
% 55.64/7.49  --bmc1_deadlock                         false
% 55.64/7.49  --bmc1_ucm                              false
% 55.64/7.49  --bmc1_add_unsat_core                   none
% 55.64/7.49  --bmc1_unsat_core_children              false
% 55.64/7.49  --bmc1_unsat_core_extrapolate_axioms    false
% 55.64/7.49  --bmc1_out_stat                         full
% 55.64/7.49  --bmc1_ground_init                      false
% 55.64/7.49  --bmc1_pre_inst_next_state              false
% 55.64/7.49  --bmc1_pre_inst_state                   false
% 55.64/7.49  --bmc1_pre_inst_reach_state             false
% 55.64/7.49  --bmc1_out_unsat_core                   false
% 55.64/7.49  --bmc1_aig_witness_out                  false
% 55.64/7.49  --bmc1_verbose                          false
% 55.64/7.49  --bmc1_dump_clauses_tptp                false
% 55.64/7.49  --bmc1_dump_unsat_core_tptp             false
% 55.64/7.49  --bmc1_dump_file                        -
% 55.64/7.49  --bmc1_ucm_expand_uc_limit              128
% 55.64/7.49  --bmc1_ucm_n_expand_iterations          6
% 55.64/7.49  --bmc1_ucm_extend_mode                  1
% 55.64/7.49  --bmc1_ucm_init_mode                    2
% 55.64/7.49  --bmc1_ucm_cone_mode                    none
% 55.64/7.49  --bmc1_ucm_reduced_relation_type        0
% 55.64/7.49  --bmc1_ucm_relax_model                  4
% 55.64/7.49  --bmc1_ucm_full_tr_after_sat            true
% 55.64/7.49  --bmc1_ucm_expand_neg_assumptions       false
% 55.64/7.49  --bmc1_ucm_layered_model                none
% 55.64/7.49  --bmc1_ucm_max_lemma_size               10
% 55.64/7.49  
% 55.64/7.49  ------ AIG Options
% 55.64/7.49  
% 55.64/7.49  --aig_mode                              false
% 55.64/7.49  
% 55.64/7.49  ------ Instantiation Options
% 55.64/7.49  
% 55.64/7.49  --instantiation_flag                    true
% 55.64/7.49  --inst_sos_flag                         true
% 55.64/7.49  --inst_sos_phase                        true
% 55.64/7.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 55.64/7.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 55.64/7.49  --inst_lit_sel_side                     num_symb
% 55.64/7.49  --inst_solver_per_active                1400
% 55.64/7.49  --inst_solver_calls_frac                1.
% 55.64/7.49  --inst_passive_queue_type               priority_queues
% 55.64/7.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 55.64/7.49  --inst_passive_queues_freq              [25;2]
% 55.64/7.49  --inst_dismatching                      true
% 55.64/7.49  --inst_eager_unprocessed_to_passive     true
% 55.64/7.49  --inst_prop_sim_given                   true
% 55.64/7.49  --inst_prop_sim_new                     false
% 55.64/7.49  --inst_subs_new                         false
% 55.64/7.49  --inst_eq_res_simp                      false
% 55.64/7.49  --inst_subs_given                       false
% 55.64/7.49  --inst_orphan_elimination               true
% 55.64/7.49  --inst_learning_loop_flag               true
% 55.64/7.49  --inst_learning_start                   3000
% 55.64/7.49  --inst_learning_factor                  2
% 55.64/7.49  --inst_start_prop_sim_after_learn       3
% 55.64/7.49  --inst_sel_renew                        solver
% 55.64/7.49  --inst_lit_activity_flag                true
% 55.64/7.49  --inst_restr_to_given                   false
% 55.64/7.49  --inst_activity_threshold               500
% 55.64/7.49  --inst_out_proof                        true
% 55.64/7.49  
% 55.64/7.49  ------ Resolution Options
% 55.64/7.49  
% 55.64/7.49  --resolution_flag                       true
% 55.64/7.49  --res_lit_sel                           adaptive
% 55.64/7.49  --res_lit_sel_side                      none
% 55.64/7.49  --res_ordering                          kbo
% 55.64/7.49  --res_to_prop_solver                    active
% 55.64/7.49  --res_prop_simpl_new                    false
% 55.64/7.49  --res_prop_simpl_given                  true
% 55.64/7.49  --res_passive_queue_type                priority_queues
% 55.64/7.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 55.64/7.49  --res_passive_queues_freq               [15;5]
% 55.64/7.49  --res_forward_subs                      full
% 55.64/7.49  --res_backward_subs                     full
% 55.64/7.49  --res_forward_subs_resolution           true
% 55.64/7.49  --res_backward_subs_resolution          true
% 55.64/7.49  --res_orphan_elimination                true
% 55.64/7.49  --res_time_limit                        2.
% 55.64/7.49  --res_out_proof                         true
% 55.64/7.49  
% 55.64/7.49  ------ Superposition Options
% 55.64/7.49  
% 55.64/7.49  --superposition_flag                    true
% 55.64/7.49  --sup_passive_queue_type                priority_queues
% 55.64/7.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 55.64/7.49  --sup_passive_queues_freq               [8;1;4]
% 55.64/7.49  --demod_completeness_check              fast
% 55.64/7.49  --demod_use_ground                      true
% 55.64/7.49  --sup_to_prop_solver                    passive
% 55.64/7.49  --sup_prop_simpl_new                    true
% 55.64/7.49  --sup_prop_simpl_given                  true
% 55.64/7.49  --sup_fun_splitting                     true
% 55.64/7.49  --sup_smt_interval                      50000
% 55.64/7.49  
% 55.64/7.49  ------ Superposition Simplification Setup
% 55.64/7.49  
% 55.64/7.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 55.64/7.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 55.64/7.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 55.64/7.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 55.64/7.49  --sup_full_triv                         [TrivRules;PropSubs]
% 55.64/7.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 55.64/7.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 55.64/7.49  --sup_immed_triv                        [TrivRules]
% 55.64/7.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 55.64/7.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 55.64/7.49  --sup_immed_bw_main                     []
% 55.64/7.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 55.64/7.49  --sup_input_triv                        [Unflattening;TrivRules]
% 55.64/7.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 55.64/7.49  --sup_input_bw                          []
% 55.64/7.49  
% 55.64/7.49  ------ Combination Options
% 55.64/7.49  
% 55.64/7.49  --comb_res_mult                         3
% 55.64/7.49  --comb_sup_mult                         2
% 55.64/7.49  --comb_inst_mult                        10
% 55.64/7.49  
% 55.64/7.49  ------ Debug Options
% 55.64/7.49  
% 55.64/7.49  --dbg_backtrace                         false
% 55.64/7.49  --dbg_dump_prop_clauses                 false
% 55.64/7.49  --dbg_dump_prop_clauses_file            -
% 55.64/7.49  --dbg_out_stat                          false
% 55.64/7.49  ------ Parsing...
% 55.64/7.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 55.64/7.49  
% 55.64/7.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 55.64/7.49  
% 55.64/7.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 55.64/7.49  
% 55.64/7.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 55.64/7.49  ------ Proving...
% 55.64/7.49  ------ Problem Properties 
% 55.64/7.49  
% 55.64/7.49  
% 55.64/7.49  clauses                                 45
% 55.64/7.49  conjectures                             12
% 55.64/7.49  EPR                                     7
% 55.64/7.49  Horn                                    41
% 55.64/7.49  unary                                   16
% 55.64/7.49  binary                                  3
% 55.64/7.49  lits                                    148
% 55.64/7.49  lits eq                                 31
% 55.64/7.49  fd_pure                                 0
% 55.64/7.49  fd_pseudo                               0
% 55.64/7.49  fd_cond                                 3
% 55.64/7.49  fd_pseudo_cond                          3
% 55.64/7.49  AC symbols                              0
% 55.64/7.49  
% 55.64/7.49  ------ Schedule dynamic 5 is on 
% 55.64/7.49  
% 55.64/7.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 55.64/7.49  
% 55.64/7.49  
% 55.64/7.49  ------ 
% 55.64/7.49  Current options:
% 55.64/7.49  ------ 
% 55.64/7.49  
% 55.64/7.49  ------ Input Options
% 55.64/7.49  
% 55.64/7.49  --out_options                           all
% 55.64/7.49  --tptp_safe_out                         true
% 55.64/7.49  --problem_path                          ""
% 55.64/7.49  --include_path                          ""
% 55.64/7.49  --clausifier                            res/vclausify_rel
% 55.64/7.49  --clausifier_options                    ""
% 55.64/7.49  --stdin                                 false
% 55.64/7.49  --stats_out                             all
% 55.64/7.49  
% 55.64/7.49  ------ General Options
% 55.64/7.49  
% 55.64/7.49  --fof                                   false
% 55.64/7.49  --time_out_real                         305.
% 55.64/7.49  --time_out_virtual                      -1.
% 55.64/7.49  --symbol_type_check                     false
% 55.64/7.49  --clausify_out                          false
% 55.64/7.49  --sig_cnt_out                           false
% 55.64/7.49  --trig_cnt_out                          false
% 55.64/7.49  --trig_cnt_out_tolerance                1.
% 55.64/7.49  --trig_cnt_out_sk_spl                   false
% 55.64/7.49  --abstr_cl_out                          false
% 55.64/7.49  
% 55.64/7.49  ------ Global Options
% 55.64/7.49  
% 55.64/7.49  --schedule                              default
% 55.64/7.49  --add_important_lit                     false
% 55.64/7.49  --prop_solver_per_cl                    1000
% 55.64/7.49  --min_unsat_core                        false
% 55.64/7.49  --soft_assumptions                      false
% 55.64/7.49  --soft_lemma_size                       3
% 55.64/7.49  --prop_impl_unit_size                   0
% 55.64/7.49  --prop_impl_unit                        []
% 55.64/7.49  --share_sel_clauses                     true
% 55.64/7.49  --reset_solvers                         false
% 55.64/7.49  --bc_imp_inh                            [conj_cone]
% 55.64/7.49  --conj_cone_tolerance                   3.
% 55.64/7.49  --extra_neg_conj                        none
% 55.64/7.49  --large_theory_mode                     true
% 55.64/7.49  --prolific_symb_bound                   200
% 55.64/7.49  --lt_threshold                          2000
% 55.64/7.49  --clause_weak_htbl                      true
% 55.64/7.49  --gc_record_bc_elim                     false
% 55.64/7.49  
% 55.64/7.49  ------ Preprocessing Options
% 55.64/7.49  
% 55.64/7.49  --preprocessing_flag                    true
% 55.64/7.49  --time_out_prep_mult                    0.1
% 55.64/7.49  --splitting_mode                        input
% 55.64/7.49  --splitting_grd                         true
% 55.64/7.49  --splitting_cvd                         false
% 55.64/7.49  --splitting_cvd_svl                     false
% 55.64/7.49  --splitting_nvd                         32
% 55.64/7.49  --sub_typing                            true
% 55.64/7.49  --prep_gs_sim                           true
% 55.64/7.49  --prep_unflatten                        true
% 55.64/7.49  --prep_res_sim                          true
% 55.64/7.49  --prep_upred                            true
% 55.64/7.49  --prep_sem_filter                       exhaustive
% 55.64/7.49  --prep_sem_filter_out                   false
% 55.64/7.49  --pred_elim                             true
% 55.64/7.49  --res_sim_input                         true
% 55.64/7.49  --eq_ax_congr_red                       true
% 55.64/7.49  --pure_diseq_elim                       true
% 55.64/7.49  --brand_transform                       false
% 55.64/7.49  --non_eq_to_eq                          false
% 55.64/7.49  --prep_def_merge                        true
% 55.64/7.49  --prep_def_merge_prop_impl              false
% 55.64/7.49  --prep_def_merge_mbd                    true
% 55.64/7.49  --prep_def_merge_tr_red                 false
% 55.64/7.49  --prep_def_merge_tr_cl                  false
% 55.64/7.49  --smt_preprocessing                     true
% 55.64/7.49  --smt_ac_axioms                         fast
% 55.64/7.49  --preprocessed_out                      false
% 55.64/7.49  --preprocessed_stats                    false
% 55.64/7.49  
% 55.64/7.49  ------ Abstraction refinement Options
% 55.64/7.49  
% 55.64/7.49  --abstr_ref                             []
% 55.64/7.49  --abstr_ref_prep                        false
% 55.64/7.49  --abstr_ref_until_sat                   false
% 55.64/7.49  --abstr_ref_sig_restrict                funpre
% 55.64/7.49  --abstr_ref_af_restrict_to_split_sk     false
% 55.64/7.49  --abstr_ref_under                       []
% 55.64/7.49  
% 55.64/7.49  ------ SAT Options
% 55.64/7.49  
% 55.64/7.49  --sat_mode                              false
% 55.64/7.49  --sat_fm_restart_options                ""
% 55.64/7.49  --sat_gr_def                            false
% 55.64/7.49  --sat_epr_types                         true
% 55.64/7.49  --sat_non_cyclic_types                  false
% 55.64/7.49  --sat_finite_models                     false
% 55.64/7.49  --sat_fm_lemmas                         false
% 55.64/7.49  --sat_fm_prep                           false
% 55.64/7.49  --sat_fm_uc_incr                        true
% 55.64/7.49  --sat_out_model                         small
% 55.64/7.49  --sat_out_clauses                       false
% 55.64/7.49  
% 55.64/7.49  ------ QBF Options
% 55.64/7.49  
% 55.64/7.49  --qbf_mode                              false
% 55.64/7.49  --qbf_elim_univ                         false
% 55.64/7.49  --qbf_dom_inst                          none
% 55.64/7.49  --qbf_dom_pre_inst                      false
% 55.64/7.49  --qbf_sk_in                             false
% 55.64/7.49  --qbf_pred_elim                         true
% 55.64/7.49  --qbf_split                             512
% 55.64/7.49  
% 55.64/7.49  ------ BMC1 Options
% 55.64/7.49  
% 55.64/7.49  --bmc1_incremental                      false
% 55.64/7.49  --bmc1_axioms                           reachable_all
% 55.64/7.49  --bmc1_min_bound                        0
% 55.64/7.49  --bmc1_max_bound                        -1
% 55.64/7.49  --bmc1_max_bound_default                -1
% 55.64/7.49  --bmc1_symbol_reachability              true
% 55.64/7.49  --bmc1_property_lemmas                  false
% 55.64/7.49  --bmc1_k_induction                      false
% 55.64/7.49  --bmc1_non_equiv_states                 false
% 55.64/7.49  --bmc1_deadlock                         false
% 55.64/7.49  --bmc1_ucm                              false
% 55.64/7.49  --bmc1_add_unsat_core                   none
% 55.64/7.49  --bmc1_unsat_core_children              false
% 55.64/7.49  --bmc1_unsat_core_extrapolate_axioms    false
% 55.64/7.49  --bmc1_out_stat                         full
% 55.64/7.49  --bmc1_ground_init                      false
% 55.64/7.49  --bmc1_pre_inst_next_state              false
% 55.64/7.49  --bmc1_pre_inst_state                   false
% 55.64/7.49  --bmc1_pre_inst_reach_state             false
% 55.64/7.49  --bmc1_out_unsat_core                   false
% 55.64/7.49  --bmc1_aig_witness_out                  false
% 55.64/7.49  --bmc1_verbose                          false
% 55.64/7.49  --bmc1_dump_clauses_tptp                false
% 55.64/7.49  --bmc1_dump_unsat_core_tptp             false
% 55.64/7.49  --bmc1_dump_file                        -
% 55.64/7.49  --bmc1_ucm_expand_uc_limit              128
% 55.64/7.49  --bmc1_ucm_n_expand_iterations          6
% 55.64/7.49  --bmc1_ucm_extend_mode                  1
% 55.64/7.49  --bmc1_ucm_init_mode                    2
% 55.64/7.49  --bmc1_ucm_cone_mode                    none
% 55.64/7.49  --bmc1_ucm_reduced_relation_type        0
% 55.64/7.49  --bmc1_ucm_relax_model                  4
% 55.64/7.49  --bmc1_ucm_full_tr_after_sat            true
% 55.64/7.49  --bmc1_ucm_expand_neg_assumptions       false
% 55.64/7.49  --bmc1_ucm_layered_model                none
% 55.64/7.49  --bmc1_ucm_max_lemma_size               10
% 55.64/7.49  
% 55.64/7.49  ------ AIG Options
% 55.64/7.49  
% 55.64/7.49  --aig_mode                              false
% 55.64/7.49  
% 55.64/7.49  ------ Instantiation Options
% 55.64/7.49  
% 55.64/7.49  --instantiation_flag                    true
% 55.64/7.49  --inst_sos_flag                         true
% 55.64/7.49  --inst_sos_phase                        true
% 55.64/7.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 55.64/7.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 55.64/7.49  --inst_lit_sel_side                     none
% 55.64/7.49  --inst_solver_per_active                1400
% 55.64/7.49  --inst_solver_calls_frac                1.
% 55.64/7.49  --inst_passive_queue_type               priority_queues
% 55.64/7.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 55.64/7.49  --inst_passive_queues_freq              [25;2]
% 55.64/7.49  --inst_dismatching                      true
% 55.64/7.49  --inst_eager_unprocessed_to_passive     true
% 55.64/7.49  --inst_prop_sim_given                   true
% 55.64/7.49  --inst_prop_sim_new                     false
% 55.64/7.49  --inst_subs_new                         false
% 55.64/7.49  --inst_eq_res_simp                      false
% 55.64/7.49  --inst_subs_given                       false
% 55.64/7.49  --inst_orphan_elimination               true
% 55.64/7.49  --inst_learning_loop_flag               true
% 55.64/7.49  --inst_learning_start                   3000
% 55.64/7.49  --inst_learning_factor                  2
% 55.64/7.49  --inst_start_prop_sim_after_learn       3
% 55.64/7.49  --inst_sel_renew                        solver
% 55.64/7.49  --inst_lit_activity_flag                true
% 55.64/7.49  --inst_restr_to_given                   false
% 55.64/7.49  --inst_activity_threshold               500
% 55.64/7.49  --inst_out_proof                        true
% 55.64/7.49  
% 55.64/7.49  ------ Resolution Options
% 55.64/7.49  
% 55.64/7.49  --resolution_flag                       false
% 55.64/7.49  --res_lit_sel                           adaptive
% 55.64/7.49  --res_lit_sel_side                      none
% 55.64/7.49  --res_ordering                          kbo
% 55.64/7.49  --res_to_prop_solver                    active
% 55.64/7.49  --res_prop_simpl_new                    false
% 55.64/7.49  --res_prop_simpl_given                  true
% 55.64/7.49  --res_passive_queue_type                priority_queues
% 55.64/7.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 55.64/7.49  --res_passive_queues_freq               [15;5]
% 55.64/7.49  --res_forward_subs                      full
% 55.64/7.49  --res_backward_subs                     full
% 55.64/7.49  --res_forward_subs_resolution           true
% 55.64/7.49  --res_backward_subs_resolution          true
% 55.64/7.49  --res_orphan_elimination                true
% 55.64/7.49  --res_time_limit                        2.
% 55.64/7.49  --res_out_proof                         true
% 55.64/7.49  
% 55.64/7.49  ------ Superposition Options
% 55.64/7.49  
% 55.64/7.49  --superposition_flag                    true
% 55.64/7.49  --sup_passive_queue_type                priority_queues
% 55.64/7.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 55.64/7.49  --sup_passive_queues_freq               [8;1;4]
% 55.64/7.49  --demod_completeness_check              fast
% 55.64/7.49  --demod_use_ground                      true
% 55.64/7.49  --sup_to_prop_solver                    passive
% 55.64/7.49  --sup_prop_simpl_new                    true
% 55.64/7.49  --sup_prop_simpl_given                  true
% 55.64/7.49  --sup_fun_splitting                     true
% 55.64/7.49  --sup_smt_interval                      50000
% 55.64/7.49  
% 55.64/7.49  ------ Superposition Simplification Setup
% 55.64/7.49  
% 55.64/7.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 55.64/7.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 55.64/7.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 55.64/7.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 55.64/7.49  --sup_full_triv                         [TrivRules;PropSubs]
% 55.64/7.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 55.64/7.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 55.64/7.49  --sup_immed_triv                        [TrivRules]
% 55.64/7.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 55.64/7.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 55.64/7.49  --sup_immed_bw_main                     []
% 55.64/7.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 55.64/7.49  --sup_input_triv                        [Unflattening;TrivRules]
% 55.64/7.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 55.64/7.49  --sup_input_bw                          []
% 55.64/7.49  
% 55.64/7.49  ------ Combination Options
% 55.64/7.49  
% 55.64/7.49  --comb_res_mult                         3
% 55.64/7.49  --comb_sup_mult                         2
% 55.64/7.49  --comb_inst_mult                        10
% 55.64/7.49  
% 55.64/7.49  ------ Debug Options
% 55.64/7.49  
% 55.64/7.49  --dbg_backtrace                         false
% 55.64/7.49  --dbg_dump_prop_clauses                 false
% 55.64/7.49  --dbg_dump_prop_clauses_file            -
% 55.64/7.49  --dbg_out_stat                          false
% 55.64/7.49  
% 55.64/7.49  
% 55.64/7.49  
% 55.64/7.49  
% 55.64/7.49  ------ Proving...
% 55.64/7.49  
% 55.64/7.49  
% 55.64/7.49  % SZS status Theorem for theBenchmark.p
% 55.64/7.49  
% 55.64/7.49  % SZS output start CNFRefutation for theBenchmark.p
% 55.64/7.49  
% 55.64/7.49  fof(f22,conjecture,(
% 55.64/7.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 55.64/7.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.64/7.49  
% 55.64/7.49  fof(f23,negated_conjecture,(
% 55.64/7.49    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 55.64/7.49    inference(negated_conjecture,[],[f22])).
% 55.64/7.49  
% 55.64/7.49  fof(f55,plain,(
% 55.64/7.49    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 55.64/7.49    inference(ennf_transformation,[],[f23])).
% 55.64/7.49  
% 55.64/7.49  fof(f56,plain,(
% 55.64/7.49    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 55.64/7.49    inference(flattening,[],[f55])).
% 55.64/7.49  
% 55.64/7.49  fof(f61,plain,(
% 55.64/7.49    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 55.64/7.49    introduced(choice_axiom,[])).
% 55.64/7.49  
% 55.64/7.49  fof(f60,plain,(
% 55.64/7.49    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 55.64/7.49    introduced(choice_axiom,[])).
% 55.64/7.49  
% 55.64/7.49  fof(f62,plain,(
% 55.64/7.49    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 55.64/7.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f56,f61,f60])).
% 55.64/7.49  
% 55.64/7.49  fof(f102,plain,(
% 55.64/7.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 55.64/7.49    inference(cnf_transformation,[],[f62])).
% 55.64/7.49  
% 55.64/7.49  fof(f105,plain,(
% 55.64/7.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 55.64/7.49    inference(cnf_transformation,[],[f62])).
% 55.64/7.49  
% 55.64/7.49  fof(f18,axiom,(
% 55.64/7.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 55.64/7.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.64/7.49  
% 55.64/7.49  fof(f49,plain,(
% 55.64/7.49    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 55.64/7.49    inference(ennf_transformation,[],[f18])).
% 55.64/7.49  
% 55.64/7.49  fof(f50,plain,(
% 55.64/7.49    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 55.64/7.49    inference(flattening,[],[f49])).
% 55.64/7.49  
% 55.64/7.49  fof(f93,plain,(
% 55.64/7.49    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 55.64/7.49    inference(cnf_transformation,[],[f50])).
% 55.64/7.49  
% 55.64/7.49  fof(f103,plain,(
% 55.64/7.49    v1_funct_1(sK3)),
% 55.64/7.49    inference(cnf_transformation,[],[f62])).
% 55.64/7.49  
% 55.64/7.49  fof(f100,plain,(
% 55.64/7.49    v1_funct_1(sK2)),
% 55.64/7.49    inference(cnf_transformation,[],[f62])).
% 55.64/7.49  
% 55.64/7.49  fof(f107,plain,(
% 55.64/7.49    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 55.64/7.49    inference(cnf_transformation,[],[f62])).
% 55.64/7.49  
% 55.64/7.49  fof(f17,axiom,(
% 55.64/7.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 55.64/7.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.64/7.49  
% 55.64/7.49  fof(f47,plain,(
% 55.64/7.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 55.64/7.49    inference(ennf_transformation,[],[f17])).
% 55.64/7.49  
% 55.64/7.49  fof(f48,plain,(
% 55.64/7.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 55.64/7.49    inference(flattening,[],[f47])).
% 55.64/7.49  
% 55.64/7.49  fof(f92,plain,(
% 55.64/7.49    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 55.64/7.49    inference(cnf_transformation,[],[f48])).
% 55.64/7.49  
% 55.64/7.49  fof(f13,axiom,(
% 55.64/7.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 55.64/7.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.64/7.49  
% 55.64/7.49  fof(f41,plain,(
% 55.64/7.49    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 55.64/7.49    inference(ennf_transformation,[],[f13])).
% 55.64/7.49  
% 55.64/7.49  fof(f42,plain,(
% 55.64/7.49    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 55.64/7.49    inference(flattening,[],[f41])).
% 55.64/7.49  
% 55.64/7.49  fof(f57,plain,(
% 55.64/7.49    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 55.64/7.49    inference(nnf_transformation,[],[f42])).
% 55.64/7.49  
% 55.64/7.49  fof(f80,plain,(
% 55.64/7.49    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 55.64/7.49    inference(cnf_transformation,[],[f57])).
% 55.64/7.49  
% 55.64/7.49  fof(f14,axiom,(
% 55.64/7.49    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 55.64/7.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.64/7.49  
% 55.64/7.49  fof(f82,plain,(
% 55.64/7.49    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 55.64/7.49    inference(cnf_transformation,[],[f14])).
% 55.64/7.49  
% 55.64/7.49  fof(f19,axiom,(
% 55.64/7.49    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 55.64/7.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.64/7.49  
% 55.64/7.49  fof(f94,plain,(
% 55.64/7.49    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 55.64/7.49    inference(cnf_transformation,[],[f19])).
% 55.64/7.49  
% 55.64/7.49  fof(f117,plain,(
% 55.64/7.49    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 55.64/7.49    inference(definition_unfolding,[],[f82,f94])).
% 55.64/7.49  
% 55.64/7.49  fof(f10,axiom,(
% 55.64/7.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 55.64/7.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.64/7.49  
% 55.64/7.49  fof(f37,plain,(
% 55.64/7.49    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 55.64/7.49    inference(ennf_transformation,[],[f10])).
% 55.64/7.49  
% 55.64/7.49  fof(f38,plain,(
% 55.64/7.49    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 55.64/7.49    inference(flattening,[],[f37])).
% 55.64/7.49  
% 55.64/7.49  fof(f77,plain,(
% 55.64/7.49    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 55.64/7.49    inference(cnf_transformation,[],[f38])).
% 55.64/7.49  
% 55.64/7.49  fof(f116,plain,(
% 55.64/7.49    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 55.64/7.49    inference(definition_unfolding,[],[f77,f94])).
% 55.64/7.49  
% 55.64/7.49  fof(f1,axiom,(
% 55.64/7.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 55.64/7.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.64/7.49  
% 55.64/7.49  fof(f25,plain,(
% 55.64/7.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 55.64/7.49    inference(ennf_transformation,[],[f1])).
% 55.64/7.49  
% 55.64/7.49  fof(f63,plain,(
% 55.64/7.49    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 55.64/7.49    inference(cnf_transformation,[],[f25])).
% 55.64/7.49  
% 55.64/7.49  fof(f2,axiom,(
% 55.64/7.49    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 55.64/7.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.64/7.49  
% 55.64/7.49  fof(f64,plain,(
% 55.64/7.49    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 55.64/7.49    inference(cnf_transformation,[],[f2])).
% 55.64/7.49  
% 55.64/7.49  fof(f16,axiom,(
% 55.64/7.49    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 55.64/7.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.64/7.49  
% 55.64/7.49  fof(f45,plain,(
% 55.64/7.49    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 55.64/7.49    inference(ennf_transformation,[],[f16])).
% 55.64/7.49  
% 55.64/7.49  fof(f46,plain,(
% 55.64/7.49    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 55.64/7.49    inference(flattening,[],[f45])).
% 55.64/7.49  
% 55.64/7.49  fof(f59,plain,(
% 55.64/7.49    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 55.64/7.49    inference(nnf_transformation,[],[f46])).
% 55.64/7.49  
% 55.64/7.49  fof(f89,plain,(
% 55.64/7.49    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 55.64/7.49    inference(cnf_transformation,[],[f59])).
% 55.64/7.49  
% 55.64/7.49  fof(f20,axiom,(
% 55.64/7.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 55.64/7.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.64/7.49  
% 55.64/7.49  fof(f51,plain,(
% 55.64/7.49    ! [X0,X1,X2] : (! [X3] : (((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 55.64/7.49    inference(ennf_transformation,[],[f20])).
% 55.64/7.49  
% 55.64/7.49  fof(f52,plain,(
% 55.64/7.49    ! [X0,X1,X2] : (! [X3] : ((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 55.64/7.49    inference(flattening,[],[f51])).
% 55.64/7.49  
% 55.64/7.49  fof(f96,plain,(
% 55.64/7.49    ( ! [X2,X0,X3,X1] : (v2_funct_2(X3,X0) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 55.64/7.49    inference(cnf_transformation,[],[f52])).
% 55.64/7.49  
% 55.64/7.49  fof(f11,axiom,(
% 55.64/7.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 55.64/7.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.64/7.49  
% 55.64/7.49  fof(f24,plain,(
% 55.64/7.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 55.64/7.49    inference(pure_predicate_removal,[],[f11])).
% 55.64/7.49  
% 55.64/7.49  fof(f39,plain,(
% 55.64/7.49    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 55.64/7.49    inference(ennf_transformation,[],[f24])).
% 55.64/7.49  
% 55.64/7.49  fof(f78,plain,(
% 55.64/7.49    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 55.64/7.49    inference(cnf_transformation,[],[f39])).
% 55.64/7.49  
% 55.64/7.49  fof(f101,plain,(
% 55.64/7.49    v1_funct_2(sK2,sK0,sK1)),
% 55.64/7.49    inference(cnf_transformation,[],[f62])).
% 55.64/7.49  
% 55.64/7.49  fof(f104,plain,(
% 55.64/7.49    v1_funct_2(sK3,sK1,sK0)),
% 55.64/7.49    inference(cnf_transformation,[],[f62])).
% 55.64/7.49  
% 55.64/7.49  fof(f15,axiom,(
% 55.64/7.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 55.64/7.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.64/7.49  
% 55.64/7.49  fof(f43,plain,(
% 55.64/7.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 55.64/7.49    inference(ennf_transformation,[],[f15])).
% 55.64/7.49  
% 55.64/7.49  fof(f44,plain,(
% 55.64/7.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 55.64/7.49    inference(flattening,[],[f43])).
% 55.64/7.49  
% 55.64/7.49  fof(f58,plain,(
% 55.64/7.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 55.64/7.49    inference(nnf_transformation,[],[f44])).
% 55.64/7.49  
% 55.64/7.49  fof(f83,plain,(
% 55.64/7.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 55.64/7.49    inference(cnf_transformation,[],[f58])).
% 55.64/7.49  
% 55.64/7.49  fof(f12,axiom,(
% 55.64/7.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 55.64/7.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.64/7.49  
% 55.64/7.49  fof(f40,plain,(
% 55.64/7.49    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 55.64/7.49    inference(ennf_transformation,[],[f12])).
% 55.64/7.49  
% 55.64/7.49  fof(f79,plain,(
% 55.64/7.49    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 55.64/7.49    inference(cnf_transformation,[],[f40])).
% 55.64/7.49  
% 55.64/7.49  fof(f109,plain,(
% 55.64/7.49    k1_xboole_0 != sK0),
% 55.64/7.49    inference(cnf_transformation,[],[f62])).
% 55.64/7.49  
% 55.64/7.49  fof(f106,plain,(
% 55.64/7.49    k2_relset_1(sK0,sK1,sK2) = sK1),
% 55.64/7.49    inference(cnf_transformation,[],[f62])).
% 55.64/7.49  
% 55.64/7.49  fof(f21,axiom,(
% 55.64/7.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 55.64/7.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.64/7.49  
% 55.64/7.49  fof(f53,plain,(
% 55.64/7.49    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 55.64/7.49    inference(ennf_transformation,[],[f21])).
% 55.64/7.49  
% 55.64/7.49  fof(f54,plain,(
% 55.64/7.49    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 55.64/7.49    inference(flattening,[],[f53])).
% 55.64/7.49  
% 55.64/7.49  fof(f99,plain,(
% 55.64/7.49    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 55.64/7.49    inference(cnf_transformation,[],[f54])).
% 55.64/7.49  
% 55.64/7.49  fof(f4,axiom,(
% 55.64/7.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 55.64/7.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.64/7.49  
% 55.64/7.49  fof(f27,plain,(
% 55.64/7.49    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 55.64/7.49    inference(ennf_transformation,[],[f4])).
% 55.64/7.49  
% 55.64/7.49  fof(f28,plain,(
% 55.64/7.49    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 55.64/7.49    inference(flattening,[],[f27])).
% 55.64/7.49  
% 55.64/7.49  fof(f66,plain,(
% 55.64/7.49    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 55.64/7.49    inference(cnf_transformation,[],[f28])).
% 55.64/7.49  
% 55.64/7.49  fof(f108,plain,(
% 55.64/7.49    v2_funct_1(sK2)),
% 55.64/7.49    inference(cnf_transformation,[],[f62])).
% 55.64/7.49  
% 55.64/7.49  fof(f98,plain,(
% 55.64/7.49    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 55.64/7.49    inference(cnf_transformation,[],[f54])).
% 55.64/7.49  
% 55.64/7.49  fof(f8,axiom,(
% 55.64/7.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 55.64/7.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.64/7.49  
% 55.64/7.49  fof(f33,plain,(
% 55.64/7.49    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 55.64/7.49    inference(ennf_transformation,[],[f8])).
% 55.64/7.49  
% 55.64/7.49  fof(f34,plain,(
% 55.64/7.49    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 55.64/7.49    inference(flattening,[],[f33])).
% 55.64/7.49  
% 55.64/7.49  fof(f73,plain,(
% 55.64/7.49    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 55.64/7.49    inference(cnf_transformation,[],[f34])).
% 55.64/7.49  
% 55.64/7.49  fof(f6,axiom,(
% 55.64/7.49    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 55.64/7.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.64/7.49  
% 55.64/7.49  fof(f70,plain,(
% 55.64/7.49    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 55.64/7.49    inference(cnf_transformation,[],[f6])).
% 55.64/7.49  
% 55.64/7.49  fof(f112,plain,(
% 55.64/7.49    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 55.64/7.49    inference(definition_unfolding,[],[f70,f94])).
% 55.64/7.49  
% 55.64/7.49  fof(f7,axiom,(
% 55.64/7.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 55.64/7.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.64/7.49  
% 55.64/7.49  fof(f31,plain,(
% 55.64/7.49    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 55.64/7.49    inference(ennf_transformation,[],[f7])).
% 55.64/7.49  
% 55.64/7.49  fof(f32,plain,(
% 55.64/7.49    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 55.64/7.49    inference(flattening,[],[f31])).
% 55.64/7.49  
% 55.64/7.49  fof(f72,plain,(
% 55.64/7.49    ( ! [X0,X1] : (v2_funct_1(X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 55.64/7.49    inference(cnf_transformation,[],[f32])).
% 55.64/7.49  
% 55.64/7.49  fof(f3,axiom,(
% 55.64/7.49    ! [X0] : (v1_relat_1(X0) => k4_relat_1(k4_relat_1(X0)) = X0)),
% 55.64/7.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 55.64/7.49  
% 55.64/7.49  fof(f26,plain,(
% 55.64/7.49    ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 55.64/7.49    inference(ennf_transformation,[],[f3])).
% 55.64/7.49  
% 55.64/7.49  fof(f65,plain,(
% 55.64/7.49    ( ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 55.64/7.49    inference(cnf_transformation,[],[f26])).
% 55.64/7.49  
% 55.64/7.49  fof(f111,plain,(
% 55.64/7.49    k2_funct_1(sK2) != sK3),
% 55.64/7.49    inference(cnf_transformation,[],[f62])).
% 55.64/7.49  
% 55.64/7.49  cnf(c_45,negated_conjecture,
% 55.64/7.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 55.64/7.49      inference(cnf_transformation,[],[f102]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_1894,plain,
% 55.64/7.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 55.64/7.49      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_42,negated_conjecture,
% 55.64/7.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 55.64/7.49      inference(cnf_transformation,[],[f105]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_1897,plain,
% 55.64/7.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 55.64/7.49      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_30,plain,
% 55.64/7.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 55.64/7.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 55.64/7.49      | ~ v1_funct_1(X0)
% 55.64/7.49      | ~ v1_funct_1(X3)
% 55.64/7.49      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 55.64/7.49      inference(cnf_transformation,[],[f93]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_1904,plain,
% 55.64/7.49      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 55.64/7.49      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 55.64/7.49      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 55.64/7.49      | v1_funct_1(X5) != iProver_top
% 55.64/7.49      | v1_funct_1(X4) != iProver_top ),
% 55.64/7.49      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_6327,plain,
% 55.64/7.49      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 55.64/7.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 55.64/7.49      | v1_funct_1(X2) != iProver_top
% 55.64/7.49      | v1_funct_1(sK3) != iProver_top ),
% 55.64/7.49      inference(superposition,[status(thm)],[c_1897,c_1904]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_44,negated_conjecture,
% 55.64/7.49      ( v1_funct_1(sK3) ),
% 55.64/7.49      inference(cnf_transformation,[],[f103]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_51,plain,
% 55.64/7.49      ( v1_funct_1(sK3) = iProver_top ),
% 55.64/7.49      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_6595,plain,
% 55.64/7.49      ( v1_funct_1(X2) != iProver_top
% 55.64/7.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 55.64/7.49      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 55.64/7.49      inference(global_propositional_subsumption,
% 55.64/7.49                [status(thm)],
% 55.64/7.49                [c_6327,c_51]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_6596,plain,
% 55.64/7.49      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 55.64/7.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 55.64/7.49      | v1_funct_1(X2) != iProver_top ),
% 55.64/7.49      inference(renaming,[status(thm)],[c_6595]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_6604,plain,
% 55.64/7.49      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 55.64/7.49      | v1_funct_1(sK2) != iProver_top ),
% 55.64/7.49      inference(superposition,[status(thm)],[c_1894,c_6596]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_47,negated_conjecture,
% 55.64/7.49      ( v1_funct_1(sK2) ),
% 55.64/7.49      inference(cnf_transformation,[],[f100]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_48,plain,
% 55.64/7.49      ( v1_funct_1(sK2) = iProver_top ),
% 55.64/7.49      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_6694,plain,
% 55.64/7.49      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 55.64/7.49      inference(global_propositional_subsumption,
% 55.64/7.49                [status(thm)],
% 55.64/7.49                [c_6604,c_48]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_40,negated_conjecture,
% 55.64/7.49      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 55.64/7.49      inference(cnf_transformation,[],[f107]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_1898,plain,
% 55.64/7.49      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) = iProver_top ),
% 55.64/7.49      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_6696,plain,
% 55.64/7.49      ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) = iProver_top ),
% 55.64/7.49      inference(demodulation,[status(thm)],[c_6694,c_1898]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_28,plain,
% 55.64/7.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 55.64/7.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 55.64/7.49      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 55.64/7.49      | ~ v1_funct_1(X0)
% 55.64/7.49      | ~ v1_funct_1(X3) ),
% 55.64/7.49      inference(cnf_transformation,[],[f92]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_1906,plain,
% 55.64/7.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 55.64/7.49      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 55.64/7.49      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 55.64/7.49      | v1_funct_1(X0) != iProver_top
% 55.64/7.49      | v1_funct_1(X3) != iProver_top ),
% 55.64/7.49      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_6698,plain,
% 55.64/7.49      ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 55.64/7.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 55.64/7.49      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 55.64/7.49      | v1_funct_1(sK3) != iProver_top
% 55.64/7.49      | v1_funct_1(sK2) != iProver_top ),
% 55.64/7.49      inference(superposition,[status(thm)],[c_6694,c_1906]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_50,plain,
% 55.64/7.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 55.64/7.49      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_53,plain,
% 55.64/7.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 55.64/7.49      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_10906,plain,
% 55.64/7.49      ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 55.64/7.49      inference(global_propositional_subsumption,
% 55.64/7.49                [status(thm)],
% 55.64/7.49                [c_6698,c_48,c_50,c_51,c_53]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_18,plain,
% 55.64/7.49      ( ~ r2_relset_1(X0,X1,X2,X3)
% 55.64/7.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 55.64/7.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 55.64/7.49      | X3 = X2 ),
% 55.64/7.49      inference(cnf_transformation,[],[f80]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_1914,plain,
% 55.64/7.49      ( X0 = X1
% 55.64/7.49      | r2_relset_1(X2,X3,X1,X0) != iProver_top
% 55.64/7.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 55.64/7.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top ),
% 55.64/7.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_10918,plain,
% 55.64/7.49      ( k5_relat_1(sK2,sK3) = X0
% 55.64/7.49      | r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),X0) != iProver_top
% 55.64/7.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 55.64/7.49      inference(superposition,[status(thm)],[c_10906,c_1914]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_17235,plain,
% 55.64/7.49      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 55.64/7.49      | m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 55.64/7.49      inference(superposition,[status(thm)],[c_6696,c_10918]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_19,plain,
% 55.64/7.49      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 55.64/7.49      inference(cnf_transformation,[],[f117]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_2239,plain,
% 55.64/7.49      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 55.64/7.49      inference(instantiation,[status(thm)],[c_19]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_2240,plain,
% 55.64/7.49      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 55.64/7.49      inference(predicate_to_equality,[status(thm)],[c_2239]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_17805,plain,
% 55.64/7.49      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 55.64/7.49      inference(global_propositional_subsumption,
% 55.64/7.49                [status(thm)],
% 55.64/7.49                [c_17235,c_2240]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_14,plain,
% 55.64/7.49      ( ~ v1_funct_1(X0)
% 55.64/7.49      | ~ v1_funct_1(X1)
% 55.64/7.49      | ~ v2_funct_1(X0)
% 55.64/7.49      | ~ v1_relat_1(X0)
% 55.64/7.49      | ~ v1_relat_1(X1)
% 55.64/7.49      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
% 55.64/7.49      | k1_relat_1(X0) != k2_relat_1(X1)
% 55.64/7.49      | k2_funct_1(X0) = X1 ),
% 55.64/7.49      inference(cnf_transformation,[],[f116]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_1917,plain,
% 55.64/7.49      ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 55.64/7.49      | k1_relat_1(X1) != k2_relat_1(X0)
% 55.64/7.49      | k2_funct_1(X1) = X0
% 55.64/7.49      | v1_funct_1(X1) != iProver_top
% 55.64/7.49      | v1_funct_1(X0) != iProver_top
% 55.64/7.49      | v2_funct_1(X1) != iProver_top
% 55.64/7.49      | v1_relat_1(X1) != iProver_top
% 55.64/7.49      | v1_relat_1(X0) != iProver_top ),
% 55.64/7.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_17827,plain,
% 55.64/7.49      ( k1_relat_1(sK3) != k2_relat_1(sK2)
% 55.64/7.49      | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
% 55.64/7.49      | k2_funct_1(sK3) = sK2
% 55.64/7.49      | v1_funct_1(sK3) != iProver_top
% 55.64/7.49      | v1_funct_1(sK2) != iProver_top
% 55.64/7.49      | v2_funct_1(sK3) != iProver_top
% 55.64/7.49      | v1_relat_1(sK3) != iProver_top
% 55.64/7.49      | v1_relat_1(sK2) != iProver_top ),
% 55.64/7.49      inference(superposition,[status(thm)],[c_17805,c_1917]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_0,plain,
% 55.64/7.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 55.64/7.49      | ~ v1_relat_1(X1)
% 55.64/7.49      | v1_relat_1(X0) ),
% 55.64/7.49      inference(cnf_transformation,[],[f63]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_1931,plain,
% 55.64/7.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 55.64/7.49      | v1_relat_1(X1) != iProver_top
% 55.64/7.49      | v1_relat_1(X0) = iProver_top ),
% 55.64/7.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_3742,plain,
% 55.64/7.49      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 55.64/7.49      | v1_relat_1(sK3) = iProver_top ),
% 55.64/7.49      inference(superposition,[status(thm)],[c_1897,c_1931]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_2054,plain,
% 55.64/7.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
% 55.64/7.49      | ~ v1_relat_1(X0)
% 55.64/7.49      | v1_relat_1(sK3) ),
% 55.64/7.49      inference(instantiation,[status(thm)],[c_0]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_2262,plain,
% 55.64/7.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 55.64/7.49      | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
% 55.64/7.49      | v1_relat_1(sK3) ),
% 55.64/7.49      inference(instantiation,[status(thm)],[c_2054]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_2812,plain,
% 55.64/7.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 55.64/7.49      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
% 55.64/7.49      | v1_relat_1(sK3) ),
% 55.64/7.49      inference(instantiation,[status(thm)],[c_2262]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_2813,plain,
% 55.64/7.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 55.64/7.49      | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 55.64/7.49      | v1_relat_1(sK3) = iProver_top ),
% 55.64/7.49      inference(predicate_to_equality,[status(thm)],[c_2812]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_1,plain,
% 55.64/7.49      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 55.64/7.49      inference(cnf_transformation,[],[f64]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_3282,plain,
% 55.64/7.49      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
% 55.64/7.49      inference(instantiation,[status(thm)],[c_1]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_3283,plain,
% 55.64/7.49      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
% 55.64/7.49      inference(predicate_to_equality,[status(thm)],[c_3282]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_4218,plain,
% 55.64/7.49      ( v1_relat_1(sK3) = iProver_top ),
% 55.64/7.49      inference(global_propositional_subsumption,
% 55.64/7.49                [status(thm)],
% 55.64/7.49                [c_3742,c_53,c_2813,c_3283]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_27,plain,
% 55.64/7.49      ( ~ v2_funct_2(X0,X1)
% 55.64/7.49      | ~ v5_relat_1(X0,X1)
% 55.64/7.49      | ~ v1_relat_1(X0)
% 55.64/7.49      | k2_relat_1(X0) = X1 ),
% 55.64/7.49      inference(cnf_transformation,[],[f89]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_31,plain,
% 55.64/7.49      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 55.64/7.49      | ~ v1_funct_2(X2,X0,X1)
% 55.64/7.49      | ~ v1_funct_2(X3,X1,X0)
% 55.64/7.49      | v2_funct_2(X3,X0)
% 55.64/7.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 55.64/7.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 55.64/7.49      | ~ v1_funct_1(X3)
% 55.64/7.49      | ~ v1_funct_1(X2) ),
% 55.64/7.49      inference(cnf_transformation,[],[f96]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_535,plain,
% 55.64/7.49      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 55.64/7.49      | ~ v1_funct_2(X2,X0,X1)
% 55.64/7.49      | ~ v1_funct_2(X3,X1,X0)
% 55.64/7.49      | ~ v5_relat_1(X4,X5)
% 55.64/7.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 55.64/7.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 55.64/7.49      | ~ v1_funct_1(X2)
% 55.64/7.49      | ~ v1_funct_1(X3)
% 55.64/7.49      | ~ v1_relat_1(X4)
% 55.64/7.49      | X3 != X4
% 55.64/7.49      | X0 != X5
% 55.64/7.49      | k2_relat_1(X4) = X5 ),
% 55.64/7.49      inference(resolution_lifted,[status(thm)],[c_27,c_31]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_536,plain,
% 55.64/7.49      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 55.64/7.49      | ~ v1_funct_2(X2,X0,X1)
% 55.64/7.49      | ~ v1_funct_2(X3,X1,X0)
% 55.64/7.49      | ~ v5_relat_1(X3,X0)
% 55.64/7.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 55.64/7.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 55.64/7.49      | ~ v1_funct_1(X3)
% 55.64/7.49      | ~ v1_funct_1(X2)
% 55.64/7.49      | ~ v1_relat_1(X3)
% 55.64/7.49      | k2_relat_1(X3) = X0 ),
% 55.64/7.49      inference(unflattening,[status(thm)],[c_535]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_15,plain,
% 55.64/7.49      ( v5_relat_1(X0,X1)
% 55.64/7.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 55.64/7.49      inference(cnf_transformation,[],[f78]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_560,plain,
% 55.64/7.49      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 55.64/7.49      | ~ v1_funct_2(X2,X0,X1)
% 55.64/7.49      | ~ v1_funct_2(X3,X1,X0)
% 55.64/7.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 55.64/7.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 55.64/7.49      | ~ v1_funct_1(X3)
% 55.64/7.49      | ~ v1_funct_1(X2)
% 55.64/7.49      | ~ v1_relat_1(X3)
% 55.64/7.49      | k2_relat_1(X3) = X0 ),
% 55.64/7.49      inference(forward_subsumption_resolution,
% 55.64/7.49                [status(thm)],
% 55.64/7.49                [c_536,c_15]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_1891,plain,
% 55.64/7.49      ( k2_relat_1(X0) = X1
% 55.64/7.49      | r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X0),k6_partfun1(X1)) != iProver_top
% 55.64/7.49      | v1_funct_2(X3,X1,X2) != iProver_top
% 55.64/7.49      | v1_funct_2(X0,X2,X1) != iProver_top
% 55.64/7.49      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 55.64/7.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 55.64/7.49      | v1_funct_1(X3) != iProver_top
% 55.64/7.49      | v1_funct_1(X0) != iProver_top
% 55.64/7.49      | v1_relat_1(X0) != iProver_top ),
% 55.64/7.49      inference(predicate_to_equality,[status(thm)],[c_560]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_2711,plain,
% 55.64/7.49      ( k2_relat_1(sK3) = sK0
% 55.64/7.49      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 55.64/7.49      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 55.64/7.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 55.64/7.49      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 55.64/7.49      | v1_funct_1(sK3) != iProver_top
% 55.64/7.49      | v1_funct_1(sK2) != iProver_top
% 55.64/7.49      | v1_relat_1(sK3) != iProver_top ),
% 55.64/7.49      inference(superposition,[status(thm)],[c_1898,c_1891]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_46,negated_conjecture,
% 55.64/7.49      ( v1_funct_2(sK2,sK0,sK1) ),
% 55.64/7.49      inference(cnf_transformation,[],[f101]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_49,plain,
% 55.64/7.49      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 55.64/7.49      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_43,negated_conjecture,
% 55.64/7.49      ( v1_funct_2(sK3,sK1,sK0) ),
% 55.64/7.49      inference(cnf_transformation,[],[f104]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_52,plain,
% 55.64/7.49      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 55.64/7.49      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_2775,plain,
% 55.64/7.49      ( k2_relat_1(sK3) = sK0 | v1_relat_1(sK3) != iProver_top ),
% 55.64/7.49      inference(global_propositional_subsumption,
% 55.64/7.49                [status(thm)],
% 55.64/7.49                [c_2711,c_48,c_49,c_50,c_51,c_52,c_53]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_4223,plain,
% 55.64/7.49      ( k2_relat_1(sK3) = sK0 ),
% 55.64/7.49      inference(superposition,[status(thm)],[c_4218,c_2775]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_25,plain,
% 55.64/7.49      ( ~ v1_funct_2(X0,X1,X2)
% 55.64/7.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 55.64/7.49      | k1_relset_1(X1,X2,X0) = X1
% 55.64/7.49      | k1_xboole_0 = X2 ),
% 55.64/7.49      inference(cnf_transformation,[],[f83]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_1907,plain,
% 55.64/7.49      ( k1_relset_1(X0,X1,X2) = X0
% 55.64/7.49      | k1_xboole_0 = X1
% 55.64/7.49      | v1_funct_2(X2,X0,X1) != iProver_top
% 55.64/7.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 55.64/7.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_5771,plain,
% 55.64/7.49      ( k1_relset_1(sK1,sK0,sK3) = sK1
% 55.64/7.49      | sK0 = k1_xboole_0
% 55.64/7.49      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 55.64/7.49      inference(superposition,[status(thm)],[c_1897,c_1907]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_16,plain,
% 55.64/7.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 55.64/7.49      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 55.64/7.49      inference(cnf_transformation,[],[f79]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_1916,plain,
% 55.64/7.49      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 55.64/7.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 55.64/7.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_3171,plain,
% 55.64/7.49      ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
% 55.64/7.49      inference(superposition,[status(thm)],[c_1897,c_1916]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_5776,plain,
% 55.64/7.49      ( k1_relat_1(sK3) = sK1
% 55.64/7.49      | sK0 = k1_xboole_0
% 55.64/7.49      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 55.64/7.49      inference(demodulation,[status(thm)],[c_5771,c_3171]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_38,negated_conjecture,
% 55.64/7.49      ( k1_xboole_0 != sK0 ),
% 55.64/7.49      inference(cnf_transformation,[],[f109]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_1234,plain,( X0 = X0 ),theory(equality) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_1271,plain,
% 55.64/7.49      ( k1_xboole_0 = k1_xboole_0 ),
% 55.64/7.49      inference(instantiation,[status(thm)],[c_1234]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_1235,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_2035,plain,
% 55.64/7.49      ( sK0 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK0 ),
% 55.64/7.49      inference(instantiation,[status(thm)],[c_1235]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_2036,plain,
% 55.64/7.49      ( sK0 != k1_xboole_0
% 55.64/7.49      | k1_xboole_0 = sK0
% 55.64/7.49      | k1_xboole_0 != k1_xboole_0 ),
% 55.64/7.49      inference(instantiation,[status(thm)],[c_2035]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_13198,plain,
% 55.64/7.49      ( k1_relat_1(sK3) = sK1 ),
% 55.64/7.49      inference(global_propositional_subsumption,
% 55.64/7.49                [status(thm)],
% 55.64/7.49                [c_5776,c_52,c_38,c_1271,c_2036]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_41,negated_conjecture,
% 55.64/7.49      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 55.64/7.49      inference(cnf_transformation,[],[f106]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_33,plain,
% 55.64/7.49      ( ~ v1_funct_2(X0,X1,X2)
% 55.64/7.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 55.64/7.49      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 55.64/7.49      | ~ v1_funct_1(X0)
% 55.64/7.49      | ~ v2_funct_1(X0)
% 55.64/7.49      | k2_relset_1(X1,X2,X0) != X2 ),
% 55.64/7.49      inference(cnf_transformation,[],[f99]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_1902,plain,
% 55.64/7.49      ( k2_relset_1(X0,X1,X2) != X1
% 55.64/7.49      | v1_funct_2(X2,X0,X1) != iProver_top
% 55.64/7.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 55.64/7.49      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
% 55.64/7.49      | v1_funct_1(X2) != iProver_top
% 55.64/7.49      | v2_funct_1(X2) != iProver_top ),
% 55.64/7.49      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_4515,plain,
% 55.64/7.49      ( v1_funct_2(sK2,sK0,sK1) != iProver_top
% 55.64/7.49      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
% 55.64/7.49      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 55.64/7.49      | v1_funct_1(sK2) != iProver_top
% 55.64/7.49      | v2_funct_1(sK2) != iProver_top ),
% 55.64/7.49      inference(superposition,[status(thm)],[c_41,c_1902]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_1892,plain,
% 55.64/7.49      ( v1_funct_1(sK2) = iProver_top ),
% 55.64/7.49      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_3,plain,
% 55.64/7.49      ( ~ v1_funct_1(X0)
% 55.64/7.49      | ~ v2_funct_1(X0)
% 55.64/7.49      | ~ v1_relat_1(X0)
% 55.64/7.49      | k2_funct_1(X0) = k4_relat_1(X0) ),
% 55.64/7.49      inference(cnf_transformation,[],[f66]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_1928,plain,
% 55.64/7.49      ( k2_funct_1(X0) = k4_relat_1(X0)
% 55.64/7.49      | v1_funct_1(X0) != iProver_top
% 55.64/7.49      | v2_funct_1(X0) != iProver_top
% 55.64/7.49      | v1_relat_1(X0) != iProver_top ),
% 55.64/7.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_3928,plain,
% 55.64/7.49      ( k2_funct_1(sK2) = k4_relat_1(sK2)
% 55.64/7.49      | v2_funct_1(sK2) != iProver_top
% 55.64/7.49      | v1_relat_1(sK2) != iProver_top ),
% 55.64/7.49      inference(superposition,[status(thm)],[c_1892,c_1928]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_39,negated_conjecture,
% 55.64/7.49      ( v2_funct_1(sK2) ),
% 55.64/7.49      inference(cnf_transformation,[],[f108]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_55,plain,
% 55.64/7.49      ( v2_funct_1(sK2) = iProver_top ),
% 55.64/7.49      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_1930,plain,
% 55.64/7.49      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 55.64/7.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_3743,plain,
% 55.64/7.49      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 55.64/7.49      | v1_relat_1(sK2) = iProver_top ),
% 55.64/7.49      inference(superposition,[status(thm)],[c_1894,c_1931]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_4225,plain,
% 55.64/7.49      ( v1_relat_1(sK2) = iProver_top ),
% 55.64/7.49      inference(superposition,[status(thm)],[c_1930,c_3743]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_4415,plain,
% 55.64/7.49      ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 55.64/7.49      inference(global_propositional_subsumption,
% 55.64/7.49                [status(thm)],
% 55.64/7.49                [c_3928,c_55,c_4225]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_4516,plain,
% 55.64/7.49      ( v1_funct_2(sK2,sK0,sK1) != iProver_top
% 55.64/7.49      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
% 55.64/7.49      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 55.64/7.49      | v1_funct_1(sK2) != iProver_top
% 55.64/7.49      | v2_funct_1(sK2) != iProver_top ),
% 55.64/7.49      inference(light_normalisation,[status(thm)],[c_4515,c_4415]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_5269,plain,
% 55.64/7.49      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 55.64/7.49      inference(global_propositional_subsumption,
% 55.64/7.49                [status(thm)],
% 55.64/7.49                [c_4516,c_48,c_49,c_50,c_55]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_5773,plain,
% 55.64/7.49      ( k1_relset_1(sK1,sK0,k4_relat_1(sK2)) = sK1
% 55.64/7.49      | sK0 = k1_xboole_0
% 55.64/7.49      | v1_funct_2(k4_relat_1(sK2),sK1,sK0) != iProver_top ),
% 55.64/7.49      inference(superposition,[status(thm)],[c_5269,c_1907]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_5274,plain,
% 55.64/7.49      ( k1_relset_1(sK1,sK0,k4_relat_1(sK2)) = k1_relat_1(k4_relat_1(sK2)) ),
% 55.64/7.49      inference(superposition,[status(thm)],[c_5269,c_1916]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_5774,plain,
% 55.64/7.49      ( k1_relat_1(k4_relat_1(sK2)) = sK1
% 55.64/7.49      | sK0 = k1_xboole_0
% 55.64/7.49      | v1_funct_2(k4_relat_1(sK2),sK1,sK0) != iProver_top ),
% 55.64/7.49      inference(demodulation,[status(thm)],[c_5773,c_5274]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_34,plain,
% 55.64/7.49      ( ~ v1_funct_2(X0,X1,X2)
% 55.64/7.49      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 55.64/7.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 55.64/7.49      | ~ v1_funct_1(X0)
% 55.64/7.49      | ~ v2_funct_1(X0)
% 55.64/7.49      | k2_relset_1(X1,X2,X0) != X2 ),
% 55.64/7.49      inference(cnf_transformation,[],[f98]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_1901,plain,
% 55.64/7.49      ( k2_relset_1(X0,X1,X2) != X1
% 55.64/7.49      | v1_funct_2(X2,X0,X1) != iProver_top
% 55.64/7.49      | v1_funct_2(k2_funct_1(X2),X1,X0) = iProver_top
% 55.64/7.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 55.64/7.49      | v1_funct_1(X2) != iProver_top
% 55.64/7.49      | v2_funct_1(X2) != iProver_top ),
% 55.64/7.49      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_3830,plain,
% 55.64/7.49      ( v1_funct_2(k2_funct_1(sK2),sK1,sK0) = iProver_top
% 55.64/7.49      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 55.64/7.49      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 55.64/7.49      | v1_funct_1(sK2) != iProver_top
% 55.64/7.49      | v2_funct_1(sK2) != iProver_top ),
% 55.64/7.49      inference(superposition,[status(thm)],[c_41,c_1901]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_4073,plain,
% 55.64/7.49      ( v1_funct_2(k2_funct_1(sK2),sK1,sK0) = iProver_top ),
% 55.64/7.49      inference(global_propositional_subsumption,
% 55.64/7.49                [status(thm)],
% 55.64/7.49                [c_3830,c_48,c_49,c_50,c_55]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_4417,plain,
% 55.64/7.49      ( v1_funct_2(k4_relat_1(sK2),sK1,sK0) = iProver_top ),
% 55.64/7.49      inference(demodulation,[status(thm)],[c_4415,c_4073]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_14265,plain,
% 55.64/7.49      ( k1_relat_1(k4_relat_1(sK2)) = sK1 ),
% 55.64/7.49      inference(global_propositional_subsumption,
% 55.64/7.49                [status(thm)],
% 55.64/7.49                [c_5774,c_38,c_1271,c_2036,c_4417]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_11,plain,
% 55.64/7.49      ( ~ v1_funct_1(X0)
% 55.64/7.49      | ~ v2_funct_1(X0)
% 55.64/7.49      | ~ v1_relat_1(X0)
% 55.64/7.49      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 55.64/7.49      inference(cnf_transformation,[],[f73]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_1920,plain,
% 55.64/7.49      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 55.64/7.49      | v1_funct_1(X0) != iProver_top
% 55.64/7.49      | v2_funct_1(X0) != iProver_top
% 55.64/7.49      | v1_relat_1(X0) != iProver_top ),
% 55.64/7.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_4923,plain,
% 55.64/7.49      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 55.64/7.49      | v2_funct_1(sK2) != iProver_top
% 55.64/7.49      | v1_relat_1(sK2) != iProver_top ),
% 55.64/7.49      inference(superposition,[status(thm)],[c_1892,c_1920]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_4925,plain,
% 55.64/7.49      ( k1_relat_1(k4_relat_1(sK2)) = k2_relat_1(sK2)
% 55.64/7.49      | v2_funct_1(sK2) != iProver_top
% 55.64/7.49      | v1_relat_1(sK2) != iProver_top ),
% 55.64/7.49      inference(light_normalisation,[status(thm)],[c_4923,c_4415]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_6943,plain,
% 55.64/7.49      ( k1_relat_1(k4_relat_1(sK2)) = k2_relat_1(sK2) ),
% 55.64/7.49      inference(global_propositional_subsumption,
% 55.64/7.49                [status(thm)],
% 55.64/7.49                [c_4925,c_55,c_4225]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_14267,plain,
% 55.64/7.49      ( k2_relat_1(sK2) = sK1 ),
% 55.64/7.49      inference(demodulation,[status(thm)],[c_14265,c_6943]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_17828,plain,
% 55.64/7.49      ( k6_partfun1(sK0) != k6_partfun1(sK0)
% 55.64/7.49      | k2_funct_1(sK3) = sK2
% 55.64/7.49      | sK1 != sK1
% 55.64/7.49      | v1_funct_1(sK3) != iProver_top
% 55.64/7.49      | v1_funct_1(sK2) != iProver_top
% 55.64/7.49      | v2_funct_1(sK3) != iProver_top
% 55.64/7.49      | v1_relat_1(sK3) != iProver_top
% 55.64/7.49      | v1_relat_1(sK2) != iProver_top ),
% 55.64/7.49      inference(light_normalisation,
% 55.64/7.49                [status(thm)],
% 55.64/7.49                [c_17827,c_4223,c_13198,c_14267]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_17829,plain,
% 55.64/7.49      ( k2_funct_1(sK3) = sK2
% 55.64/7.49      | v1_funct_1(sK3) != iProver_top
% 55.64/7.49      | v1_funct_1(sK2) != iProver_top
% 55.64/7.49      | v2_funct_1(sK3) != iProver_top
% 55.64/7.49      | v1_relat_1(sK3) != iProver_top
% 55.64/7.49      | v1_relat_1(sK2) != iProver_top ),
% 55.64/7.49      inference(equality_resolution_simp,[status(thm)],[c_17828]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_6,plain,
% 55.64/7.49      ( v2_funct_1(k6_partfun1(X0)) ),
% 55.64/7.49      inference(cnf_transformation,[],[f112]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_1925,plain,
% 55.64/7.49      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 55.64/7.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_8,plain,
% 55.64/7.49      ( ~ v1_funct_1(X0)
% 55.64/7.49      | ~ v1_funct_1(X1)
% 55.64/7.49      | v2_funct_1(X0)
% 55.64/7.49      | ~ v2_funct_1(k5_relat_1(X1,X0))
% 55.64/7.49      | ~ v1_relat_1(X0)
% 55.64/7.49      | ~ v1_relat_1(X1)
% 55.64/7.49      | k1_relat_1(X0) != k2_relat_1(X1) ),
% 55.64/7.49      inference(cnf_transformation,[],[f72]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_1923,plain,
% 55.64/7.49      ( k1_relat_1(X0) != k2_relat_1(X1)
% 55.64/7.49      | v1_funct_1(X0) != iProver_top
% 55.64/7.49      | v1_funct_1(X1) != iProver_top
% 55.64/7.49      | v2_funct_1(X0) = iProver_top
% 55.64/7.49      | v2_funct_1(k5_relat_1(X1,X0)) != iProver_top
% 55.64/7.49      | v1_relat_1(X0) != iProver_top
% 55.64/7.49      | v1_relat_1(X1) != iProver_top ),
% 55.64/7.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_13205,plain,
% 55.64/7.49      ( k2_relat_1(X0) != sK1
% 55.64/7.49      | v1_funct_1(X0) != iProver_top
% 55.64/7.49      | v1_funct_1(sK3) != iProver_top
% 55.64/7.49      | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
% 55.64/7.49      | v2_funct_1(sK3) = iProver_top
% 55.64/7.49      | v1_relat_1(X0) != iProver_top
% 55.64/7.49      | v1_relat_1(sK3) != iProver_top ),
% 55.64/7.49      inference(superposition,[status(thm)],[c_13198,c_1923]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_103407,plain,
% 55.64/7.49      ( v1_relat_1(X0) != iProver_top
% 55.64/7.49      | v2_funct_1(sK3) = iProver_top
% 55.64/7.49      | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
% 55.64/7.49      | k2_relat_1(X0) != sK1
% 55.64/7.49      | v1_funct_1(X0) != iProver_top ),
% 55.64/7.49      inference(global_propositional_subsumption,
% 55.64/7.49                [status(thm)],
% 55.64/7.49                [c_13205,c_51,c_53,c_2813,c_3283]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_103408,plain,
% 55.64/7.49      ( k2_relat_1(X0) != sK1
% 55.64/7.49      | v1_funct_1(X0) != iProver_top
% 55.64/7.49      | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
% 55.64/7.49      | v2_funct_1(sK3) = iProver_top
% 55.64/7.49      | v1_relat_1(X0) != iProver_top ),
% 55.64/7.49      inference(renaming,[status(thm)],[c_103407]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_103413,plain,
% 55.64/7.49      ( v1_funct_1(sK2) != iProver_top
% 55.64/7.49      | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
% 55.64/7.49      | v2_funct_1(sK3) = iProver_top
% 55.64/7.49      | v1_relat_1(sK2) != iProver_top ),
% 55.64/7.49      inference(superposition,[status(thm)],[c_14267,c_103408]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_103418,plain,
% 55.64/7.49      ( v1_funct_1(sK2) != iProver_top
% 55.64/7.49      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 55.64/7.49      | v2_funct_1(sK3) = iProver_top
% 55.64/7.49      | v1_relat_1(sK2) != iProver_top ),
% 55.64/7.49      inference(light_normalisation,[status(thm)],[c_103413,c_17805]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_111490,plain,
% 55.64/7.49      ( v2_funct_1(sK3) = iProver_top
% 55.64/7.49      | v2_funct_1(k6_partfun1(sK0)) != iProver_top ),
% 55.64/7.49      inference(global_propositional_subsumption,
% 55.64/7.49                [status(thm)],
% 55.64/7.49                [c_103418,c_48,c_4225]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_111491,plain,
% 55.64/7.49      ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 55.64/7.49      | v2_funct_1(sK3) = iProver_top ),
% 55.64/7.49      inference(renaming,[status(thm)],[c_111490]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_111494,plain,
% 55.64/7.49      ( v2_funct_1(sK3) = iProver_top ),
% 55.64/7.49      inference(superposition,[status(thm)],[c_1925,c_111491]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_165238,plain,
% 55.64/7.49      ( k2_funct_1(sK3) = sK2 ),
% 55.64/7.49      inference(global_propositional_subsumption,
% 55.64/7.49                [status(thm)],
% 55.64/7.49                [c_17829,c_48,c_51,c_53,c_2813,c_3283,c_4225,c_111494]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_1895,plain,
% 55.64/7.49      ( v1_funct_1(sK3) = iProver_top ),
% 55.64/7.49      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_3927,plain,
% 55.64/7.49      ( k2_funct_1(sK3) = k4_relat_1(sK3)
% 55.64/7.49      | v2_funct_1(sK3) != iProver_top
% 55.64/7.49      | v1_relat_1(sK3) != iProver_top ),
% 55.64/7.49      inference(superposition,[status(thm)],[c_1895,c_1928]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_4410,plain,
% 55.64/7.49      ( v2_funct_1(sK3) != iProver_top
% 55.64/7.49      | k2_funct_1(sK3) = k4_relat_1(sK3) ),
% 55.64/7.49      inference(global_propositional_subsumption,
% 55.64/7.49                [status(thm)],
% 55.64/7.49                [c_3927,c_53,c_2813,c_3283]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_4411,plain,
% 55.64/7.49      ( k2_funct_1(sK3) = k4_relat_1(sK3)
% 55.64/7.49      | v2_funct_1(sK3) != iProver_top ),
% 55.64/7.49      inference(renaming,[status(thm)],[c_4410]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_111501,plain,
% 55.64/7.49      ( k2_funct_1(sK3) = k4_relat_1(sK3) ),
% 55.64/7.49      inference(superposition,[status(thm)],[c_111494,c_4411]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_165240,plain,
% 55.64/7.49      ( k4_relat_1(sK3) = sK2 ),
% 55.64/7.49      inference(demodulation,[status(thm)],[c_165238,c_111501]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_2,plain,
% 55.64/7.49      ( ~ v1_relat_1(X0) | k4_relat_1(k4_relat_1(X0)) = X0 ),
% 55.64/7.49      inference(cnf_transformation,[],[f65]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_1929,plain,
% 55.64/7.49      ( k4_relat_1(k4_relat_1(X0)) = X0 | v1_relat_1(X0) != iProver_top ),
% 55.64/7.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_4222,plain,
% 55.64/7.49      ( k4_relat_1(k4_relat_1(sK3)) = sK3 ),
% 55.64/7.49      inference(superposition,[status(thm)],[c_4218,c_1929]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_165926,plain,
% 55.64/7.49      ( k4_relat_1(sK2) = sK3 ),
% 55.64/7.49      inference(demodulation,[status(thm)],[c_165240,c_4222]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_36,negated_conjecture,
% 55.64/7.49      ( k2_funct_1(sK2) != sK3 ),
% 55.64/7.49      inference(cnf_transformation,[],[f111]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(c_4419,plain,
% 55.64/7.49      ( k4_relat_1(sK2) != sK3 ),
% 55.64/7.49      inference(demodulation,[status(thm)],[c_4415,c_36]) ).
% 55.64/7.49  
% 55.64/7.49  cnf(contradiction,plain,
% 55.64/7.49      ( $false ),
% 55.64/7.49      inference(minisat,[status(thm)],[c_165926,c_4419]) ).
% 55.64/7.49  
% 55.64/7.49  
% 55.64/7.49  % SZS output end CNFRefutation for theBenchmark.p
% 55.64/7.49  
% 55.64/7.49  ------                               Statistics
% 55.64/7.49  
% 55.64/7.49  ------ General
% 55.64/7.49  
% 55.64/7.49  abstr_ref_over_cycles:                  0
% 55.64/7.49  abstr_ref_under_cycles:                 0
% 55.64/7.49  gc_basic_clause_elim:                   0
% 55.64/7.49  forced_gc_time:                         0
% 55.64/7.49  parsing_time:                           0.011
% 55.64/7.49  unif_index_cands_time:                  0.
% 55.64/7.49  unif_index_add_time:                    0.
% 55.64/7.49  orderings_time:                         0.
% 55.64/7.49  out_proof_time:                         0.05
% 55.64/7.49  total_time:                             6.787
% 55.64/7.49  num_of_symbols:                         55
% 55.64/7.49  num_of_terms:                           185478
% 55.64/7.49  
% 55.64/7.49  ------ Preprocessing
% 55.64/7.49  
% 55.64/7.49  num_of_splits:                          0
% 55.64/7.49  num_of_split_atoms:                     0
% 55.64/7.49  num_of_reused_defs:                     0
% 55.64/7.49  num_eq_ax_congr_red:                    8
% 55.64/7.49  num_of_sem_filtered_clauses:            1
% 55.64/7.49  num_of_subtypes:                        0
% 55.64/7.49  monotx_restored_types:                  0
% 55.64/7.49  sat_num_of_epr_types:                   0
% 55.64/7.49  sat_num_of_non_cyclic_types:            0
% 55.64/7.49  sat_guarded_non_collapsed_types:        0
% 55.64/7.49  num_pure_diseq_elim:                    0
% 55.64/7.49  simp_replaced_by:                       0
% 55.64/7.49  res_preprocessed:                       222
% 55.64/7.49  prep_upred:                             0
% 55.64/7.49  prep_unflattend:                        38
% 55.64/7.49  smt_new_axioms:                         0
% 55.64/7.49  pred_elim_cands:                        6
% 55.64/7.49  pred_elim:                              2
% 55.64/7.49  pred_elim_cl:                           3
% 55.64/7.49  pred_elim_cycles:                       5
% 55.64/7.49  merged_defs:                            0
% 55.64/7.49  merged_defs_ncl:                        0
% 55.64/7.49  bin_hyper_res:                          0
% 55.64/7.49  prep_cycles:                            4
% 55.64/7.49  pred_elim_time:                         0.015
% 55.64/7.49  splitting_time:                         0.
% 55.64/7.49  sem_filter_time:                        0.
% 55.64/7.49  monotx_time:                            0.001
% 55.64/7.49  subtype_inf_time:                       0.
% 55.64/7.49  
% 55.64/7.49  ------ Problem properties
% 55.64/7.49  
% 55.64/7.49  clauses:                                45
% 55.64/7.49  conjectures:                            12
% 55.64/7.49  epr:                                    7
% 55.64/7.49  horn:                                   41
% 55.64/7.49  ground:                                 12
% 55.64/7.49  unary:                                  16
% 55.64/7.49  binary:                                 3
% 55.64/7.49  lits:                                   148
% 55.64/7.49  lits_eq:                                31
% 55.64/7.49  fd_pure:                                0
% 55.64/7.49  fd_pseudo:                              0
% 55.64/7.49  fd_cond:                                3
% 55.64/7.49  fd_pseudo_cond:                         3
% 55.64/7.49  ac_symbols:                             0
% 55.64/7.49  
% 55.64/7.49  ------ Propositional Solver
% 55.64/7.49  
% 55.64/7.49  prop_solver_calls:                      73
% 55.64/7.49  prop_fast_solver_calls:                 8974
% 55.64/7.49  smt_solver_calls:                       0
% 55.64/7.49  smt_fast_solver_calls:                  0
% 55.64/7.49  prop_num_of_clauses:                    72236
% 55.64/7.49  prop_preprocess_simplified:             144242
% 55.64/7.49  prop_fo_subsumed:                       2719
% 55.64/7.49  prop_solver_time:                       0.
% 55.64/7.49  smt_solver_time:                        0.
% 55.64/7.49  smt_fast_solver_time:                   0.
% 55.64/7.49  prop_fast_solver_time:                  0.
% 55.64/7.49  prop_unsat_core_time:                   0.014
% 55.64/7.49  
% 55.64/7.49  ------ QBF
% 55.64/7.49  
% 55.64/7.49  qbf_q_res:                              0
% 55.64/7.49  qbf_num_tautologies:                    0
% 55.64/7.49  qbf_prep_cycles:                        0
% 55.64/7.49  
% 55.64/7.49  ------ BMC1
% 55.64/7.49  
% 55.64/7.49  bmc1_current_bound:                     -1
% 55.64/7.49  bmc1_last_solved_bound:                 -1
% 55.64/7.49  bmc1_unsat_core_size:                   -1
% 55.64/7.49  bmc1_unsat_core_parents_size:           -1
% 55.64/7.49  bmc1_merge_next_fun:                    0
% 55.64/7.49  bmc1_unsat_core_clauses_time:           0.
% 55.64/7.49  
% 55.64/7.49  ------ Instantiation
% 55.64/7.49  
% 55.64/7.49  inst_num_of_clauses:                    14109
% 55.64/7.49  inst_num_in_passive:                    6487
% 55.64/7.49  inst_num_in_active:                     7626
% 55.64/7.49  inst_num_in_unprocessed:                2822
% 55.64/7.49  inst_num_of_loops:                      8119
% 55.64/7.49  inst_num_of_learning_restarts:          1
% 55.64/7.49  inst_num_moves_active_passive:          491
% 55.64/7.49  inst_lit_activity:                      0
% 55.64/7.49  inst_lit_activity_moves:                6
% 55.64/7.49  inst_num_tautologies:                   0
% 55.64/7.49  inst_num_prop_implied:                  0
% 55.64/7.49  inst_num_existing_simplified:           0
% 55.64/7.49  inst_num_eq_res_simplified:             0
% 55.64/7.49  inst_num_child_elim:                    0
% 55.64/7.49  inst_num_of_dismatching_blockings:      13274
% 55.64/7.49  inst_num_of_non_proper_insts:           18745
% 55.64/7.49  inst_num_of_duplicates:                 0
% 55.64/7.49  inst_inst_num_from_inst_to_res:         0
% 55.64/7.49  inst_dismatching_checking_time:         0.
% 55.64/7.49  
% 55.64/7.49  ------ Resolution
% 55.64/7.49  
% 55.64/7.49  res_num_of_clauses:                     64
% 55.64/7.49  res_num_in_passive:                     64
% 55.64/7.49  res_num_in_active:                      0
% 55.64/7.49  res_num_of_loops:                       226
% 55.64/7.49  res_forward_subset_subsumed:            1041
% 55.64/7.49  res_backward_subset_subsumed:           2
% 55.64/7.49  res_forward_subsumed:                   0
% 55.64/7.49  res_backward_subsumed:                  0
% 55.64/7.49  res_forward_subsumption_resolution:     4
% 55.64/7.49  res_backward_subsumption_resolution:    0
% 55.64/7.49  res_clause_to_clause_subsumption:       27355
% 55.64/7.49  res_orphan_elimination:                 0
% 55.64/7.49  res_tautology_del:                      638
% 55.64/7.49  res_num_eq_res_simplified:              0
% 55.64/7.49  res_num_sel_changes:                    0
% 55.64/7.49  res_moves_from_active_to_pass:          0
% 55.64/7.49  
% 55.64/7.49  ------ Superposition
% 55.64/7.49  
% 55.64/7.49  sup_time_total:                         0.
% 55.64/7.49  sup_time_generating:                    0.
% 55.64/7.49  sup_time_sim_full:                      0.
% 55.64/7.49  sup_time_sim_immed:                     0.
% 55.64/7.49  
% 55.64/7.49  sup_num_of_clauses:                     9667
% 55.64/7.49  sup_num_in_active:                      1519
% 55.64/7.49  sup_num_in_passive:                     8148
% 55.64/7.49  sup_num_of_loops:                       1622
% 55.64/7.49  sup_fw_superposition:                   3139
% 55.64/7.49  sup_bw_superposition:                   7813
% 55.64/7.49  sup_immediate_simplified:               6182
% 55.64/7.49  sup_given_eliminated:                   0
% 55.64/7.49  comparisons_done:                       0
% 55.64/7.49  comparisons_avoided:                    1
% 55.64/7.49  
% 55.64/7.49  ------ Simplifications
% 55.64/7.49  
% 55.64/7.49  
% 55.64/7.49  sim_fw_subset_subsumed:                 157
% 55.64/7.49  sim_bw_subset_subsumed:                 429
% 55.64/7.49  sim_fw_subsumed:                        49
% 55.64/7.49  sim_bw_subsumed:                        7
% 55.64/7.49  sim_fw_subsumption_res:                 0
% 55.64/7.49  sim_bw_subsumption_res:                 0
% 55.64/7.49  sim_tautology_del:                      0
% 55.64/7.49  sim_eq_tautology_del:                   192
% 55.64/7.49  sim_eq_res_simp:                        5
% 55.64/7.49  sim_fw_demodulated:                     907
% 55.64/7.49  sim_bw_demodulated:                     71
% 55.64/7.49  sim_light_normalised:                   5269
% 55.64/7.49  sim_joinable_taut:                      0
% 55.64/7.49  sim_joinable_simp:                      0
% 55.64/7.49  sim_ac_normalised:                      0
% 55.64/7.49  sim_smt_subsumption:                    0
% 55.64/7.49  
%------------------------------------------------------------------------------
