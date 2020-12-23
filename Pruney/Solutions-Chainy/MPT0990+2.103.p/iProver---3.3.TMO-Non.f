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
% DateTime   : Thu Dec  3 12:03:18 EST 2020

% Result     : Timeout 59.45s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :  259 (2284 expanded)
%              Number of clauses        :  151 ( 698 expanded)
%              Number of leaves         :   27 ( 568 expanded)
%              Depth                    :   25
%              Number of atoms          : 1017 (18757 expanded)
%              Number of equality atoms :  480 (6873 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f32,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f32])).

fof(f133,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f38,conjecture,(
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

fof(f39,negated_conjecture,(
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
    inference(negated_conjecture,[],[f38])).

fof(f78,plain,(
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
    inference(ennf_transformation,[],[f39])).

fof(f79,plain,(
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
    inference(flattening,[],[f78])).

fof(f87,plain,(
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

fof(f86,plain,
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

fof(f88,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f79,f87,f86])).

fof(f146,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f88])).

fof(f149,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f88])).

fof(f33,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f71,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f70])).

fof(f134,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f147,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f88])).

fof(f144,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f88])).

fof(f151,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f88])).

fof(f31,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f69,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f68])).

fof(f132,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f29,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f65,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f64])).

fof(f84,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f65])).

fof(f127,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f27,axiom,(
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

fof(f61,plain,(
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
    inference(ennf_transformation,[],[f27])).

fof(f62,plain,(
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
    inference(flattening,[],[f61])).

fof(f124,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f34,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f135,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f34])).

fof(f168,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f124,f135])).

fof(f11,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f103,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f82,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f97,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f99,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f98,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f66])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f67])).

fof(f129,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f35,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
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
    inference(ennf_transformation,[],[f35])).

fof(f73,plain,(
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
    inference(flattening,[],[f72])).

fof(f137,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_funct_2(X3,X0)
      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f28,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f145,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f88])).

fof(f148,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f88])).

fof(f26,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
          & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] :
      ( ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f60,plain,(
    ! [X0] :
      ( ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f59])).

fof(f122,plain,(
    ! [X0] :
      ( k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f150,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f88])).

fof(f37,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
            & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f77,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f76])).

fof(f143,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f152,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f88])).

fof(f154,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f88])).

fof(f18,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f111,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f162,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f111,f135])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f100,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f80,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f80])).

fof(f92,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f23,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f118,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f166,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f118,f135])).

fof(f36,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( ( k2_relset_1(X0,X1,X3) = X1
              & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) )
           => ( ( v2_funct_1(X4)
                & v2_funct_1(X3) )
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( v2_funct_1(X4)
            & v2_funct_1(X3) )
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | k2_relset_1(X0,X1,X3) != X1
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f75,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( v2_funct_1(X4)
            & v2_funct_1(X3) )
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | k2_relset_1(X0,X1,X3) != X1
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f74])).

fof(f140,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v2_funct_1(X4)
      | k1_xboole_0 = X2
      | k2_relset_1(X0,X1,X3) != X1
      | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f153,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f88])).

fof(f90,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f81])).

fof(f170,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f90])).

fof(f24,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0))
           => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f55])).

fof(f119,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
      | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f25,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f58,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f57])).

fof(f120,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f142,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f22,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f54,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f53])).

fof(f116,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f104,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f155,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_40,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f133])).

cnf(c_2708,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_59,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f146])).

cnf(c_2694,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_59])).

cnf(c_56,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f149])).

cnf(c_2697,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_56])).

cnf(c_41,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f134])).

cnf(c_2707,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_10546,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2697,c_2707])).

cnf(c_58,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f147])).

cnf(c_65,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_58])).

cnf(c_10630,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10546,c_65])).

cnf(c_10631,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_10630])).

cnf(c_10640,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2694,c_10631])).

cnf(c_61,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f144])).

cnf(c_62,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_61])).

cnf(c_10660,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10640,c_62])).

cnf(c_54,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f151])).

cnf(c_2698,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_54])).

cnf(c_10662,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_10660,c_2698])).

cnf(c_38,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f132])).

cnf(c_2710,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_10664,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_10660,c_2710])).

cnf(c_64,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_59])).

cnf(c_67,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_56])).

cnf(c_12078,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10664,c_62,c_64,c_65,c_67])).

cnf(c_35,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f127])).

cnf(c_2711,plain,
    ( X0 = X1
    | r2_relset_1(X2,X3,X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_12088,plain,
    ( k5_relat_1(sK2,sK3) = X0
    | r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_12078,c_2711])).

cnf(c_18076,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_10662,c_12088])).

cnf(c_18081,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(superposition,[status(thm)],[c_2708,c_18076])).

cnf(c_31,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
    | k2_funct_1(X0) = X1
    | k2_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f168])).

cnf(c_2713,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k2_relat_1(X0) != k1_relat_1(X1)
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_18183,plain,
    ( k2_funct_1(sK3) = sK2
    | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_18081,c_2713])).

cnf(c_10,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_2731,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_2733,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4956,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2697,c_2733])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_4,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_435,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_4])).

cnf(c_436,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_435])).

cnf(c_538,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_436])).

cnf(c_2691,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_538])).

cnf(c_11277,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4956,c_2691])).

cnf(c_11309,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2731,c_11277])).

cnf(c_37,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f129])).

cnf(c_42,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v1_funct_2(X2,X0,X1)
    | v2_funct_2(X3,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f137])).

cnf(c_783,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v5_relat_1(X4,X5)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X4)
    | X3 != X4
    | X0 != X5
    | k2_relat_1(X4) = X5 ),
    inference(resolution_lifted,[status(thm)],[c_37,c_42])).

cnf(c_784,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v5_relat_1(X3,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X3)
    | k2_relat_1(X3) = X0 ),
    inference(unflattening,[status(thm)],[c_783])).

cnf(c_32,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_808,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X3)
    | k2_relat_1(X3) = X0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_784,c_32])).

cnf(c_2689,plain,
    ( k2_relat_1(X0) = X1
    | r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X0),k6_partfun1(X1)) != iProver_top
    | v1_funct_2(X3,X1,X2) != iProver_top
    | v1_funct_2(X0,X2,X1) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_808])).

cnf(c_3655,plain,
    ( k2_relat_1(sK3) = sK0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2698,c_2689])).

cnf(c_60,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f145])).

cnf(c_63,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_60])).

cnf(c_57,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f148])).

cnf(c_66,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_57])).

cnf(c_3658,plain,
    ( k2_relat_1(sK3) = sK0
    | v1_relat_1(sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3655,c_62,c_63,c_64,c_65,c_66,c_67])).

cnf(c_11573,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(superposition,[status(thm)],[c_11309,c_3658])).

cnf(c_4957,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2694,c_2733])).

cnf(c_11278,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4957,c_2691])).

cnf(c_11336,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2731,c_11278])).

cnf(c_2692,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_61])).

cnf(c_30,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_2714,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_6968,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1(sK2),sK2)) = k2_relat_1(sK2)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2692,c_2714])).

cnf(c_55,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f150])).

cnf(c_48,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f143])).

cnf(c_2701,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_6067,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_55,c_2701])).

cnf(c_53,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f152])).

cnf(c_51,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f154])).

cnf(c_2816,plain,
    ( ~ v1_funct_2(X0,X1,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,sK1,X0) != sK1
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_48])).

cnf(c_2967,plain,
    ( ~ v1_funct_2(sK2,X0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(X0,sK1,sK2) != sK1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_2816])).

cnf(c_3089,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(sK0,sK1,sK2) != sK1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_2967])).

cnf(c_6550,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6067,c_61,c_60,c_59,c_55,c_53,c_51,c_3089])).

cnf(c_6969,plain,
    ( k1_relat_1(k6_partfun1(sK1)) = k2_relat_1(sK2)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6968,c_6550])).

cnf(c_19,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f162])).

cnf(c_6970,plain,
    ( k2_relat_1(sK2) = sK1
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6969,c_19])).

cnf(c_69,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_53])).

cnf(c_7039,plain,
    ( k2_relat_1(sK2) = sK1
    | v1_relat_1(sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6970,c_69])).

cnf(c_11610,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(superposition,[status(thm)],[c_11336,c_7039])).

cnf(c_18188,plain,
    ( k2_funct_1(sK3) = sK2
    | k6_partfun1(sK0) != k6_partfun1(sK0)
    | k1_relat_1(sK3) != sK1
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_18183,c_11573,c_11610])).

cnf(c_18189,plain,
    ( k2_funct_1(sK3) = sK2
    | k1_relat_1(sK3) != sK1
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_18188])).

cnf(c_33,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_8,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_723,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_33,c_8])).

cnf(c_2690,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_723])).

cnf(c_3785,plain,
    ( r1_tarski(k1_relat_1(sK3),sK1) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2697,c_2690])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2736,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_6323,plain,
    ( k1_relat_1(sK3) = sK1
    | r1_tarski(sK1,k1_relat_1(sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3785,c_2736])).

cnf(c_24,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f166])).

cnf(c_10783,plain,
    ( v2_funct_1(k6_partfun1(sK0)) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_10784,plain,
    ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10783])).

cnf(c_45,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v2_funct_1(X0)
    | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
    | k2_relset_1(X4,X1,X3) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f140])).

cnf(c_2704,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k1_xboole_0 = X3
    | v1_funct_2(X4,X1,X3) != iProver_top
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X4) = iProver_top
    | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_8325,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_55,c_2704])).

cnf(c_8904,plain,
    ( v1_funct_1(X1) != iProver_top
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | k1_xboole_0 = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8325,c_62,c_63,c_64])).

cnf(c_8905,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_8904])).

cnf(c_10668,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_10660,c_8905])).

cnf(c_52,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f153])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f170])).

cnf(c_197,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_201,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1633,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2860,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1633])).

cnf(c_2861,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2860])).

cnf(c_10897,plain,
    ( v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10668,c_65,c_66,c_67,c_52,c_197,c_201,c_2861])).

cnf(c_18171,plain,
    ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_18081,c_10897])).

cnf(c_26,plain,
    ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k5_relat_1(X0,X1)) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_2718,plain,
    ( k1_relat_1(k5_relat_1(X0,X1)) != k1_relat_1(X0)
    | r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_18184,plain,
    ( k1_relat_1(k6_partfun1(sK0)) != k1_relat_1(sK2)
    | r1_tarski(k2_relat_1(sK2),k1_relat_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_18081,c_2718])).

cnf(c_28,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_2716,plain,
    ( k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_7642,plain,
    ( k1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) = k1_relat_1(sK2)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2692,c_2716])).

cnf(c_49,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f142])).

cnf(c_2700,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_4358,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_55,c_2700])).

cnf(c_2817,plain,
    ( ~ v1_funct_2(X0,X1,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,sK1,X0) != sK1
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_49])).

cnf(c_2999,plain,
    ( ~ v1_funct_2(sK2,X0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(X0,sK1,sK2) != sK1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_2817])).

cnf(c_3112,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(sK0,sK1,sK2) != sK1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_2999])).

cnf(c_4522,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4358,c_61,c_60,c_59,c_55,c_53,c_51,c_3112])).

cnf(c_7643,plain,
    ( k1_relat_1(k6_partfun1(sK0)) = k1_relat_1(sK2)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7642,c_4522])).

cnf(c_7644,plain,
    ( k1_relat_1(sK2) = sK0
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7643,c_19])).

cnf(c_8051,plain,
    ( k1_relat_1(sK2) = sK0
    | v1_relat_1(sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7644,c_69])).

cnf(c_11609,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(superposition,[status(thm)],[c_11336,c_8051])).

cnf(c_18185,plain,
    ( k1_relat_1(k6_partfun1(sK0)) != sK0
    | r1_tarski(sK1,k1_relat_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_18184,c_11609,c_11610])).

cnf(c_18186,plain,
    ( sK0 != sK0
    | r1_tarski(sK1,k1_relat_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_18185,c_19])).

cnf(c_18187,plain,
    ( r1_tarski(sK1,k1_relat_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_18186])).

cnf(c_176458,plain,
    ( k2_funct_1(sK3) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_18189,c_62,c_65,c_6323,c_10784,c_11309,c_11336,c_18171,c_18187])).

cnf(c_18931,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_18171,c_10784])).

cnf(c_2695,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_58])).

cnf(c_23,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_2721,plain,
    ( k2_funct_1(X0) = k4_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_6847,plain,
    ( k2_funct_1(sK3) = k4_relat_1(sK3)
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2695,c_2721])).

cnf(c_18939,plain,
    ( k2_funct_1(sK3) = k4_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_18931,c_6847])).

cnf(c_18944,plain,
    ( k2_funct_1(sK3) = k4_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18939,c_6847,c_10784,c_11309,c_18171])).

cnf(c_176460,plain,
    ( k4_relat_1(sK3) = sK2 ),
    inference(demodulation,[status(thm)],[c_176458,c_18944])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k4_relat_1(k4_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_2730,plain,
    ( k4_relat_1(k4_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_11571,plain,
    ( k4_relat_1(k4_relat_1(sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_11309,c_2730])).

cnf(c_177188,plain,
    ( k4_relat_1(sK2) = sK3 ),
    inference(demodulation,[status(thm)],[c_176460,c_11571])).

cnf(c_6848,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2692,c_2721])).

cnf(c_7006,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6848,c_69])).

cnf(c_11611,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_11336,c_7006])).

cnf(c_50,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f155])).

cnf(c_11674,plain,
    ( k4_relat_1(sK2) != sK3 ),
    inference(demodulation,[status(thm)],[c_11611,c_50])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_177188,c_11674])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:53:38 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 59.45/8.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 59.45/8.00  
% 59.45/8.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 59.45/8.00  
% 59.45/8.00  ------  iProver source info
% 59.45/8.00  
% 59.45/8.00  git: date: 2020-06-30 10:37:57 +0100
% 59.45/8.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 59.45/8.00  git: non_committed_changes: false
% 59.45/8.00  git: last_make_outside_of_git: false
% 59.45/8.00  
% 59.45/8.00  ------ 
% 59.45/8.00  
% 59.45/8.00  ------ Input Options
% 59.45/8.00  
% 59.45/8.00  --out_options                           all
% 59.45/8.00  --tptp_safe_out                         true
% 59.45/8.00  --problem_path                          ""
% 59.45/8.00  --include_path                          ""
% 59.45/8.00  --clausifier                            res/vclausify_rel
% 59.45/8.00  --clausifier_options                    ""
% 59.45/8.00  --stdin                                 false
% 59.45/8.00  --stats_out                             all
% 59.45/8.00  
% 59.45/8.00  ------ General Options
% 59.45/8.00  
% 59.45/8.00  --fof                                   false
% 59.45/8.00  --time_out_real                         305.
% 59.45/8.00  --time_out_virtual                      -1.
% 59.45/8.00  --symbol_type_check                     false
% 59.45/8.00  --clausify_out                          false
% 59.45/8.00  --sig_cnt_out                           false
% 59.45/8.00  --trig_cnt_out                          false
% 59.45/8.00  --trig_cnt_out_tolerance                1.
% 59.45/8.00  --trig_cnt_out_sk_spl                   false
% 59.45/8.00  --abstr_cl_out                          false
% 59.45/8.00  
% 59.45/8.00  ------ Global Options
% 59.45/8.00  
% 59.45/8.00  --schedule                              default
% 59.45/8.00  --add_important_lit                     false
% 59.45/8.00  --prop_solver_per_cl                    1000
% 59.45/8.00  --min_unsat_core                        false
% 59.45/8.00  --soft_assumptions                      false
% 59.45/8.00  --soft_lemma_size                       3
% 59.45/8.00  --prop_impl_unit_size                   0
% 59.45/8.00  --prop_impl_unit                        []
% 59.45/8.00  --share_sel_clauses                     true
% 59.45/8.00  --reset_solvers                         false
% 59.45/8.00  --bc_imp_inh                            [conj_cone]
% 59.45/8.00  --conj_cone_tolerance                   3.
% 59.45/8.00  --extra_neg_conj                        none
% 59.45/8.00  --large_theory_mode                     true
% 59.45/8.00  --prolific_symb_bound                   200
% 59.45/8.00  --lt_threshold                          2000
% 59.45/8.00  --clause_weak_htbl                      true
% 59.45/8.00  --gc_record_bc_elim                     false
% 59.45/8.00  
% 59.45/8.00  ------ Preprocessing Options
% 59.45/8.00  
% 59.45/8.00  --preprocessing_flag                    true
% 59.45/8.00  --time_out_prep_mult                    0.1
% 59.45/8.00  --splitting_mode                        input
% 59.45/8.00  --splitting_grd                         true
% 59.45/8.00  --splitting_cvd                         false
% 59.45/8.00  --splitting_cvd_svl                     false
% 59.45/8.00  --splitting_nvd                         32
% 59.45/8.00  --sub_typing                            true
% 59.45/8.00  --prep_gs_sim                           true
% 59.45/8.00  --prep_unflatten                        true
% 59.45/8.00  --prep_res_sim                          true
% 59.45/8.00  --prep_upred                            true
% 59.45/8.00  --prep_sem_filter                       exhaustive
% 59.45/8.00  --prep_sem_filter_out                   false
% 59.45/8.00  --pred_elim                             true
% 59.45/8.00  --res_sim_input                         true
% 59.45/8.00  --eq_ax_congr_red                       true
% 59.45/8.00  --pure_diseq_elim                       true
% 59.45/8.00  --brand_transform                       false
% 59.45/8.00  --non_eq_to_eq                          false
% 59.45/8.00  --prep_def_merge                        true
% 59.45/8.00  --prep_def_merge_prop_impl              false
% 59.45/8.00  --prep_def_merge_mbd                    true
% 59.45/8.00  --prep_def_merge_tr_red                 false
% 59.45/8.00  --prep_def_merge_tr_cl                  false
% 59.45/8.00  --smt_preprocessing                     true
% 59.45/8.00  --smt_ac_axioms                         fast
% 59.45/8.00  --preprocessed_out                      false
% 59.45/8.00  --preprocessed_stats                    false
% 59.45/8.00  
% 59.45/8.00  ------ Abstraction refinement Options
% 59.45/8.00  
% 59.45/8.00  --abstr_ref                             []
% 59.45/8.00  --abstr_ref_prep                        false
% 59.45/8.00  --abstr_ref_until_sat                   false
% 59.45/8.00  --abstr_ref_sig_restrict                funpre
% 59.45/8.00  --abstr_ref_af_restrict_to_split_sk     false
% 59.45/8.00  --abstr_ref_under                       []
% 59.45/8.00  
% 59.45/8.00  ------ SAT Options
% 59.45/8.00  
% 59.45/8.00  --sat_mode                              false
% 59.45/8.00  --sat_fm_restart_options                ""
% 59.45/8.00  --sat_gr_def                            false
% 59.45/8.00  --sat_epr_types                         true
% 59.45/8.00  --sat_non_cyclic_types                  false
% 59.45/8.00  --sat_finite_models                     false
% 59.45/8.00  --sat_fm_lemmas                         false
% 59.45/8.00  --sat_fm_prep                           false
% 59.45/8.00  --sat_fm_uc_incr                        true
% 59.45/8.00  --sat_out_model                         small
% 59.45/8.00  --sat_out_clauses                       false
% 59.45/8.00  
% 59.45/8.00  ------ QBF Options
% 59.45/8.00  
% 59.45/8.00  --qbf_mode                              false
% 59.45/8.00  --qbf_elim_univ                         false
% 59.45/8.00  --qbf_dom_inst                          none
% 59.45/8.00  --qbf_dom_pre_inst                      false
% 59.45/8.00  --qbf_sk_in                             false
% 59.45/8.00  --qbf_pred_elim                         true
% 59.45/8.00  --qbf_split                             512
% 59.45/8.00  
% 59.45/8.00  ------ BMC1 Options
% 59.45/8.00  
% 59.45/8.00  --bmc1_incremental                      false
% 59.45/8.00  --bmc1_axioms                           reachable_all
% 59.45/8.00  --bmc1_min_bound                        0
% 59.45/8.00  --bmc1_max_bound                        -1
% 59.45/8.00  --bmc1_max_bound_default                -1
% 59.45/8.00  --bmc1_symbol_reachability              true
% 59.45/8.00  --bmc1_property_lemmas                  false
% 59.45/8.00  --bmc1_k_induction                      false
% 59.45/8.00  --bmc1_non_equiv_states                 false
% 59.45/8.00  --bmc1_deadlock                         false
% 59.45/8.00  --bmc1_ucm                              false
% 59.45/8.00  --bmc1_add_unsat_core                   none
% 59.45/8.00  --bmc1_unsat_core_children              false
% 59.45/8.00  --bmc1_unsat_core_extrapolate_axioms    false
% 59.45/8.00  --bmc1_out_stat                         full
% 59.45/8.00  --bmc1_ground_init                      false
% 59.45/8.00  --bmc1_pre_inst_next_state              false
% 59.45/8.00  --bmc1_pre_inst_state                   false
% 59.45/8.00  --bmc1_pre_inst_reach_state             false
% 59.45/8.00  --bmc1_out_unsat_core                   false
% 59.45/8.00  --bmc1_aig_witness_out                  false
% 59.45/8.00  --bmc1_verbose                          false
% 59.45/8.00  --bmc1_dump_clauses_tptp                false
% 59.45/8.00  --bmc1_dump_unsat_core_tptp             false
% 59.45/8.00  --bmc1_dump_file                        -
% 59.45/8.00  --bmc1_ucm_expand_uc_limit              128
% 59.45/8.00  --bmc1_ucm_n_expand_iterations          6
% 59.45/8.00  --bmc1_ucm_extend_mode                  1
% 59.45/8.00  --bmc1_ucm_init_mode                    2
% 59.45/8.00  --bmc1_ucm_cone_mode                    none
% 59.45/8.00  --bmc1_ucm_reduced_relation_type        0
% 59.45/8.00  --bmc1_ucm_relax_model                  4
% 59.45/8.00  --bmc1_ucm_full_tr_after_sat            true
% 59.45/8.00  --bmc1_ucm_expand_neg_assumptions       false
% 59.45/8.00  --bmc1_ucm_layered_model                none
% 59.45/8.00  --bmc1_ucm_max_lemma_size               10
% 59.45/8.00  
% 59.45/8.00  ------ AIG Options
% 59.45/8.00  
% 59.45/8.00  --aig_mode                              false
% 59.45/8.00  
% 59.45/8.00  ------ Instantiation Options
% 59.45/8.00  
% 59.45/8.00  --instantiation_flag                    true
% 59.45/8.00  --inst_sos_flag                         true
% 59.45/8.00  --inst_sos_phase                        true
% 59.45/8.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 59.45/8.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 59.45/8.00  --inst_lit_sel_side                     num_symb
% 59.45/8.00  --inst_solver_per_active                1400
% 59.45/8.00  --inst_solver_calls_frac                1.
% 59.45/8.00  --inst_passive_queue_type               priority_queues
% 59.45/8.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 59.45/8.00  --inst_passive_queues_freq              [25;2]
% 59.45/8.00  --inst_dismatching                      true
% 59.45/8.00  --inst_eager_unprocessed_to_passive     true
% 59.45/8.00  --inst_prop_sim_given                   true
% 59.45/8.00  --inst_prop_sim_new                     false
% 59.45/8.00  --inst_subs_new                         false
% 59.45/8.00  --inst_eq_res_simp                      false
% 59.45/8.00  --inst_subs_given                       false
% 59.45/8.00  --inst_orphan_elimination               true
% 59.45/8.00  --inst_learning_loop_flag               true
% 59.45/8.00  --inst_learning_start                   3000
% 59.45/8.00  --inst_learning_factor                  2
% 59.45/8.00  --inst_start_prop_sim_after_learn       3
% 59.45/8.00  --inst_sel_renew                        solver
% 59.45/8.00  --inst_lit_activity_flag                true
% 59.45/8.00  --inst_restr_to_given                   false
% 59.45/8.00  --inst_activity_threshold               500
% 59.45/8.00  --inst_out_proof                        true
% 59.45/8.00  
% 59.45/8.00  ------ Resolution Options
% 59.45/8.00  
% 59.45/8.00  --resolution_flag                       true
% 59.45/8.00  --res_lit_sel                           adaptive
% 59.45/8.00  --res_lit_sel_side                      none
% 59.45/8.00  --res_ordering                          kbo
% 59.45/8.00  --res_to_prop_solver                    active
% 59.45/8.00  --res_prop_simpl_new                    false
% 59.45/8.00  --res_prop_simpl_given                  true
% 59.45/8.00  --res_passive_queue_type                priority_queues
% 59.45/8.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 59.45/8.00  --res_passive_queues_freq               [15;5]
% 59.45/8.00  --res_forward_subs                      full
% 59.45/8.00  --res_backward_subs                     full
% 59.45/8.00  --res_forward_subs_resolution           true
% 59.45/8.00  --res_backward_subs_resolution          true
% 59.45/8.00  --res_orphan_elimination                true
% 59.45/8.00  --res_time_limit                        2.
% 59.45/8.00  --res_out_proof                         true
% 59.45/8.00  
% 59.45/8.00  ------ Superposition Options
% 59.45/8.00  
% 59.45/8.00  --superposition_flag                    true
% 59.45/8.00  --sup_passive_queue_type                priority_queues
% 59.45/8.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 59.45/8.00  --sup_passive_queues_freq               [8;1;4]
% 59.45/8.00  --demod_completeness_check              fast
% 59.45/8.00  --demod_use_ground                      true
% 59.45/8.00  --sup_to_prop_solver                    passive
% 59.45/8.00  --sup_prop_simpl_new                    true
% 59.45/8.00  --sup_prop_simpl_given                  true
% 59.45/8.00  --sup_fun_splitting                     true
% 59.45/8.00  --sup_smt_interval                      50000
% 59.45/8.00  
% 59.45/8.00  ------ Superposition Simplification Setup
% 59.45/8.00  
% 59.45/8.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 59.45/8.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 59.45/8.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 59.45/8.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 59.45/8.00  --sup_full_triv                         [TrivRules;PropSubs]
% 59.45/8.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 59.45/8.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 59.45/8.00  --sup_immed_triv                        [TrivRules]
% 59.45/8.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 59.45/8.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 59.45/8.00  --sup_immed_bw_main                     []
% 59.45/8.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 59.45/8.00  --sup_input_triv                        [Unflattening;TrivRules]
% 59.45/8.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 59.45/8.00  --sup_input_bw                          []
% 59.45/8.00  
% 59.45/8.00  ------ Combination Options
% 59.45/8.00  
% 59.45/8.00  --comb_res_mult                         3
% 59.45/8.00  --comb_sup_mult                         2
% 59.45/8.00  --comb_inst_mult                        10
% 59.45/8.00  
% 59.45/8.00  ------ Debug Options
% 59.45/8.00  
% 59.45/8.00  --dbg_backtrace                         false
% 59.45/8.00  --dbg_dump_prop_clauses                 false
% 59.45/8.00  --dbg_dump_prop_clauses_file            -
% 59.45/8.00  --dbg_out_stat                          false
% 59.45/8.00  ------ Parsing...
% 59.45/8.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 59.45/8.00  
% 59.45/8.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 59.45/8.00  
% 59.45/8.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 59.45/8.00  
% 59.45/8.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 59.45/8.00  ------ Proving...
% 59.45/8.00  ------ Problem Properties 
% 59.45/8.00  
% 59.45/8.00  
% 59.45/8.00  clauses                                 56
% 59.45/8.00  conjectures                             12
% 59.45/8.00  EPR                                     10
% 59.45/8.00  Horn                                    52
% 59.45/8.00  unary                                   21
% 59.45/8.00  binary                                  12
% 59.45/8.00  lits                                    179
% 59.45/8.00  lits eq                                 40
% 59.45/8.00  fd_pure                                 0
% 59.45/8.00  fd_pseudo                               0
% 59.45/8.00  fd_cond                                 4
% 59.45/8.00  fd_pseudo_cond                          4
% 59.45/8.00  AC symbols                              0
% 59.45/8.00  
% 59.45/8.00  ------ Schedule dynamic 5 is on 
% 59.45/8.00  
% 59.45/8.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 59.45/8.00  
% 59.45/8.00  
% 59.45/8.00  ------ 
% 59.45/8.00  Current options:
% 59.45/8.00  ------ 
% 59.45/8.00  
% 59.45/8.00  ------ Input Options
% 59.45/8.00  
% 59.45/8.00  --out_options                           all
% 59.45/8.00  --tptp_safe_out                         true
% 59.45/8.00  --problem_path                          ""
% 59.45/8.00  --include_path                          ""
% 59.45/8.00  --clausifier                            res/vclausify_rel
% 59.45/8.00  --clausifier_options                    ""
% 59.45/8.00  --stdin                                 false
% 59.45/8.00  --stats_out                             all
% 59.45/8.00  
% 59.45/8.00  ------ General Options
% 59.45/8.00  
% 59.45/8.00  --fof                                   false
% 59.45/8.00  --time_out_real                         305.
% 59.45/8.00  --time_out_virtual                      -1.
% 59.45/8.00  --symbol_type_check                     false
% 59.45/8.00  --clausify_out                          false
% 59.45/8.00  --sig_cnt_out                           false
% 59.45/8.00  --trig_cnt_out                          false
% 59.45/8.00  --trig_cnt_out_tolerance                1.
% 59.45/8.00  --trig_cnt_out_sk_spl                   false
% 59.45/8.00  --abstr_cl_out                          false
% 59.45/8.00  
% 59.45/8.00  ------ Global Options
% 59.45/8.00  
% 59.45/8.00  --schedule                              default
% 59.45/8.00  --add_important_lit                     false
% 59.45/8.00  --prop_solver_per_cl                    1000
% 59.45/8.00  --min_unsat_core                        false
% 59.45/8.00  --soft_assumptions                      false
% 59.45/8.00  --soft_lemma_size                       3
% 59.45/8.00  --prop_impl_unit_size                   0
% 59.45/8.00  --prop_impl_unit                        []
% 59.45/8.00  --share_sel_clauses                     true
% 59.45/8.00  --reset_solvers                         false
% 59.45/8.00  --bc_imp_inh                            [conj_cone]
% 59.45/8.00  --conj_cone_tolerance                   3.
% 59.45/8.00  --extra_neg_conj                        none
% 59.45/8.00  --large_theory_mode                     true
% 59.45/8.00  --prolific_symb_bound                   200
% 59.45/8.00  --lt_threshold                          2000
% 59.45/8.00  --clause_weak_htbl                      true
% 59.45/8.00  --gc_record_bc_elim                     false
% 59.45/8.00  
% 59.45/8.00  ------ Preprocessing Options
% 59.45/8.00  
% 59.45/8.00  --preprocessing_flag                    true
% 59.45/8.00  --time_out_prep_mult                    0.1
% 59.45/8.00  --splitting_mode                        input
% 59.45/8.00  --splitting_grd                         true
% 59.45/8.00  --splitting_cvd                         false
% 59.45/8.00  --splitting_cvd_svl                     false
% 59.45/8.00  --splitting_nvd                         32
% 59.45/8.00  --sub_typing                            true
% 59.45/8.00  --prep_gs_sim                           true
% 59.45/8.00  --prep_unflatten                        true
% 59.45/8.00  --prep_res_sim                          true
% 59.45/8.00  --prep_upred                            true
% 59.45/8.00  --prep_sem_filter                       exhaustive
% 59.45/8.00  --prep_sem_filter_out                   false
% 59.45/8.00  --pred_elim                             true
% 59.45/8.00  --res_sim_input                         true
% 59.45/8.00  --eq_ax_congr_red                       true
% 59.45/8.00  --pure_diseq_elim                       true
% 59.45/8.00  --brand_transform                       false
% 59.45/8.01  --non_eq_to_eq                          false
% 59.45/8.01  --prep_def_merge                        true
% 59.45/8.01  --prep_def_merge_prop_impl              false
% 59.45/8.01  --prep_def_merge_mbd                    true
% 59.45/8.01  --prep_def_merge_tr_red                 false
% 59.45/8.01  --prep_def_merge_tr_cl                  false
% 59.45/8.01  --smt_preprocessing                     true
% 59.45/8.01  --smt_ac_axioms                         fast
% 59.45/8.01  --preprocessed_out                      false
% 59.45/8.01  --preprocessed_stats                    false
% 59.45/8.01  
% 59.45/8.01  ------ Abstraction refinement Options
% 59.45/8.01  
% 59.45/8.01  --abstr_ref                             []
% 59.45/8.01  --abstr_ref_prep                        false
% 59.45/8.01  --abstr_ref_until_sat                   false
% 59.45/8.01  --abstr_ref_sig_restrict                funpre
% 59.45/8.01  --abstr_ref_af_restrict_to_split_sk     false
% 59.45/8.01  --abstr_ref_under                       []
% 59.45/8.01  
% 59.45/8.01  ------ SAT Options
% 59.45/8.01  
% 59.45/8.01  --sat_mode                              false
% 59.45/8.01  --sat_fm_restart_options                ""
% 59.45/8.01  --sat_gr_def                            false
% 59.45/8.01  --sat_epr_types                         true
% 59.45/8.01  --sat_non_cyclic_types                  false
% 59.45/8.01  --sat_finite_models                     false
% 59.45/8.01  --sat_fm_lemmas                         false
% 59.45/8.01  --sat_fm_prep                           false
% 59.45/8.01  --sat_fm_uc_incr                        true
% 59.45/8.01  --sat_out_model                         small
% 59.45/8.01  --sat_out_clauses                       false
% 59.45/8.01  
% 59.45/8.01  ------ QBF Options
% 59.45/8.01  
% 59.45/8.01  --qbf_mode                              false
% 59.45/8.01  --qbf_elim_univ                         false
% 59.45/8.01  --qbf_dom_inst                          none
% 59.45/8.01  --qbf_dom_pre_inst                      false
% 59.45/8.01  --qbf_sk_in                             false
% 59.45/8.01  --qbf_pred_elim                         true
% 59.45/8.01  --qbf_split                             512
% 59.45/8.01  
% 59.45/8.01  ------ BMC1 Options
% 59.45/8.01  
% 59.45/8.01  --bmc1_incremental                      false
% 59.45/8.01  --bmc1_axioms                           reachable_all
% 59.45/8.01  --bmc1_min_bound                        0
% 59.45/8.01  --bmc1_max_bound                        -1
% 59.45/8.01  --bmc1_max_bound_default                -1
% 59.45/8.01  --bmc1_symbol_reachability              true
% 59.45/8.01  --bmc1_property_lemmas                  false
% 59.45/8.01  --bmc1_k_induction                      false
% 59.45/8.01  --bmc1_non_equiv_states                 false
% 59.45/8.01  --bmc1_deadlock                         false
% 59.45/8.01  --bmc1_ucm                              false
% 59.45/8.01  --bmc1_add_unsat_core                   none
% 59.45/8.01  --bmc1_unsat_core_children              false
% 59.45/8.01  --bmc1_unsat_core_extrapolate_axioms    false
% 59.45/8.01  --bmc1_out_stat                         full
% 59.45/8.01  --bmc1_ground_init                      false
% 59.45/8.01  --bmc1_pre_inst_next_state              false
% 59.45/8.01  --bmc1_pre_inst_state                   false
% 59.45/8.01  --bmc1_pre_inst_reach_state             false
% 59.45/8.01  --bmc1_out_unsat_core                   false
% 59.45/8.01  --bmc1_aig_witness_out                  false
% 59.45/8.01  --bmc1_verbose                          false
% 59.45/8.01  --bmc1_dump_clauses_tptp                false
% 59.45/8.01  --bmc1_dump_unsat_core_tptp             false
% 59.45/8.01  --bmc1_dump_file                        -
% 59.45/8.01  --bmc1_ucm_expand_uc_limit              128
% 59.45/8.01  --bmc1_ucm_n_expand_iterations          6
% 59.45/8.01  --bmc1_ucm_extend_mode                  1
% 59.45/8.01  --bmc1_ucm_init_mode                    2
% 59.45/8.01  --bmc1_ucm_cone_mode                    none
% 59.45/8.01  --bmc1_ucm_reduced_relation_type        0
% 59.45/8.01  --bmc1_ucm_relax_model                  4
% 59.45/8.01  --bmc1_ucm_full_tr_after_sat            true
% 59.45/8.01  --bmc1_ucm_expand_neg_assumptions       false
% 59.45/8.01  --bmc1_ucm_layered_model                none
% 59.45/8.01  --bmc1_ucm_max_lemma_size               10
% 59.45/8.01  
% 59.45/8.01  ------ AIG Options
% 59.45/8.01  
% 59.45/8.01  --aig_mode                              false
% 59.45/8.01  
% 59.45/8.01  ------ Instantiation Options
% 59.45/8.01  
% 59.45/8.01  --instantiation_flag                    true
% 59.45/8.01  --inst_sos_flag                         true
% 59.45/8.01  --inst_sos_phase                        true
% 59.45/8.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 59.45/8.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 59.45/8.01  --inst_lit_sel_side                     none
% 59.45/8.01  --inst_solver_per_active                1400
% 59.45/8.01  --inst_solver_calls_frac                1.
% 59.45/8.01  --inst_passive_queue_type               priority_queues
% 59.45/8.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 59.45/8.01  --inst_passive_queues_freq              [25;2]
% 59.45/8.01  --inst_dismatching                      true
% 59.45/8.01  --inst_eager_unprocessed_to_passive     true
% 59.45/8.01  --inst_prop_sim_given                   true
% 59.45/8.01  --inst_prop_sim_new                     false
% 59.45/8.01  --inst_subs_new                         false
% 59.45/8.01  --inst_eq_res_simp                      false
% 59.45/8.01  --inst_subs_given                       false
% 59.45/8.01  --inst_orphan_elimination               true
% 59.45/8.01  --inst_learning_loop_flag               true
% 59.45/8.01  --inst_learning_start                   3000
% 59.45/8.01  --inst_learning_factor                  2
% 59.45/8.01  --inst_start_prop_sim_after_learn       3
% 59.45/8.01  --inst_sel_renew                        solver
% 59.45/8.01  --inst_lit_activity_flag                true
% 59.45/8.01  --inst_restr_to_given                   false
% 59.45/8.01  --inst_activity_threshold               500
% 59.45/8.01  --inst_out_proof                        true
% 59.45/8.01  
% 59.45/8.01  ------ Resolution Options
% 59.45/8.01  
% 59.45/8.01  --resolution_flag                       false
% 59.45/8.01  --res_lit_sel                           adaptive
% 59.45/8.01  --res_lit_sel_side                      none
% 59.45/8.01  --res_ordering                          kbo
% 59.45/8.01  --res_to_prop_solver                    active
% 59.45/8.01  --res_prop_simpl_new                    false
% 59.45/8.01  --res_prop_simpl_given                  true
% 59.45/8.01  --res_passive_queue_type                priority_queues
% 59.45/8.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 59.45/8.01  --res_passive_queues_freq               [15;5]
% 59.45/8.01  --res_forward_subs                      full
% 59.45/8.01  --res_backward_subs                     full
% 59.45/8.01  --res_forward_subs_resolution           true
% 59.45/8.01  --res_backward_subs_resolution          true
% 59.45/8.01  --res_orphan_elimination                true
% 59.45/8.01  --res_time_limit                        2.
% 59.45/8.01  --res_out_proof                         true
% 59.45/8.01  
% 59.45/8.01  ------ Superposition Options
% 59.45/8.01  
% 59.45/8.01  --superposition_flag                    true
% 59.45/8.01  --sup_passive_queue_type                priority_queues
% 59.45/8.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 59.45/8.01  --sup_passive_queues_freq               [8;1;4]
% 59.45/8.01  --demod_completeness_check              fast
% 59.45/8.01  --demod_use_ground                      true
% 59.45/8.01  --sup_to_prop_solver                    passive
% 59.45/8.01  --sup_prop_simpl_new                    true
% 59.45/8.01  --sup_prop_simpl_given                  true
% 59.45/8.01  --sup_fun_splitting                     true
% 59.45/8.01  --sup_smt_interval                      50000
% 59.45/8.01  
% 59.45/8.01  ------ Superposition Simplification Setup
% 59.45/8.01  
% 59.45/8.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 59.45/8.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 59.45/8.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 59.45/8.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 59.45/8.01  --sup_full_triv                         [TrivRules;PropSubs]
% 59.45/8.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 59.45/8.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 59.45/8.01  --sup_immed_triv                        [TrivRules]
% 59.45/8.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 59.45/8.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 59.45/8.01  --sup_immed_bw_main                     []
% 59.45/8.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 59.45/8.01  --sup_input_triv                        [Unflattening;TrivRules]
% 59.45/8.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 59.45/8.01  --sup_input_bw                          []
% 59.45/8.01  
% 59.45/8.01  ------ Combination Options
% 59.45/8.01  
% 59.45/8.01  --comb_res_mult                         3
% 59.45/8.01  --comb_sup_mult                         2
% 59.45/8.01  --comb_inst_mult                        10
% 59.45/8.01  
% 59.45/8.01  ------ Debug Options
% 59.45/8.01  
% 59.45/8.01  --dbg_backtrace                         false
% 59.45/8.01  --dbg_dump_prop_clauses                 false
% 59.45/8.01  --dbg_dump_prop_clauses_file            -
% 59.45/8.01  --dbg_out_stat                          false
% 59.45/8.01  
% 59.45/8.01  
% 59.45/8.01  
% 59.45/8.01  
% 59.45/8.01  ------ Proving...
% 59.45/8.01  
% 59.45/8.01  
% 59.45/8.01  % SZS status Theorem for theBenchmark.p
% 59.45/8.01  
% 59.45/8.01  % SZS output start CNFRefutation for theBenchmark.p
% 59.45/8.01  
% 59.45/8.01  fof(f32,axiom,(
% 59.45/8.01    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 59.45/8.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.45/8.01  
% 59.45/8.01  fof(f41,plain,(
% 59.45/8.01    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 59.45/8.01    inference(pure_predicate_removal,[],[f32])).
% 59.45/8.01  
% 59.45/8.01  fof(f133,plain,(
% 59.45/8.01    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 59.45/8.01    inference(cnf_transformation,[],[f41])).
% 59.45/8.01  
% 59.45/8.01  fof(f38,conjecture,(
% 59.45/8.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 59.45/8.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.45/8.01  
% 59.45/8.01  fof(f39,negated_conjecture,(
% 59.45/8.01    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 59.45/8.01    inference(negated_conjecture,[],[f38])).
% 59.45/8.01  
% 59.45/8.01  fof(f78,plain,(
% 59.45/8.01    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 59.45/8.01    inference(ennf_transformation,[],[f39])).
% 59.45/8.01  
% 59.45/8.01  fof(f79,plain,(
% 59.45/8.01    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 59.45/8.01    inference(flattening,[],[f78])).
% 59.45/8.01  
% 59.45/8.01  fof(f87,plain,(
% 59.45/8.01    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 59.45/8.01    introduced(choice_axiom,[])).
% 59.45/8.01  
% 59.45/8.01  fof(f86,plain,(
% 59.45/8.01    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 59.45/8.01    introduced(choice_axiom,[])).
% 59.45/8.01  
% 59.45/8.01  fof(f88,plain,(
% 59.45/8.01    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 59.45/8.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f79,f87,f86])).
% 59.45/8.01  
% 59.45/8.01  fof(f146,plain,(
% 59.45/8.01    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 59.45/8.01    inference(cnf_transformation,[],[f88])).
% 59.45/8.01  
% 59.45/8.01  fof(f149,plain,(
% 59.45/8.01    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 59.45/8.01    inference(cnf_transformation,[],[f88])).
% 59.45/8.01  
% 59.45/8.01  fof(f33,axiom,(
% 59.45/8.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 59.45/8.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.45/8.01  
% 59.45/8.01  fof(f70,plain,(
% 59.45/8.01    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 59.45/8.01    inference(ennf_transformation,[],[f33])).
% 59.45/8.01  
% 59.45/8.01  fof(f71,plain,(
% 59.45/8.01    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 59.45/8.01    inference(flattening,[],[f70])).
% 59.45/8.01  
% 59.45/8.01  fof(f134,plain,(
% 59.45/8.01    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 59.45/8.01    inference(cnf_transformation,[],[f71])).
% 59.45/8.01  
% 59.45/8.01  fof(f147,plain,(
% 59.45/8.01    v1_funct_1(sK3)),
% 59.45/8.01    inference(cnf_transformation,[],[f88])).
% 59.45/8.01  
% 59.45/8.01  fof(f144,plain,(
% 59.45/8.01    v1_funct_1(sK2)),
% 59.45/8.01    inference(cnf_transformation,[],[f88])).
% 59.45/8.01  
% 59.45/8.01  fof(f151,plain,(
% 59.45/8.01    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 59.45/8.01    inference(cnf_transformation,[],[f88])).
% 59.45/8.01  
% 59.45/8.01  fof(f31,axiom,(
% 59.45/8.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 59.45/8.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.45/8.01  
% 59.45/8.01  fof(f68,plain,(
% 59.45/8.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 59.45/8.01    inference(ennf_transformation,[],[f31])).
% 59.45/8.01  
% 59.45/8.01  fof(f69,plain,(
% 59.45/8.01    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 59.45/8.01    inference(flattening,[],[f68])).
% 59.45/8.01  
% 59.45/8.01  fof(f132,plain,(
% 59.45/8.01    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 59.45/8.01    inference(cnf_transformation,[],[f69])).
% 59.45/8.01  
% 59.45/8.01  fof(f29,axiom,(
% 59.45/8.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 59.45/8.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.45/8.01  
% 59.45/8.01  fof(f64,plain,(
% 59.45/8.01    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 59.45/8.01    inference(ennf_transformation,[],[f29])).
% 59.45/8.01  
% 59.45/8.01  fof(f65,plain,(
% 59.45/8.01    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 59.45/8.01    inference(flattening,[],[f64])).
% 59.45/8.01  
% 59.45/8.01  fof(f84,plain,(
% 59.45/8.01    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 59.45/8.01    inference(nnf_transformation,[],[f65])).
% 59.45/8.01  
% 59.45/8.01  fof(f127,plain,(
% 59.45/8.01    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 59.45/8.01    inference(cnf_transformation,[],[f84])).
% 59.45/8.01  
% 59.45/8.01  fof(f27,axiom,(
% 59.45/8.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 59.45/8.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.45/8.01  
% 59.45/8.01  fof(f61,plain,(
% 59.45/8.01    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 59.45/8.01    inference(ennf_transformation,[],[f27])).
% 59.45/8.01  
% 59.45/8.01  fof(f62,plain,(
% 59.45/8.01    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 59.45/8.01    inference(flattening,[],[f61])).
% 59.45/8.01  
% 59.45/8.01  fof(f124,plain,(
% 59.45/8.01    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 59.45/8.01    inference(cnf_transformation,[],[f62])).
% 59.45/8.01  
% 59.45/8.01  fof(f34,axiom,(
% 59.45/8.01    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 59.45/8.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.45/8.01  
% 59.45/8.01  fof(f135,plain,(
% 59.45/8.01    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 59.45/8.01    inference(cnf_transformation,[],[f34])).
% 59.45/8.01  
% 59.45/8.01  fof(f168,plain,(
% 59.45/8.01    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 59.45/8.01    inference(definition_unfolding,[],[f124,f135])).
% 59.45/8.01  
% 59.45/8.01  fof(f11,axiom,(
% 59.45/8.01    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 59.45/8.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.45/8.01  
% 59.45/8.01  fof(f103,plain,(
% 59.45/8.01    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 59.45/8.01    inference(cnf_transformation,[],[f11])).
% 59.45/8.01  
% 59.45/8.01  fof(f7,axiom,(
% 59.45/8.01    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 59.45/8.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.45/8.01  
% 59.45/8.01  fof(f82,plain,(
% 59.45/8.01    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 59.45/8.01    inference(nnf_transformation,[],[f7])).
% 59.45/8.01  
% 59.45/8.01  fof(f97,plain,(
% 59.45/8.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 59.45/8.01    inference(cnf_transformation,[],[f82])).
% 59.45/8.01  
% 59.45/8.01  fof(f8,axiom,(
% 59.45/8.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 59.45/8.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.45/8.01  
% 59.45/8.01  fof(f42,plain,(
% 59.45/8.01    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 59.45/8.01    inference(ennf_transformation,[],[f8])).
% 59.45/8.01  
% 59.45/8.01  fof(f99,plain,(
% 59.45/8.01    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 59.45/8.01    inference(cnf_transformation,[],[f42])).
% 59.45/8.01  
% 59.45/8.01  fof(f98,plain,(
% 59.45/8.01    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 59.45/8.01    inference(cnf_transformation,[],[f82])).
% 59.45/8.01  
% 59.45/8.01  fof(f30,axiom,(
% 59.45/8.01    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 59.45/8.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.45/8.01  
% 59.45/8.01  fof(f66,plain,(
% 59.45/8.01    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 59.45/8.01    inference(ennf_transformation,[],[f30])).
% 59.45/8.01  
% 59.45/8.01  fof(f67,plain,(
% 59.45/8.01    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 59.45/8.01    inference(flattening,[],[f66])).
% 59.45/8.01  
% 59.45/8.01  fof(f85,plain,(
% 59.45/8.01    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 59.45/8.01    inference(nnf_transformation,[],[f67])).
% 59.45/8.01  
% 59.45/8.01  fof(f129,plain,(
% 59.45/8.01    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 59.45/8.01    inference(cnf_transformation,[],[f85])).
% 59.45/8.01  
% 59.45/8.01  fof(f35,axiom,(
% 59.45/8.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 59.45/8.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.45/8.01  
% 59.45/8.01  fof(f72,plain,(
% 59.45/8.01    ! [X0,X1,X2] : (! [X3] : (((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 59.45/8.01    inference(ennf_transformation,[],[f35])).
% 59.45/8.01  
% 59.45/8.01  fof(f73,plain,(
% 59.45/8.01    ! [X0,X1,X2] : (! [X3] : ((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 59.45/8.01    inference(flattening,[],[f72])).
% 59.45/8.01  
% 59.45/8.01  fof(f137,plain,(
% 59.45/8.01    ( ! [X2,X0,X3,X1] : (v2_funct_2(X3,X0) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 59.45/8.01    inference(cnf_transformation,[],[f73])).
% 59.45/8.01  
% 59.45/8.01  fof(f28,axiom,(
% 59.45/8.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 59.45/8.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.45/8.01  
% 59.45/8.01  fof(f63,plain,(
% 59.45/8.01    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 59.45/8.01    inference(ennf_transformation,[],[f28])).
% 59.45/8.01  
% 59.45/8.01  fof(f126,plain,(
% 59.45/8.01    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 59.45/8.01    inference(cnf_transformation,[],[f63])).
% 59.45/8.01  
% 59.45/8.01  fof(f145,plain,(
% 59.45/8.01    v1_funct_2(sK2,sK0,sK1)),
% 59.45/8.01    inference(cnf_transformation,[],[f88])).
% 59.45/8.01  
% 59.45/8.01  fof(f148,plain,(
% 59.45/8.01    v1_funct_2(sK3,sK1,sK0)),
% 59.45/8.01    inference(cnf_transformation,[],[f88])).
% 59.45/8.01  
% 59.45/8.01  fof(f26,axiom,(
% 59.45/8.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0))))),
% 59.45/8.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.45/8.01  
% 59.45/8.01  fof(f59,plain,(
% 59.45/8.01    ! [X0] : (((k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 59.45/8.01    inference(ennf_transformation,[],[f26])).
% 59.45/8.01  
% 59.45/8.01  fof(f60,plain,(
% 59.45/8.01    ! [X0] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 59.45/8.01    inference(flattening,[],[f59])).
% 59.45/8.01  
% 59.45/8.01  fof(f122,plain,(
% 59.45/8.01    ( ! [X0] : (k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 59.45/8.01    inference(cnf_transformation,[],[f60])).
% 59.45/8.01  
% 59.45/8.01  fof(f150,plain,(
% 59.45/8.01    k2_relset_1(sK0,sK1,sK2) = sK1),
% 59.45/8.01    inference(cnf_transformation,[],[f88])).
% 59.45/8.01  
% 59.45/8.01  fof(f37,axiom,(
% 59.45/8.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 59.45/8.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.45/8.01  
% 59.45/8.01  fof(f76,plain,(
% 59.45/8.01    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 59.45/8.01    inference(ennf_transformation,[],[f37])).
% 59.45/8.01  
% 59.45/8.01  fof(f77,plain,(
% 59.45/8.01    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 59.45/8.01    inference(flattening,[],[f76])).
% 59.45/8.01  
% 59.45/8.01  fof(f143,plain,(
% 59.45/8.01    ( ! [X2,X0,X1] : (k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 59.45/8.01    inference(cnf_transformation,[],[f77])).
% 59.45/8.01  
% 59.45/8.01  fof(f152,plain,(
% 59.45/8.01    v2_funct_1(sK2)),
% 59.45/8.01    inference(cnf_transformation,[],[f88])).
% 59.45/8.01  
% 59.45/8.01  fof(f154,plain,(
% 59.45/8.01    k1_xboole_0 != sK1),
% 59.45/8.01    inference(cnf_transformation,[],[f88])).
% 59.45/8.01  
% 59.45/8.01  fof(f18,axiom,(
% 59.45/8.01    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 59.45/8.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.45/8.01  
% 59.45/8.01  fof(f111,plain,(
% 59.45/8.01    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 59.45/8.01    inference(cnf_transformation,[],[f18])).
% 59.45/8.01  
% 59.45/8.01  fof(f162,plain,(
% 59.45/8.01    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 59.45/8.01    inference(definition_unfolding,[],[f111,f135])).
% 59.45/8.01  
% 59.45/8.01  fof(f125,plain,(
% 59.45/8.01    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 59.45/8.01    inference(cnf_transformation,[],[f63])).
% 59.45/8.01  
% 59.45/8.01  fof(f9,axiom,(
% 59.45/8.01    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 59.45/8.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.45/8.01  
% 59.45/8.01  fof(f43,plain,(
% 59.45/8.01    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 59.45/8.01    inference(ennf_transformation,[],[f9])).
% 59.45/8.01  
% 59.45/8.01  fof(f83,plain,(
% 59.45/8.01    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 59.45/8.01    inference(nnf_transformation,[],[f43])).
% 59.45/8.01  
% 59.45/8.01  fof(f100,plain,(
% 59.45/8.01    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 59.45/8.01    inference(cnf_transformation,[],[f83])).
% 59.45/8.01  
% 59.45/8.01  fof(f2,axiom,(
% 59.45/8.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 59.45/8.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.45/8.01  
% 59.45/8.01  fof(f80,plain,(
% 59.45/8.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 59.45/8.01    inference(nnf_transformation,[],[f2])).
% 59.45/8.01  
% 59.45/8.01  fof(f81,plain,(
% 59.45/8.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 59.45/8.01    inference(flattening,[],[f80])).
% 59.45/8.01  
% 59.45/8.01  fof(f92,plain,(
% 59.45/8.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 59.45/8.01    inference(cnf_transformation,[],[f81])).
% 59.45/8.01  
% 59.45/8.01  fof(f23,axiom,(
% 59.45/8.01    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 59.45/8.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.45/8.01  
% 59.45/8.01  fof(f118,plain,(
% 59.45/8.01    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 59.45/8.01    inference(cnf_transformation,[],[f23])).
% 59.45/8.01  
% 59.45/8.01  fof(f166,plain,(
% 59.45/8.01    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 59.45/8.01    inference(definition_unfolding,[],[f118,f135])).
% 59.45/8.01  
% 59.45/8.01  fof(f36,axiom,(
% 59.45/8.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 59.45/8.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.45/8.01  
% 59.45/8.01  fof(f74,plain,(
% 59.45/8.01    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 59.45/8.01    inference(ennf_transformation,[],[f36])).
% 59.45/8.01  
% 59.45/8.01  fof(f75,plain,(
% 59.45/8.01    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 59.45/8.01    inference(flattening,[],[f74])).
% 59.45/8.01  
% 59.45/8.01  fof(f140,plain,(
% 59.45/8.01    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X4) | k1_xboole_0 = X2 | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 59.45/8.01    inference(cnf_transformation,[],[f75])).
% 59.45/8.01  
% 59.45/8.01  fof(f153,plain,(
% 59.45/8.01    k1_xboole_0 != sK0),
% 59.45/8.01    inference(cnf_transformation,[],[f88])).
% 59.45/8.01  
% 59.45/8.01  fof(f90,plain,(
% 59.45/8.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 59.45/8.01    inference(cnf_transformation,[],[f81])).
% 59.45/8.01  
% 59.45/8.01  fof(f170,plain,(
% 59.45/8.01    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 59.45/8.01    inference(equality_resolution,[],[f90])).
% 59.45/8.01  
% 59.45/8.01  fof(f24,axiom,(
% 59.45/8.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0)) => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)))))),
% 59.45/8.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.45/8.01  
% 59.45/8.01  fof(f55,plain,(
% 59.45/8.01    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 59.45/8.01    inference(ennf_transformation,[],[f24])).
% 59.45/8.01  
% 59.45/8.01  fof(f56,plain,(
% 59.45/8.01    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 59.45/8.01    inference(flattening,[],[f55])).
% 59.45/8.01  
% 59.45/8.01  fof(f119,plain,(
% 59.45/8.01    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 59.45/8.01    inference(cnf_transformation,[],[f56])).
% 59.45/8.01  
% 59.45/8.01  fof(f25,axiom,(
% 59.45/8.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 59.45/8.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.45/8.01  
% 59.45/8.01  fof(f57,plain,(
% 59.45/8.01    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 59.45/8.01    inference(ennf_transformation,[],[f25])).
% 59.45/8.01  
% 59.45/8.01  fof(f58,plain,(
% 59.45/8.01    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 59.45/8.01    inference(flattening,[],[f57])).
% 59.45/8.01  
% 59.45/8.01  fof(f120,plain,(
% 59.45/8.01    ( ! [X0] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 59.45/8.01    inference(cnf_transformation,[],[f58])).
% 59.45/8.01  
% 59.45/8.01  fof(f142,plain,(
% 59.45/8.01    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 59.45/8.01    inference(cnf_transformation,[],[f77])).
% 59.45/8.01  
% 59.45/8.01  fof(f22,axiom,(
% 59.45/8.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 59.45/8.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.45/8.01  
% 59.45/8.01  fof(f53,plain,(
% 59.45/8.01    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 59.45/8.01    inference(ennf_transformation,[],[f22])).
% 59.45/8.01  
% 59.45/8.01  fof(f54,plain,(
% 59.45/8.01    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 59.45/8.01    inference(flattening,[],[f53])).
% 59.45/8.01  
% 59.45/8.01  fof(f116,plain,(
% 59.45/8.01    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 59.45/8.01    inference(cnf_transformation,[],[f54])).
% 59.45/8.01  
% 59.45/8.01  fof(f12,axiom,(
% 59.45/8.01    ! [X0] : (v1_relat_1(X0) => k4_relat_1(k4_relat_1(X0)) = X0)),
% 59.45/8.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.45/8.01  
% 59.45/8.01  fof(f45,plain,(
% 59.45/8.01    ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 59.45/8.01    inference(ennf_transformation,[],[f12])).
% 59.45/8.01  
% 59.45/8.01  fof(f104,plain,(
% 59.45/8.01    ( ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 59.45/8.01    inference(cnf_transformation,[],[f45])).
% 59.45/8.01  
% 59.45/8.01  fof(f155,plain,(
% 59.45/8.01    k2_funct_1(sK2) != sK3),
% 59.45/8.01    inference(cnf_transformation,[],[f88])).
% 59.45/8.01  
% 59.45/8.01  cnf(c_40,plain,
% 59.45/8.01      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 59.45/8.01      inference(cnf_transformation,[],[f133]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_2708,plain,
% 59.45/8.01      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 59.45/8.01      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_59,negated_conjecture,
% 59.45/8.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 59.45/8.01      inference(cnf_transformation,[],[f146]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_2694,plain,
% 59.45/8.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 59.45/8.01      inference(predicate_to_equality,[status(thm)],[c_59]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_56,negated_conjecture,
% 59.45/8.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 59.45/8.01      inference(cnf_transformation,[],[f149]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_2697,plain,
% 59.45/8.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 59.45/8.01      inference(predicate_to_equality,[status(thm)],[c_56]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_41,plain,
% 59.45/8.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 59.45/8.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 59.45/8.01      | ~ v1_funct_1(X0)
% 59.45/8.01      | ~ v1_funct_1(X3)
% 59.45/8.01      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 59.45/8.01      inference(cnf_transformation,[],[f134]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_2707,plain,
% 59.45/8.01      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 59.45/8.01      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 59.45/8.01      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 59.45/8.01      | v1_funct_1(X5) != iProver_top
% 59.45/8.01      | v1_funct_1(X4) != iProver_top ),
% 59.45/8.01      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_10546,plain,
% 59.45/8.01      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 59.45/8.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 59.45/8.01      | v1_funct_1(X2) != iProver_top
% 59.45/8.01      | v1_funct_1(sK3) != iProver_top ),
% 59.45/8.01      inference(superposition,[status(thm)],[c_2697,c_2707]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_58,negated_conjecture,
% 59.45/8.01      ( v1_funct_1(sK3) ),
% 59.45/8.01      inference(cnf_transformation,[],[f147]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_65,plain,
% 59.45/8.01      ( v1_funct_1(sK3) = iProver_top ),
% 59.45/8.01      inference(predicate_to_equality,[status(thm)],[c_58]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_10630,plain,
% 59.45/8.01      ( v1_funct_1(X2) != iProver_top
% 59.45/8.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 59.45/8.01      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 59.45/8.01      inference(global_propositional_subsumption,
% 59.45/8.01                [status(thm)],
% 59.45/8.01                [c_10546,c_65]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_10631,plain,
% 59.45/8.01      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 59.45/8.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 59.45/8.01      | v1_funct_1(X2) != iProver_top ),
% 59.45/8.01      inference(renaming,[status(thm)],[c_10630]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_10640,plain,
% 59.45/8.01      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 59.45/8.01      | v1_funct_1(sK2) != iProver_top ),
% 59.45/8.01      inference(superposition,[status(thm)],[c_2694,c_10631]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_61,negated_conjecture,
% 59.45/8.01      ( v1_funct_1(sK2) ),
% 59.45/8.01      inference(cnf_transformation,[],[f144]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_62,plain,
% 59.45/8.01      ( v1_funct_1(sK2) = iProver_top ),
% 59.45/8.01      inference(predicate_to_equality,[status(thm)],[c_61]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_10660,plain,
% 59.45/8.01      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 59.45/8.01      inference(global_propositional_subsumption,
% 59.45/8.01                [status(thm)],
% 59.45/8.01                [c_10640,c_62]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_54,negated_conjecture,
% 59.45/8.01      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 59.45/8.01      inference(cnf_transformation,[],[f151]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_2698,plain,
% 59.45/8.01      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) = iProver_top ),
% 59.45/8.01      inference(predicate_to_equality,[status(thm)],[c_54]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_10662,plain,
% 59.45/8.01      ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) = iProver_top ),
% 59.45/8.01      inference(demodulation,[status(thm)],[c_10660,c_2698]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_38,plain,
% 59.45/8.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 59.45/8.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 59.45/8.01      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 59.45/8.01      | ~ v1_funct_1(X0)
% 59.45/8.01      | ~ v1_funct_1(X3) ),
% 59.45/8.01      inference(cnf_transformation,[],[f132]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_2710,plain,
% 59.45/8.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 59.45/8.01      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 59.45/8.01      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 59.45/8.01      | v1_funct_1(X0) != iProver_top
% 59.45/8.01      | v1_funct_1(X3) != iProver_top ),
% 59.45/8.01      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_10664,plain,
% 59.45/8.01      ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 59.45/8.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 59.45/8.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 59.45/8.01      | v1_funct_1(sK3) != iProver_top
% 59.45/8.01      | v1_funct_1(sK2) != iProver_top ),
% 59.45/8.01      inference(superposition,[status(thm)],[c_10660,c_2710]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_64,plain,
% 59.45/8.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 59.45/8.01      inference(predicate_to_equality,[status(thm)],[c_59]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_67,plain,
% 59.45/8.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 59.45/8.01      inference(predicate_to_equality,[status(thm)],[c_56]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_12078,plain,
% 59.45/8.01      ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 59.45/8.01      inference(global_propositional_subsumption,
% 59.45/8.01                [status(thm)],
% 59.45/8.01                [c_10664,c_62,c_64,c_65,c_67]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_35,plain,
% 59.45/8.01      ( ~ r2_relset_1(X0,X1,X2,X3)
% 59.45/8.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 59.45/8.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 59.45/8.01      | X3 = X2 ),
% 59.45/8.01      inference(cnf_transformation,[],[f127]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_2711,plain,
% 59.45/8.01      ( X0 = X1
% 59.45/8.01      | r2_relset_1(X2,X3,X1,X0) != iProver_top
% 59.45/8.01      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 59.45/8.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top ),
% 59.45/8.01      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_12088,plain,
% 59.45/8.01      ( k5_relat_1(sK2,sK3) = X0
% 59.45/8.01      | r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),X0) != iProver_top
% 59.45/8.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 59.45/8.01      inference(superposition,[status(thm)],[c_12078,c_2711]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_18076,plain,
% 59.45/8.01      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 59.45/8.01      | m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 59.45/8.01      inference(superposition,[status(thm)],[c_10662,c_12088]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_18081,plain,
% 59.45/8.01      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 59.45/8.01      inference(superposition,[status(thm)],[c_2708,c_18076]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_31,plain,
% 59.45/8.01      ( ~ v1_funct_1(X0)
% 59.45/8.01      | ~ v1_funct_1(X1)
% 59.45/8.01      | ~ v2_funct_1(X0)
% 59.45/8.01      | ~ v1_relat_1(X0)
% 59.45/8.01      | ~ v1_relat_1(X1)
% 59.45/8.01      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
% 59.45/8.01      | k2_funct_1(X0) = X1
% 59.45/8.01      | k2_relat_1(X1) != k1_relat_1(X0) ),
% 59.45/8.01      inference(cnf_transformation,[],[f168]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_2713,plain,
% 59.45/8.01      ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 59.45/8.01      | k2_funct_1(X1) = X0
% 59.45/8.01      | k2_relat_1(X0) != k1_relat_1(X1)
% 59.45/8.01      | v1_funct_1(X1) != iProver_top
% 59.45/8.01      | v1_funct_1(X0) != iProver_top
% 59.45/8.01      | v2_funct_1(X1) != iProver_top
% 59.45/8.01      | v1_relat_1(X1) != iProver_top
% 59.45/8.01      | v1_relat_1(X0) != iProver_top ),
% 59.45/8.01      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_18183,plain,
% 59.45/8.01      ( k2_funct_1(sK3) = sK2
% 59.45/8.01      | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
% 59.45/8.01      | k2_relat_1(sK2) != k1_relat_1(sK3)
% 59.45/8.01      | v1_funct_1(sK3) != iProver_top
% 59.45/8.01      | v1_funct_1(sK2) != iProver_top
% 59.45/8.01      | v2_funct_1(sK3) != iProver_top
% 59.45/8.01      | v1_relat_1(sK3) != iProver_top
% 59.45/8.01      | v1_relat_1(sK2) != iProver_top ),
% 59.45/8.01      inference(superposition,[status(thm)],[c_18081,c_2713]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_10,plain,
% 59.45/8.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 59.45/8.01      inference(cnf_transformation,[],[f103]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_2731,plain,
% 59.45/8.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 59.45/8.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_5,plain,
% 59.45/8.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 59.45/8.01      inference(cnf_transformation,[],[f97]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_2733,plain,
% 59.45/8.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 59.45/8.01      | r1_tarski(X0,X1) = iProver_top ),
% 59.45/8.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_4956,plain,
% 59.45/8.01      ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK0)) = iProver_top ),
% 59.45/8.01      inference(superposition,[status(thm)],[c_2697,c_2733]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_6,plain,
% 59.45/8.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 59.45/8.01      | ~ v1_relat_1(X1)
% 59.45/8.01      | v1_relat_1(X0) ),
% 59.45/8.01      inference(cnf_transformation,[],[f99]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_4,plain,
% 59.45/8.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 59.45/8.01      inference(cnf_transformation,[],[f98]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_435,plain,
% 59.45/8.01      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 59.45/8.01      inference(prop_impl,[status(thm)],[c_4]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_436,plain,
% 59.45/8.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 59.45/8.01      inference(renaming,[status(thm)],[c_435]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_538,plain,
% 59.45/8.01      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 59.45/8.01      inference(bin_hyper_res,[status(thm)],[c_6,c_436]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_2691,plain,
% 59.45/8.01      ( r1_tarski(X0,X1) != iProver_top
% 59.45/8.01      | v1_relat_1(X1) != iProver_top
% 59.45/8.01      | v1_relat_1(X0) = iProver_top ),
% 59.45/8.01      inference(predicate_to_equality,[status(thm)],[c_538]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_11277,plain,
% 59.45/8.01      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 59.45/8.01      | v1_relat_1(sK3) = iProver_top ),
% 59.45/8.01      inference(superposition,[status(thm)],[c_4956,c_2691]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_11309,plain,
% 59.45/8.01      ( v1_relat_1(sK3) = iProver_top ),
% 59.45/8.01      inference(superposition,[status(thm)],[c_2731,c_11277]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_37,plain,
% 59.45/8.01      ( ~ v2_funct_2(X0,X1)
% 59.45/8.01      | ~ v5_relat_1(X0,X1)
% 59.45/8.01      | ~ v1_relat_1(X0)
% 59.45/8.01      | k2_relat_1(X0) = X1 ),
% 59.45/8.01      inference(cnf_transformation,[],[f129]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_42,plain,
% 59.45/8.01      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 59.45/8.01      | ~ v1_funct_2(X3,X1,X0)
% 59.45/8.01      | ~ v1_funct_2(X2,X0,X1)
% 59.45/8.01      | v2_funct_2(X3,X0)
% 59.45/8.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 59.45/8.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 59.45/8.01      | ~ v1_funct_1(X3)
% 59.45/8.01      | ~ v1_funct_1(X2) ),
% 59.45/8.01      inference(cnf_transformation,[],[f137]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_783,plain,
% 59.45/8.01      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 59.45/8.01      | ~ v1_funct_2(X3,X1,X0)
% 59.45/8.01      | ~ v1_funct_2(X2,X0,X1)
% 59.45/8.01      | ~ v5_relat_1(X4,X5)
% 59.45/8.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 59.45/8.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 59.45/8.01      | ~ v1_funct_1(X2)
% 59.45/8.01      | ~ v1_funct_1(X3)
% 59.45/8.01      | ~ v1_relat_1(X4)
% 59.45/8.01      | X3 != X4
% 59.45/8.01      | X0 != X5
% 59.45/8.01      | k2_relat_1(X4) = X5 ),
% 59.45/8.01      inference(resolution_lifted,[status(thm)],[c_37,c_42]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_784,plain,
% 59.45/8.01      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 59.45/8.01      | ~ v1_funct_2(X3,X1,X0)
% 59.45/8.01      | ~ v1_funct_2(X2,X0,X1)
% 59.45/8.01      | ~ v5_relat_1(X3,X0)
% 59.45/8.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 59.45/8.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 59.45/8.01      | ~ v1_funct_1(X3)
% 59.45/8.01      | ~ v1_funct_1(X2)
% 59.45/8.01      | ~ v1_relat_1(X3)
% 59.45/8.01      | k2_relat_1(X3) = X0 ),
% 59.45/8.01      inference(unflattening,[status(thm)],[c_783]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_32,plain,
% 59.45/8.01      ( v5_relat_1(X0,X1)
% 59.45/8.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 59.45/8.01      inference(cnf_transformation,[],[f126]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_808,plain,
% 59.45/8.01      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 59.45/8.01      | ~ v1_funct_2(X3,X1,X0)
% 59.45/8.01      | ~ v1_funct_2(X2,X0,X1)
% 59.45/8.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 59.45/8.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 59.45/8.01      | ~ v1_funct_1(X3)
% 59.45/8.01      | ~ v1_funct_1(X2)
% 59.45/8.01      | ~ v1_relat_1(X3)
% 59.45/8.01      | k2_relat_1(X3) = X0 ),
% 59.45/8.01      inference(forward_subsumption_resolution,
% 59.45/8.01                [status(thm)],
% 59.45/8.01                [c_784,c_32]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_2689,plain,
% 59.45/8.01      ( k2_relat_1(X0) = X1
% 59.45/8.01      | r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X0),k6_partfun1(X1)) != iProver_top
% 59.45/8.01      | v1_funct_2(X3,X1,X2) != iProver_top
% 59.45/8.01      | v1_funct_2(X0,X2,X1) != iProver_top
% 59.45/8.01      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 59.45/8.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 59.45/8.01      | v1_funct_1(X3) != iProver_top
% 59.45/8.01      | v1_funct_1(X0) != iProver_top
% 59.45/8.01      | v1_relat_1(X0) != iProver_top ),
% 59.45/8.01      inference(predicate_to_equality,[status(thm)],[c_808]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_3655,plain,
% 59.45/8.01      ( k2_relat_1(sK3) = sK0
% 59.45/8.01      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 59.45/8.01      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 59.45/8.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 59.45/8.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 59.45/8.01      | v1_funct_1(sK3) != iProver_top
% 59.45/8.01      | v1_funct_1(sK2) != iProver_top
% 59.45/8.01      | v1_relat_1(sK3) != iProver_top ),
% 59.45/8.01      inference(superposition,[status(thm)],[c_2698,c_2689]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_60,negated_conjecture,
% 59.45/8.01      ( v1_funct_2(sK2,sK0,sK1) ),
% 59.45/8.01      inference(cnf_transformation,[],[f145]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_63,plain,
% 59.45/8.01      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 59.45/8.01      inference(predicate_to_equality,[status(thm)],[c_60]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_57,negated_conjecture,
% 59.45/8.01      ( v1_funct_2(sK3,sK1,sK0) ),
% 59.45/8.01      inference(cnf_transformation,[],[f148]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_66,plain,
% 59.45/8.01      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 59.45/8.01      inference(predicate_to_equality,[status(thm)],[c_57]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_3658,plain,
% 59.45/8.01      ( k2_relat_1(sK3) = sK0 | v1_relat_1(sK3) != iProver_top ),
% 59.45/8.01      inference(global_propositional_subsumption,
% 59.45/8.01                [status(thm)],
% 59.45/8.01                [c_3655,c_62,c_63,c_64,c_65,c_66,c_67]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_11573,plain,
% 59.45/8.01      ( k2_relat_1(sK3) = sK0 ),
% 59.45/8.01      inference(superposition,[status(thm)],[c_11309,c_3658]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_4957,plain,
% 59.45/8.01      ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 59.45/8.01      inference(superposition,[status(thm)],[c_2694,c_2733]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_11278,plain,
% 59.45/8.01      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 59.45/8.01      | v1_relat_1(sK2) = iProver_top ),
% 59.45/8.01      inference(superposition,[status(thm)],[c_4957,c_2691]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_11336,plain,
% 59.45/8.01      ( v1_relat_1(sK2) = iProver_top ),
% 59.45/8.01      inference(superposition,[status(thm)],[c_2731,c_11278]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_2692,plain,
% 59.45/8.01      ( v1_funct_1(sK2) = iProver_top ),
% 59.45/8.01      inference(predicate_to_equality,[status(thm)],[c_61]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_30,plain,
% 59.45/8.01      ( ~ v1_funct_1(X0)
% 59.45/8.01      | ~ v2_funct_1(X0)
% 59.45/8.01      | ~ v1_relat_1(X0)
% 59.45/8.01      | k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) ),
% 59.45/8.01      inference(cnf_transformation,[],[f122]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_2714,plain,
% 59.45/8.01      ( k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0)
% 59.45/8.01      | v1_funct_1(X0) != iProver_top
% 59.45/8.01      | v2_funct_1(X0) != iProver_top
% 59.45/8.01      | v1_relat_1(X0) != iProver_top ),
% 59.45/8.01      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_6968,plain,
% 59.45/8.01      ( k1_relat_1(k5_relat_1(k2_funct_1(sK2),sK2)) = k2_relat_1(sK2)
% 59.45/8.01      | v2_funct_1(sK2) != iProver_top
% 59.45/8.01      | v1_relat_1(sK2) != iProver_top ),
% 59.45/8.01      inference(superposition,[status(thm)],[c_2692,c_2714]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_55,negated_conjecture,
% 59.45/8.01      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 59.45/8.01      inference(cnf_transformation,[],[f150]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_48,plain,
% 59.45/8.01      ( ~ v1_funct_2(X0,X1,X2)
% 59.45/8.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 59.45/8.01      | ~ v1_funct_1(X0)
% 59.45/8.01      | ~ v2_funct_1(X0)
% 59.45/8.01      | k2_relset_1(X1,X2,X0) != X2
% 59.45/8.01      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
% 59.45/8.01      | k1_xboole_0 = X2 ),
% 59.45/8.01      inference(cnf_transformation,[],[f143]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_2701,plain,
% 59.45/8.01      ( k2_relset_1(X0,X1,X2) != X1
% 59.45/8.01      | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
% 59.45/8.01      | k1_xboole_0 = X1
% 59.45/8.01      | v1_funct_2(X2,X0,X1) != iProver_top
% 59.45/8.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 59.45/8.01      | v1_funct_1(X2) != iProver_top
% 59.45/8.01      | v2_funct_1(X2) != iProver_top ),
% 59.45/8.01      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_6067,plain,
% 59.45/8.01      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 59.45/8.01      | sK1 = k1_xboole_0
% 59.45/8.01      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 59.45/8.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 59.45/8.01      | v1_funct_1(sK2) != iProver_top
% 59.45/8.01      | v2_funct_1(sK2) != iProver_top ),
% 59.45/8.01      inference(superposition,[status(thm)],[c_55,c_2701]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_53,negated_conjecture,
% 59.45/8.01      ( v2_funct_1(sK2) ),
% 59.45/8.01      inference(cnf_transformation,[],[f152]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_51,negated_conjecture,
% 59.45/8.01      ( k1_xboole_0 != sK1 ),
% 59.45/8.01      inference(cnf_transformation,[],[f154]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_2816,plain,
% 59.45/8.01      ( ~ v1_funct_2(X0,X1,sK1)
% 59.45/8.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 59.45/8.01      | ~ v1_funct_1(X0)
% 59.45/8.01      | ~ v2_funct_1(X0)
% 59.45/8.01      | k2_relset_1(X1,sK1,X0) != sK1
% 59.45/8.01      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(sK1)
% 59.45/8.01      | k1_xboole_0 = sK1 ),
% 59.45/8.01      inference(instantiation,[status(thm)],[c_48]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_2967,plain,
% 59.45/8.01      ( ~ v1_funct_2(sK2,X0,sK1)
% 59.45/8.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
% 59.45/8.01      | ~ v1_funct_1(sK2)
% 59.45/8.01      | ~ v2_funct_1(sK2)
% 59.45/8.01      | k2_relset_1(X0,sK1,sK2) != sK1
% 59.45/8.01      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 59.45/8.01      | k1_xboole_0 = sK1 ),
% 59.45/8.01      inference(instantiation,[status(thm)],[c_2816]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_3089,plain,
% 59.45/8.01      ( ~ v1_funct_2(sK2,sK0,sK1)
% 59.45/8.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 59.45/8.01      | ~ v1_funct_1(sK2)
% 59.45/8.01      | ~ v2_funct_1(sK2)
% 59.45/8.01      | k2_relset_1(sK0,sK1,sK2) != sK1
% 59.45/8.01      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 59.45/8.01      | k1_xboole_0 = sK1 ),
% 59.45/8.01      inference(instantiation,[status(thm)],[c_2967]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_6550,plain,
% 59.45/8.01      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
% 59.45/8.01      inference(global_propositional_subsumption,
% 59.45/8.01                [status(thm)],
% 59.45/8.01                [c_6067,c_61,c_60,c_59,c_55,c_53,c_51,c_3089]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_6969,plain,
% 59.45/8.01      ( k1_relat_1(k6_partfun1(sK1)) = k2_relat_1(sK2)
% 59.45/8.01      | v2_funct_1(sK2) != iProver_top
% 59.45/8.01      | v1_relat_1(sK2) != iProver_top ),
% 59.45/8.01      inference(light_normalisation,[status(thm)],[c_6968,c_6550]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_19,plain,
% 59.45/8.01      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 59.45/8.01      inference(cnf_transformation,[],[f162]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_6970,plain,
% 59.45/8.01      ( k2_relat_1(sK2) = sK1
% 59.45/8.01      | v2_funct_1(sK2) != iProver_top
% 59.45/8.01      | v1_relat_1(sK2) != iProver_top ),
% 59.45/8.01      inference(demodulation,[status(thm)],[c_6969,c_19]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_69,plain,
% 59.45/8.01      ( v2_funct_1(sK2) = iProver_top ),
% 59.45/8.01      inference(predicate_to_equality,[status(thm)],[c_53]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_7039,plain,
% 59.45/8.01      ( k2_relat_1(sK2) = sK1 | v1_relat_1(sK2) != iProver_top ),
% 59.45/8.01      inference(global_propositional_subsumption,
% 59.45/8.01                [status(thm)],
% 59.45/8.01                [c_6970,c_69]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_11610,plain,
% 59.45/8.01      ( k2_relat_1(sK2) = sK1 ),
% 59.45/8.01      inference(superposition,[status(thm)],[c_11336,c_7039]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_18188,plain,
% 59.45/8.01      ( k2_funct_1(sK3) = sK2
% 59.45/8.01      | k6_partfun1(sK0) != k6_partfun1(sK0)
% 59.45/8.01      | k1_relat_1(sK3) != sK1
% 59.45/8.01      | v1_funct_1(sK3) != iProver_top
% 59.45/8.01      | v1_funct_1(sK2) != iProver_top
% 59.45/8.01      | v2_funct_1(sK3) != iProver_top
% 59.45/8.01      | v1_relat_1(sK3) != iProver_top
% 59.45/8.01      | v1_relat_1(sK2) != iProver_top ),
% 59.45/8.01      inference(light_normalisation,
% 59.45/8.01                [status(thm)],
% 59.45/8.01                [c_18183,c_11573,c_11610]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_18189,plain,
% 59.45/8.01      ( k2_funct_1(sK3) = sK2
% 59.45/8.01      | k1_relat_1(sK3) != sK1
% 59.45/8.01      | v1_funct_1(sK3) != iProver_top
% 59.45/8.01      | v1_funct_1(sK2) != iProver_top
% 59.45/8.01      | v2_funct_1(sK3) != iProver_top
% 59.45/8.01      | v1_relat_1(sK3) != iProver_top
% 59.45/8.01      | v1_relat_1(sK2) != iProver_top ),
% 59.45/8.01      inference(equality_resolution_simp,[status(thm)],[c_18188]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_33,plain,
% 59.45/8.01      ( v4_relat_1(X0,X1)
% 59.45/8.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 59.45/8.01      inference(cnf_transformation,[],[f125]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_8,plain,
% 59.45/8.01      ( ~ v4_relat_1(X0,X1)
% 59.45/8.01      | r1_tarski(k1_relat_1(X0),X1)
% 59.45/8.01      | ~ v1_relat_1(X0) ),
% 59.45/8.01      inference(cnf_transformation,[],[f100]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_723,plain,
% 59.45/8.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 59.45/8.01      | r1_tarski(k1_relat_1(X0),X1)
% 59.45/8.01      | ~ v1_relat_1(X0) ),
% 59.45/8.01      inference(resolution,[status(thm)],[c_33,c_8]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_2690,plain,
% 59.45/8.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 59.45/8.01      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 59.45/8.01      | v1_relat_1(X0) != iProver_top ),
% 59.45/8.01      inference(predicate_to_equality,[status(thm)],[c_723]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_3785,plain,
% 59.45/8.01      ( r1_tarski(k1_relat_1(sK3),sK1) = iProver_top
% 59.45/8.01      | v1_relat_1(sK3) != iProver_top ),
% 59.45/8.01      inference(superposition,[status(thm)],[c_2697,c_2690]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_1,plain,
% 59.45/8.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 59.45/8.01      inference(cnf_transformation,[],[f92]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_2736,plain,
% 59.45/8.01      ( X0 = X1
% 59.45/8.01      | r1_tarski(X0,X1) != iProver_top
% 59.45/8.01      | r1_tarski(X1,X0) != iProver_top ),
% 59.45/8.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_6323,plain,
% 59.45/8.01      ( k1_relat_1(sK3) = sK1
% 59.45/8.01      | r1_tarski(sK1,k1_relat_1(sK3)) != iProver_top
% 59.45/8.01      | v1_relat_1(sK3) != iProver_top ),
% 59.45/8.01      inference(superposition,[status(thm)],[c_3785,c_2736]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_24,plain,
% 59.45/8.01      ( v2_funct_1(k6_partfun1(X0)) ),
% 59.45/8.01      inference(cnf_transformation,[],[f166]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_10783,plain,
% 59.45/8.01      ( v2_funct_1(k6_partfun1(sK0)) ),
% 59.45/8.01      inference(instantiation,[status(thm)],[c_24]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_10784,plain,
% 59.45/8.01      ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
% 59.45/8.01      inference(predicate_to_equality,[status(thm)],[c_10783]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_45,plain,
% 59.45/8.01      ( ~ v1_funct_2(X0,X1,X2)
% 59.45/8.01      | ~ v1_funct_2(X3,X4,X1)
% 59.45/8.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 59.45/8.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 59.45/8.01      | ~ v1_funct_1(X0)
% 59.45/8.01      | ~ v1_funct_1(X3)
% 59.45/8.01      | v2_funct_1(X0)
% 59.45/8.01      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 59.45/8.01      | k2_relset_1(X4,X1,X3) != X1
% 59.45/8.01      | k1_xboole_0 = X2 ),
% 59.45/8.01      inference(cnf_transformation,[],[f140]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_2704,plain,
% 59.45/8.01      ( k2_relset_1(X0,X1,X2) != X1
% 59.45/8.01      | k1_xboole_0 = X3
% 59.45/8.01      | v1_funct_2(X4,X1,X3) != iProver_top
% 59.45/8.01      | v1_funct_2(X2,X0,X1) != iProver_top
% 59.45/8.01      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
% 59.45/8.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 59.45/8.01      | v1_funct_1(X4) != iProver_top
% 59.45/8.01      | v1_funct_1(X2) != iProver_top
% 59.45/8.01      | v2_funct_1(X4) = iProver_top
% 59.45/8.01      | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top ),
% 59.45/8.01      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_8325,plain,
% 59.45/8.01      ( k1_xboole_0 = X0
% 59.45/8.01      | v1_funct_2(X1,sK1,X0) != iProver_top
% 59.45/8.01      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 59.45/8.01      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 59.45/8.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 59.45/8.01      | v1_funct_1(X1) != iProver_top
% 59.45/8.01      | v1_funct_1(sK2) != iProver_top
% 59.45/8.01      | v2_funct_1(X1) = iProver_top
% 59.45/8.01      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
% 59.45/8.01      inference(superposition,[status(thm)],[c_55,c_2704]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_8904,plain,
% 59.45/8.01      ( v1_funct_1(X1) != iProver_top
% 59.45/8.01      | v1_funct_2(X1,sK1,X0) != iProver_top
% 59.45/8.01      | k1_xboole_0 = X0
% 59.45/8.01      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 59.45/8.01      | v2_funct_1(X1) = iProver_top
% 59.45/8.01      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
% 59.45/8.01      inference(global_propositional_subsumption,
% 59.45/8.01                [status(thm)],
% 59.45/8.01                [c_8325,c_62,c_63,c_64]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_8905,plain,
% 59.45/8.01      ( k1_xboole_0 = X0
% 59.45/8.01      | v1_funct_2(X1,sK1,X0) != iProver_top
% 59.45/8.01      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 59.45/8.01      | v1_funct_1(X1) != iProver_top
% 59.45/8.01      | v2_funct_1(X1) = iProver_top
% 59.45/8.01      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
% 59.45/8.01      inference(renaming,[status(thm)],[c_8904]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_10668,plain,
% 59.45/8.01      ( sK0 = k1_xboole_0
% 59.45/8.01      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 59.45/8.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 59.45/8.01      | v1_funct_1(sK3) != iProver_top
% 59.45/8.01      | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
% 59.45/8.01      | v2_funct_1(sK3) = iProver_top ),
% 59.45/8.01      inference(superposition,[status(thm)],[c_10660,c_8905]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_52,negated_conjecture,
% 59.45/8.01      ( k1_xboole_0 != sK0 ),
% 59.45/8.01      inference(cnf_transformation,[],[f153]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_3,plain,
% 59.45/8.01      ( r1_tarski(X0,X0) ),
% 59.45/8.01      inference(cnf_transformation,[],[f170]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_197,plain,
% 59.45/8.01      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 59.45/8.01      inference(instantiation,[status(thm)],[c_3]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_201,plain,
% 59.45/8.01      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 59.45/8.01      | k1_xboole_0 = k1_xboole_0 ),
% 59.45/8.01      inference(instantiation,[status(thm)],[c_1]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_1633,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_2860,plain,
% 59.45/8.01      ( sK0 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK0 ),
% 59.45/8.01      inference(instantiation,[status(thm)],[c_1633]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_2861,plain,
% 59.45/8.01      ( sK0 != k1_xboole_0
% 59.45/8.01      | k1_xboole_0 = sK0
% 59.45/8.01      | k1_xboole_0 != k1_xboole_0 ),
% 59.45/8.01      inference(instantiation,[status(thm)],[c_2860]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_10897,plain,
% 59.45/8.01      ( v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
% 59.45/8.01      | v2_funct_1(sK3) = iProver_top ),
% 59.45/8.01      inference(global_propositional_subsumption,
% 59.45/8.01                [status(thm)],
% 59.45/8.01                [c_10668,c_65,c_66,c_67,c_52,c_197,c_201,c_2861]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_18171,plain,
% 59.45/8.01      ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 59.45/8.01      | v2_funct_1(sK3) = iProver_top ),
% 59.45/8.01      inference(demodulation,[status(thm)],[c_18081,c_10897]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_26,plain,
% 59.45/8.01      ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
% 59.45/8.01      | ~ v1_funct_1(X1)
% 59.45/8.01      | ~ v1_funct_1(X0)
% 59.45/8.01      | ~ v1_relat_1(X1)
% 59.45/8.01      | ~ v1_relat_1(X0)
% 59.45/8.01      | k1_relat_1(k5_relat_1(X0,X1)) != k1_relat_1(X0) ),
% 59.45/8.01      inference(cnf_transformation,[],[f119]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_2718,plain,
% 59.45/8.01      ( k1_relat_1(k5_relat_1(X0,X1)) != k1_relat_1(X0)
% 59.45/8.01      | r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) = iProver_top
% 59.45/8.01      | v1_funct_1(X0) != iProver_top
% 59.45/8.01      | v1_funct_1(X1) != iProver_top
% 59.45/8.01      | v1_relat_1(X0) != iProver_top
% 59.45/8.01      | v1_relat_1(X1) != iProver_top ),
% 59.45/8.01      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_18184,plain,
% 59.45/8.01      ( k1_relat_1(k6_partfun1(sK0)) != k1_relat_1(sK2)
% 59.45/8.01      | r1_tarski(k2_relat_1(sK2),k1_relat_1(sK3)) = iProver_top
% 59.45/8.01      | v1_funct_1(sK3) != iProver_top
% 59.45/8.01      | v1_funct_1(sK2) != iProver_top
% 59.45/8.01      | v1_relat_1(sK3) != iProver_top
% 59.45/8.01      | v1_relat_1(sK2) != iProver_top ),
% 59.45/8.01      inference(superposition,[status(thm)],[c_18081,c_2718]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_28,plain,
% 59.45/8.01      ( ~ v1_funct_1(X0)
% 59.45/8.01      | ~ v2_funct_1(X0)
% 59.45/8.01      | ~ v1_relat_1(X0)
% 59.45/8.01      | k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ),
% 59.45/8.01      inference(cnf_transformation,[],[f120]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_2716,plain,
% 59.45/8.01      ( k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
% 59.45/8.01      | v1_funct_1(X0) != iProver_top
% 59.45/8.01      | v2_funct_1(X0) != iProver_top
% 59.45/8.01      | v1_relat_1(X0) != iProver_top ),
% 59.45/8.01      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_7642,plain,
% 59.45/8.01      ( k1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) = k1_relat_1(sK2)
% 59.45/8.01      | v2_funct_1(sK2) != iProver_top
% 59.45/8.01      | v1_relat_1(sK2) != iProver_top ),
% 59.45/8.01      inference(superposition,[status(thm)],[c_2692,c_2716]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_49,plain,
% 59.45/8.01      ( ~ v1_funct_2(X0,X1,X2)
% 59.45/8.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 59.45/8.01      | ~ v1_funct_1(X0)
% 59.45/8.01      | ~ v2_funct_1(X0)
% 59.45/8.01      | k2_relset_1(X1,X2,X0) != X2
% 59.45/8.01      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 59.45/8.01      | k1_xboole_0 = X2 ),
% 59.45/8.01      inference(cnf_transformation,[],[f142]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_2700,plain,
% 59.45/8.01      ( k2_relset_1(X0,X1,X2) != X1
% 59.45/8.01      | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
% 59.45/8.01      | k1_xboole_0 = X1
% 59.45/8.01      | v1_funct_2(X2,X0,X1) != iProver_top
% 59.45/8.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 59.45/8.01      | v1_funct_1(X2) != iProver_top
% 59.45/8.01      | v2_funct_1(X2) != iProver_top ),
% 59.45/8.01      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_4358,plain,
% 59.45/8.01      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
% 59.45/8.01      | sK1 = k1_xboole_0
% 59.45/8.01      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 59.45/8.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 59.45/8.01      | v1_funct_1(sK2) != iProver_top
% 59.45/8.01      | v2_funct_1(sK2) != iProver_top ),
% 59.45/8.01      inference(superposition,[status(thm)],[c_55,c_2700]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_2817,plain,
% 59.45/8.01      ( ~ v1_funct_2(X0,X1,sK1)
% 59.45/8.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 59.45/8.01      | ~ v1_funct_1(X0)
% 59.45/8.01      | ~ v2_funct_1(X0)
% 59.45/8.01      | k2_relset_1(X1,sK1,X0) != sK1
% 59.45/8.01      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 59.45/8.01      | k1_xboole_0 = sK1 ),
% 59.45/8.01      inference(instantiation,[status(thm)],[c_49]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_2999,plain,
% 59.45/8.01      ( ~ v1_funct_2(sK2,X0,sK1)
% 59.45/8.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
% 59.45/8.01      | ~ v1_funct_1(sK2)
% 59.45/8.01      | ~ v2_funct_1(sK2)
% 59.45/8.01      | k2_relset_1(X0,sK1,sK2) != sK1
% 59.45/8.01      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
% 59.45/8.01      | k1_xboole_0 = sK1 ),
% 59.45/8.01      inference(instantiation,[status(thm)],[c_2817]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_3112,plain,
% 59.45/8.01      ( ~ v1_funct_2(sK2,sK0,sK1)
% 59.45/8.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 59.45/8.01      | ~ v1_funct_1(sK2)
% 59.45/8.01      | ~ v2_funct_1(sK2)
% 59.45/8.01      | k2_relset_1(sK0,sK1,sK2) != sK1
% 59.45/8.01      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
% 59.45/8.01      | k1_xboole_0 = sK1 ),
% 59.45/8.01      inference(instantiation,[status(thm)],[c_2999]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_4522,plain,
% 59.45/8.01      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
% 59.45/8.01      inference(global_propositional_subsumption,
% 59.45/8.01                [status(thm)],
% 59.45/8.01                [c_4358,c_61,c_60,c_59,c_55,c_53,c_51,c_3112]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_7643,plain,
% 59.45/8.01      ( k1_relat_1(k6_partfun1(sK0)) = k1_relat_1(sK2)
% 59.45/8.01      | v2_funct_1(sK2) != iProver_top
% 59.45/8.01      | v1_relat_1(sK2) != iProver_top ),
% 59.45/8.01      inference(light_normalisation,[status(thm)],[c_7642,c_4522]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_7644,plain,
% 59.45/8.01      ( k1_relat_1(sK2) = sK0
% 59.45/8.01      | v2_funct_1(sK2) != iProver_top
% 59.45/8.01      | v1_relat_1(sK2) != iProver_top ),
% 59.45/8.01      inference(demodulation,[status(thm)],[c_7643,c_19]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_8051,plain,
% 59.45/8.01      ( k1_relat_1(sK2) = sK0 | v1_relat_1(sK2) != iProver_top ),
% 59.45/8.01      inference(global_propositional_subsumption,
% 59.45/8.01                [status(thm)],
% 59.45/8.01                [c_7644,c_69]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_11609,plain,
% 59.45/8.01      ( k1_relat_1(sK2) = sK0 ),
% 59.45/8.01      inference(superposition,[status(thm)],[c_11336,c_8051]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_18185,plain,
% 59.45/8.01      ( k1_relat_1(k6_partfun1(sK0)) != sK0
% 59.45/8.01      | r1_tarski(sK1,k1_relat_1(sK3)) = iProver_top
% 59.45/8.01      | v1_funct_1(sK3) != iProver_top
% 59.45/8.01      | v1_funct_1(sK2) != iProver_top
% 59.45/8.01      | v1_relat_1(sK3) != iProver_top
% 59.45/8.01      | v1_relat_1(sK2) != iProver_top ),
% 59.45/8.01      inference(light_normalisation,
% 59.45/8.01                [status(thm)],
% 59.45/8.01                [c_18184,c_11609,c_11610]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_18186,plain,
% 59.45/8.01      ( sK0 != sK0
% 59.45/8.01      | r1_tarski(sK1,k1_relat_1(sK3)) = iProver_top
% 59.45/8.01      | v1_funct_1(sK3) != iProver_top
% 59.45/8.01      | v1_funct_1(sK2) != iProver_top
% 59.45/8.01      | v1_relat_1(sK3) != iProver_top
% 59.45/8.01      | v1_relat_1(sK2) != iProver_top ),
% 59.45/8.01      inference(demodulation,[status(thm)],[c_18185,c_19]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_18187,plain,
% 59.45/8.01      ( r1_tarski(sK1,k1_relat_1(sK3)) = iProver_top
% 59.45/8.01      | v1_funct_1(sK3) != iProver_top
% 59.45/8.01      | v1_funct_1(sK2) != iProver_top
% 59.45/8.01      | v1_relat_1(sK3) != iProver_top
% 59.45/8.01      | v1_relat_1(sK2) != iProver_top ),
% 59.45/8.01      inference(equality_resolution_simp,[status(thm)],[c_18186]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_176458,plain,
% 59.45/8.01      ( k2_funct_1(sK3) = sK2 ),
% 59.45/8.01      inference(global_propositional_subsumption,
% 59.45/8.01                [status(thm)],
% 59.45/8.01                [c_18189,c_62,c_65,c_6323,c_10784,c_11309,c_11336,
% 59.45/8.01                 c_18171,c_18187]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_18931,plain,
% 59.45/8.01      ( v2_funct_1(sK3) = iProver_top ),
% 59.45/8.01      inference(global_propositional_subsumption,
% 59.45/8.01                [status(thm)],
% 59.45/8.01                [c_18171,c_10784]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_2695,plain,
% 59.45/8.01      ( v1_funct_1(sK3) = iProver_top ),
% 59.45/8.01      inference(predicate_to_equality,[status(thm)],[c_58]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_23,plain,
% 59.45/8.01      ( ~ v1_funct_1(X0)
% 59.45/8.01      | ~ v2_funct_1(X0)
% 59.45/8.01      | ~ v1_relat_1(X0)
% 59.45/8.01      | k2_funct_1(X0) = k4_relat_1(X0) ),
% 59.45/8.01      inference(cnf_transformation,[],[f116]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_2721,plain,
% 59.45/8.01      ( k2_funct_1(X0) = k4_relat_1(X0)
% 59.45/8.01      | v1_funct_1(X0) != iProver_top
% 59.45/8.01      | v2_funct_1(X0) != iProver_top
% 59.45/8.01      | v1_relat_1(X0) != iProver_top ),
% 59.45/8.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_6847,plain,
% 59.45/8.01      ( k2_funct_1(sK3) = k4_relat_1(sK3)
% 59.45/8.01      | v2_funct_1(sK3) != iProver_top
% 59.45/8.01      | v1_relat_1(sK3) != iProver_top ),
% 59.45/8.01      inference(superposition,[status(thm)],[c_2695,c_2721]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_18939,plain,
% 59.45/8.01      ( k2_funct_1(sK3) = k4_relat_1(sK3)
% 59.45/8.01      | v1_relat_1(sK3) != iProver_top ),
% 59.45/8.01      inference(superposition,[status(thm)],[c_18931,c_6847]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_18944,plain,
% 59.45/8.01      ( k2_funct_1(sK3) = k4_relat_1(sK3) ),
% 59.45/8.01      inference(global_propositional_subsumption,
% 59.45/8.01                [status(thm)],
% 59.45/8.01                [c_18939,c_6847,c_10784,c_11309,c_18171]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_176460,plain,
% 59.45/8.01      ( k4_relat_1(sK3) = sK2 ),
% 59.45/8.01      inference(demodulation,[status(thm)],[c_176458,c_18944]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_11,plain,
% 59.45/8.01      ( ~ v1_relat_1(X0) | k4_relat_1(k4_relat_1(X0)) = X0 ),
% 59.45/8.01      inference(cnf_transformation,[],[f104]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_2730,plain,
% 59.45/8.01      ( k4_relat_1(k4_relat_1(X0)) = X0 | v1_relat_1(X0) != iProver_top ),
% 59.45/8.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_11571,plain,
% 59.45/8.01      ( k4_relat_1(k4_relat_1(sK3)) = sK3 ),
% 59.45/8.01      inference(superposition,[status(thm)],[c_11309,c_2730]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_177188,plain,
% 59.45/8.01      ( k4_relat_1(sK2) = sK3 ),
% 59.45/8.01      inference(demodulation,[status(thm)],[c_176460,c_11571]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_6848,plain,
% 59.45/8.01      ( k2_funct_1(sK2) = k4_relat_1(sK2)
% 59.45/8.01      | v2_funct_1(sK2) != iProver_top
% 59.45/8.01      | v1_relat_1(sK2) != iProver_top ),
% 59.45/8.01      inference(superposition,[status(thm)],[c_2692,c_2721]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_7006,plain,
% 59.45/8.01      ( k2_funct_1(sK2) = k4_relat_1(sK2)
% 59.45/8.01      | v1_relat_1(sK2) != iProver_top ),
% 59.45/8.01      inference(global_propositional_subsumption,
% 59.45/8.01                [status(thm)],
% 59.45/8.01                [c_6848,c_69]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_11611,plain,
% 59.45/8.01      ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 59.45/8.01      inference(superposition,[status(thm)],[c_11336,c_7006]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_50,negated_conjecture,
% 59.45/8.01      ( k2_funct_1(sK2) != sK3 ),
% 59.45/8.01      inference(cnf_transformation,[],[f155]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(c_11674,plain,
% 59.45/8.01      ( k4_relat_1(sK2) != sK3 ),
% 59.45/8.01      inference(demodulation,[status(thm)],[c_11611,c_50]) ).
% 59.45/8.01  
% 59.45/8.01  cnf(contradiction,plain,
% 59.45/8.01      ( $false ),
% 59.45/8.01      inference(minisat,[status(thm)],[c_177188,c_11674]) ).
% 59.45/8.01  
% 59.45/8.01  
% 59.45/8.01  % SZS output end CNFRefutation for theBenchmark.p
% 59.45/8.01  
% 59.45/8.01  ------                               Statistics
% 59.45/8.01  
% 59.45/8.01  ------ General
% 59.45/8.01  
% 59.45/8.01  abstr_ref_over_cycles:                  0
% 59.45/8.01  abstr_ref_under_cycles:                 0
% 59.45/8.01  gc_basic_clause_elim:                   0
% 59.45/8.01  forced_gc_time:                         0
% 59.45/8.01  parsing_time:                           0.012
% 59.45/8.01  unif_index_cands_time:                  0.
% 59.45/8.01  unif_index_add_time:                    0.
% 59.45/8.01  orderings_time:                         0.
% 59.45/8.01  out_proof_time:                         0.043
% 59.45/8.01  total_time:                             7.216
% 59.45/8.01  num_of_symbols:                         59
% 59.45/8.01  num_of_terms:                           206347
% 59.45/8.01  
% 59.45/8.01  ------ Preprocessing
% 59.45/8.01  
% 59.45/8.01  num_of_splits:                          0
% 59.45/8.01  num_of_split_atoms:                     0
% 59.45/8.01  num_of_reused_defs:                     0
% 59.45/8.01  num_eq_ax_congr_red:                    7
% 59.45/8.01  num_of_sem_filtered_clauses:            1
% 59.45/8.01  num_of_subtypes:                        0
% 59.45/8.01  monotx_restored_types:                  0
% 59.45/8.01  sat_num_of_epr_types:                   0
% 59.45/8.01  sat_num_of_non_cyclic_types:            0
% 59.45/8.01  sat_guarded_non_collapsed_types:        0
% 59.45/8.01  num_pure_diseq_elim:                    0
% 59.45/8.01  simp_replaced_by:                       0
% 59.45/8.01  res_preprocessed:                       274
% 59.45/8.01  prep_upred:                             0
% 59.45/8.01  prep_unflattend:                        38
% 59.45/8.01  smt_new_axioms:                         0
% 59.45/8.01  pred_elim_cands:                        7
% 59.45/8.01  pred_elim:                              3
% 59.45/8.01  pred_elim_cl:                           5
% 59.45/8.01  pred_elim_cycles:                       6
% 59.45/8.01  merged_defs:                            8
% 59.45/8.01  merged_defs_ncl:                        0
% 59.45/8.01  bin_hyper_res:                          9
% 59.45/8.01  prep_cycles:                            4
% 59.45/8.01  pred_elim_time:                         0.015
% 59.45/8.01  splitting_time:                         0.
% 59.45/8.01  sem_filter_time:                        0.
% 59.45/8.01  monotx_time:                            0.001
% 59.45/8.01  subtype_inf_time:                       0.
% 59.45/8.01  
% 59.45/8.01  ------ Problem properties
% 59.45/8.01  
% 59.45/8.01  clauses:                                56
% 59.45/8.01  conjectures:                            12
% 59.45/8.01  epr:                                    10
% 59.45/8.01  horn:                                   52
% 59.45/8.01  ground:                                 12
% 59.45/8.01  unary:                                  21
% 59.45/8.01  binary:                                 12
% 59.45/8.01  lits:                                   179
% 59.45/8.01  lits_eq:                                40
% 59.45/8.01  fd_pure:                                0
% 59.45/8.01  fd_pseudo:                              0
% 59.45/8.01  fd_cond:                                4
% 59.45/8.01  fd_pseudo_cond:                         4
% 59.45/8.01  ac_symbols:                             0
% 59.45/8.01  
% 59.45/8.01  ------ Propositional Solver
% 59.45/8.01  
% 59.45/8.01  prop_solver_calls:                      81
% 59.45/8.01  prop_fast_solver_calls:                 8790
% 59.45/8.01  smt_solver_calls:                       0
% 59.45/8.01  smt_fast_solver_calls:                  0
% 59.45/8.01  prop_num_of_clauses:                    80980
% 59.45/8.01  prop_preprocess_simplified:             134556
% 59.45/8.01  prop_fo_subsumed:                       1759
% 59.45/8.01  prop_solver_time:                       0.
% 59.45/8.01  smt_solver_time:                        0.
% 59.45/8.01  smt_fast_solver_time:                   0.
% 59.45/8.01  prop_fast_solver_time:                  0.
% 59.45/8.01  prop_unsat_core_time:                   0.012
% 59.45/8.01  
% 59.45/8.01  ------ QBF
% 59.45/8.01  
% 59.45/8.01  qbf_q_res:                              0
% 59.45/8.01  qbf_num_tautologies:                    0
% 59.45/8.01  qbf_prep_cycles:                        0
% 59.45/8.01  
% 59.45/8.01  ------ BMC1
% 59.45/8.01  
% 59.45/8.01  bmc1_current_bound:                     -1
% 59.45/8.01  bmc1_last_solved_bound:                 -1
% 59.45/8.01  bmc1_unsat_core_size:                   -1
% 59.45/8.01  bmc1_unsat_core_parents_size:           -1
% 59.45/8.01  bmc1_merge_next_fun:                    0
% 59.45/8.01  bmc1_unsat_core_clauses_time:           0.
% 59.45/8.01  
% 59.45/8.01  ------ Instantiation
% 59.45/8.01  
% 59.45/8.01  inst_num_of_clauses:                    14293
% 59.45/8.01  inst_num_in_passive:                    7044
% 59.45/8.01  inst_num_in_active:                     7642
% 59.45/8.01  inst_num_in_unprocessed:                2286
% 59.45/8.01  inst_num_of_loops:                      8319
% 59.45/8.01  inst_num_of_learning_restarts:          1
% 59.45/8.01  inst_num_moves_active_passive:          674
% 59.45/8.01  inst_lit_activity:                      0
% 59.45/8.01  inst_lit_activity_moves:                4
% 59.45/8.01  inst_num_tautologies:                   0
% 59.45/8.01  inst_num_prop_implied:                  0
% 59.45/8.01  inst_num_existing_simplified:           0
% 59.45/8.01  inst_num_eq_res_simplified:             0
% 59.45/8.01  inst_num_child_elim:                    0
% 59.45/8.01  inst_num_of_dismatching_blockings:      12087
% 59.45/8.01  inst_num_of_non_proper_insts:           23341
% 59.45/8.01  inst_num_of_duplicates:                 0
% 59.45/8.01  inst_inst_num_from_inst_to_res:         0
% 59.45/8.01  inst_dismatching_checking_time:         0.
% 59.45/8.01  
% 59.45/8.01  ------ Resolution
% 59.45/8.01  
% 59.45/8.01  res_num_of_clauses:                     78
% 59.45/8.01  res_num_in_passive:                     78
% 59.45/8.01  res_num_in_active:                      0
% 59.45/8.01  res_num_of_loops:                       278
% 59.45/8.01  res_forward_subset_subsumed:            1360
% 59.45/8.01  res_backward_subset_subsumed:           0
% 59.45/8.01  res_forward_subsumed:                   0
% 59.45/8.01  res_backward_subsumed:                  0
% 59.45/8.01  res_forward_subsumption_resolution:     4
% 59.45/8.01  res_backward_subsumption_resolution:    0
% 59.45/8.01  res_clause_to_clause_subsumption:       49423
% 59.45/8.01  res_orphan_elimination:                 0
% 59.45/8.01  res_tautology_del:                      1099
% 59.45/8.01  res_num_eq_res_simplified:              0
% 59.45/8.01  res_num_sel_changes:                    0
% 59.45/8.01  res_moves_from_active_to_pass:          0
% 59.45/8.01  
% 59.45/8.01  ------ Superposition
% 59.45/8.01  
% 59.45/8.01  sup_time_total:                         0.
% 59.45/8.01  sup_time_generating:                    0.
% 59.45/8.01  sup_time_sim_full:                      0.
% 59.45/8.01  sup_time_sim_immed:                     0.
% 59.45/8.01  
% 59.45/8.01  sup_num_of_clauses:                     11688
% 59.45/8.01  sup_num_in_active:                      1378
% 59.45/8.01  sup_num_in_passive:                     10310
% 59.45/8.01  sup_num_of_loops:                       1662
% 59.45/8.01  sup_fw_superposition:                   4978
% 59.45/8.01  sup_bw_superposition:                   9964
% 59.45/8.01  sup_immediate_simplified:               6917
% 59.45/8.01  sup_given_eliminated:                   1
% 59.45/8.01  comparisons_done:                       0
% 59.45/8.01  comparisons_avoided:                    0
% 59.45/8.01  
% 59.45/8.01  ------ Simplifications
% 59.45/8.01  
% 59.45/8.01  
% 59.45/8.01  sim_fw_subset_subsumed:                 91
% 59.45/8.01  sim_bw_subset_subsumed:                 374
% 59.45/8.01  sim_fw_subsumed:                        281
% 59.45/8.01  sim_bw_subsumed:                        9
% 59.45/8.01  sim_fw_subsumption_res:                 0
% 59.45/8.01  sim_bw_subsumption_res:                 0
% 59.45/8.01  sim_tautology_del:                      67
% 59.45/8.01  sim_eq_tautology_del:                   825
% 59.45/8.01  sim_eq_res_simp:                        84
% 59.45/8.01  sim_fw_demodulated:                     1036
% 59.45/8.01  sim_bw_demodulated:                     197
% 59.45/8.01  sim_light_normalised:                   5771
% 59.45/8.01  sim_joinable_taut:                      0
% 59.45/8.01  sim_joinable_simp:                      0
% 59.45/8.01  sim_ac_normalised:                      0
% 59.45/8.01  sim_smt_subsumption:                    0
% 59.45/8.01  
%------------------------------------------------------------------------------
