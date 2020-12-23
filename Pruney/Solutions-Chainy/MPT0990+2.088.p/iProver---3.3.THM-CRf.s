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
% DateTime   : Thu Dec  3 12:03:15 EST 2020

% Result     : Theorem 7.77s
% Output     : CNFRefutation 7.77s
% Verified   : 
% Statistics : Number of formulae       :  266 (2934 expanded)
%              Number of clauses        :  177 ( 794 expanded)
%              Number of leaves         :   23 ( 773 expanded)
%              Depth                    :   29
%              Number of atoms          :  977 (25049 expanded)
%              Number of equality atoms :  540 (9238 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
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

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

fof(f46,plain,(
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
    inference(ennf_transformation,[],[f20])).

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
    inference(flattening,[],[f46])).

fof(f50,plain,(
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

fof(f49,plain,
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

fof(f51,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f47,f50,f49])).

fof(f86,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f51])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f16,axiom,(
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

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f88,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f51])).

fof(f81,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f82,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f83,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f51])).

fof(f84,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f85,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f2,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f15,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f94,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f53,f73])).

fof(f6,axiom,(
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

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X1)
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f89,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f34])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f12,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f97,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f69,f73])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f36])).

fof(f71,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f70,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f87,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f51])).

fof(f17,axiom,(
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

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f77,plain,(
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
    inference(cnf_transformation,[],[f43])).

fof(f90,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f51])).

fof(f54,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f93,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f54,f73])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f31,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f63,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f18,axiom,(
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

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f44])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f91,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f51])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f55,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f95,plain,(
    ! [X0] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f55,f73])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f38])).

fof(f72,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f57,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f56,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f96,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f56,f73])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f29,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f61,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f92,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1260,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1272,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2298,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1260,c_1272])).

cnf(c_21,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_32,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_433,plain,
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
    inference(resolution_lifted,[status(thm)],[c_21,c_32])).

cnf(c_434,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0
    | k6_partfun1(sK0) != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_433])).

cnf(c_521,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_434])).

cnf(c_1252,plain,
    ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X0,sK0,X2) = sK0
    | v1_funct_2(X2,X0,sK0) != iProver_top
    | v1_funct_2(X1,sK0,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_521])).

cnf(c_1823,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1252])).

cnf(c_39,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_40,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_38,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_41,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_37,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_42,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_43,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_35,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_44,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_45,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_2066,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1823,c_40,c_41,c_42,c_43,c_44,c_45])).

cnf(c_2301,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_2298,c_2066])).

cnf(c_2,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_8,plain,
    ( v2_funct_1(X0)
    | ~ v2_funct_1(k5_relat_1(X0,X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_relat_1(X1) != k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1278,plain,
    ( k1_relat_1(X0) != k2_relat_1(X1)
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k5_relat_1(X1,X0)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4992,plain,
    ( k2_relat_1(X0) != X1
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k5_relat_1(X0,k6_partfun1(X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k6_partfun1(X1)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k6_partfun1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_1278])).

cnf(c_5727,plain,
    ( sK0 != X0
    | v2_funct_1(k5_relat_1(sK3,k6_partfun1(X0))) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_funct_1(k6_partfun1(X0)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(k6_partfun1(X0)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2301,c_4992])).

cnf(c_31,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_47,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_16,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_420,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_32])).

cnf(c_421,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_420])).

cnf(c_17,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_429,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_421,c_17])).

cnf(c_1253,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_429])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1369,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_2059,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1253,c_39,c_37,c_36,c_34,c_429,c_1369])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v1_funct_1(k1_partfun1(X4,X5,X1,X2,X3,X0)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1269,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(k1_partfun1(X4,X5,X1,X2,X3,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4926,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(k6_partfun1(sK0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2059,c_1269])).

cnf(c_33,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v2_funct_1(X0)
    | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X4,X1,X3) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1266,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k1_xboole_0 = X3
    | v1_funct_2(X4,X1,X3) != iProver_top
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v2_funct_1(X4) = iProver_top
    | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_6713,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_33,c_1266])).

cnf(c_6861,plain,
    ( v1_funct_1(X1) != iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | k1_xboole_0 = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6713,c_40,c_41,c_42])).

cnf(c_6862,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_6861])).

cnf(c_6865,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2059,c_6862])).

cnf(c_30,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_712,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_743,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_712])).

cnf(c_713,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1367,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_713])).

cnf(c_1368,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1367])).

cnf(c_6903,plain,
    ( v2_funct_1(sK3) = iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6865,c_43,c_44,c_45,c_30,c_743,c_1368])).

cnf(c_6904,plain,
    ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_6903])).

cnf(c_1,plain,
    ( k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1261,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_12,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1274,plain,
    ( k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3545,plain,
    ( k1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) = k1_relat_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1261,c_1274])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1262,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v2_funct_1(X2) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3166,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_33,c_1262])).

cnf(c_29,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1332,plain,
    ( ~ v1_funct_2(X0,X1,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,sK1,X0) != sK1
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_1440,plain,
    ( ~ v1_funct_2(sK2,X0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0,sK1,sK2) != sK1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1332])).

cnf(c_1659,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(sK0,sK1,sK2) != sK1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1440])).

cnf(c_3270,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3166,c_39,c_38,c_37,c_33,c_31,c_29,c_1659])).

cnf(c_3546,plain,
    ( k1_relat_1(k6_partfun1(sK0)) = k1_relat_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3545,c_3270])).

cnf(c_3547,plain,
    ( k1_relat_1(sK2) = sK0
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3546,c_2])).

cnf(c_1257,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1273,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2254,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1257,c_1273])).

cnf(c_3550,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3547,c_40,c_2254])).

cnf(c_4993,plain,
    ( k2_relat_1(X0) != sK0
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k5_relat_1(X0,sK2)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3550,c_1278])).

cnf(c_15564,plain,
    ( v1_relat_1(X0) != iProver_top
    | k2_relat_1(X0) != sK0
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k5_relat_1(X0,sK2)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4993,c_40,c_2254])).

cnf(c_15565,plain,
    ( k2_relat_1(X0) != sK0
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k5_relat_1(X0,sK2)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_15564])).

cnf(c_15570,plain,
    ( sK0 != X0
    | v2_funct_1(k5_relat_1(k6_partfun1(X0),sK2)) != iProver_top
    | v2_funct_1(k6_partfun1(X0)) = iProver_top
    | v1_funct_1(k6_partfun1(X0)) != iProver_top
    | v1_relat_1(k6_partfun1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_15565])).

cnf(c_1271,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2252,plain,
    ( v1_relat_1(k6_partfun1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1271,c_1273])).

cnf(c_15581,plain,
    ( v1_funct_1(k6_partfun1(X0)) != iProver_top
    | v2_funct_1(k6_partfun1(X0)) = iProver_top
    | v2_funct_1(k5_relat_1(k6_partfun1(X0),sK2)) != iProver_top
    | sK0 != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_15570,c_2252])).

cnf(c_15582,plain,
    ( sK0 != X0
    | v2_funct_1(k5_relat_1(k6_partfun1(X0),sK2)) != iProver_top
    | v2_funct_1(k6_partfun1(X0)) = iProver_top
    | v1_funct_1(k6_partfun1(X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_15581])).

cnf(c_15587,plain,
    ( v2_funct_1(k5_relat_1(k6_partfun1(sK0),sK2)) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) = iProver_top
    | v1_funct_1(k6_partfun1(sK0)) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_15582])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1283,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2832,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(sK2)),sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_2254,c_1283])).

cnf(c_3553,plain,
    ( k5_relat_1(k6_partfun1(sK0),sK2) = sK2 ),
    inference(demodulation,[status(thm)],[c_3550,c_2832])).

cnf(c_15588,plain,
    ( v2_funct_1(k6_partfun1(sK0)) = iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(k6_partfun1(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_15587,c_3553])).

cnf(c_18856,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5727,c_40,c_42,c_43,c_45,c_47,c_4926,c_6904,c_15588])).

cnf(c_18861,plain,
    ( k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) = k1_relat_1(sK3)
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_18856,c_1274])).

cnf(c_3167,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2066,c_1262])).

cnf(c_3369,plain,
    ( v2_funct_1(sK3) != iProver_top
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3167,c_43,c_44,c_45,c_30,c_743,c_1368])).

cnf(c_3370,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | v2_funct_1(sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_3369])).

cnf(c_18865,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    inference(superposition,[status(thm)],[c_18856,c_3370])).

cnf(c_18867,plain,
    ( k1_relat_1(k6_partfun1(sK1)) = k1_relat_1(sK3)
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_18861,c_18865])).

cnf(c_18868,plain,
    ( k1_relat_1(sK3) = sK1
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_18867,c_2])).

cnf(c_2253,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1260,c_1273])).

cnf(c_18932,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_18868,c_43,c_2253])).

cnf(c_2828,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(sK3)),sK3) = sK3 ),
    inference(superposition,[status(thm)],[c_2253,c_1283])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k5_relat_1(k5_relat_1(X2,X1),X0) = k5_relat_1(X2,k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1284,plain,
    ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3783,plain,
    ( k5_relat_1(k6_partfun1(X0),k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(k6_partfun1(X0),X1),X2)
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2252,c_1284])).

cnf(c_9724,plain,
    ( k5_relat_1(k5_relat_1(k6_partfun1(X0),sK3),X1) = k5_relat_1(k6_partfun1(X0),k5_relat_1(sK3,X1))
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2253,c_3783])).

cnf(c_9754,plain,
    ( k5_relat_1(k5_relat_1(k6_partfun1(X0),sK3),sK2) = k5_relat_1(k6_partfun1(X0),k5_relat_1(sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_2254,c_9724])).

cnf(c_9777,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(sK3)),k5_relat_1(sK3,sK2)) = k5_relat_1(sK3,sK2) ),
    inference(superposition,[status(thm)],[c_2828,c_9754])).

cnf(c_18937,plain,
    ( k5_relat_1(k6_partfun1(sK1),k5_relat_1(sK3,sK2)) = k5_relat_1(sK3,sK2) ),
    inference(demodulation,[status(thm)],[c_18932,c_9777])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1268,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4981,plain,
    ( k1_partfun1(X0,X1,sK0,sK1,X2,sK2) = k5_relat_1(X2,sK2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1257,c_1268])).

cnf(c_5098,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK0,sK1,X2,sK2) = k5_relat_1(X2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4981,c_40])).

cnf(c_5099,plain,
    ( k1_partfun1(X0,X1,sK0,sK1,X2,sK2) = k5_relat_1(X2,sK2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_5098])).

cnf(c_5105,plain,
    ( k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) = k5_relat_1(sK3,sK2)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1260,c_5099])).

cnf(c_5123,plain,
    ( k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) = k5_relat_1(sK3,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5105,c_43])).

cnf(c_1270,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_5767,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5123,c_1270])).

cnf(c_7014,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5767,c_40,c_42,c_43,c_45])).

cnf(c_7021,plain,
    ( v1_relat_1(k5_relat_1(sK3,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7014,c_1273])).

cnf(c_1255,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_6,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1280,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3780,plain,
    ( k5_relat_1(k2_funct_1(X0),k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(k2_funct_1(X0),X1),X2)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1280,c_1284])).

cnf(c_10065,plain,
    ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1255,c_3780])).

cnf(c_10323,plain,
    ( v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10065,c_2254])).

cnf(c_10324,plain,
    ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_10323])).

cnf(c_10331,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2254,c_10324])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1263,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v2_funct_1(X2) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3510,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_33,c_1263])).

cnf(c_1331,plain,
    ( ~ v1_funct_2(X0,X1,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,sK1,X0) != sK1
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_1420,plain,
    ( ~ v1_funct_2(sK2,X0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0,sK1,sK2) != sK1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1331])).

cnf(c_1644,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(sK0,sK1,sK2) != sK1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1420])).

cnf(c_4735,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3510,c_39,c_38,c_37,c_33,c_31,c_29,c_1644])).

cnf(c_10336,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k6_partfun1(sK1),X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10331,c_4735])).

cnf(c_10365,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,k5_relat_1(sK3,sK2))) = k5_relat_1(k6_partfun1(sK1),k5_relat_1(sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_7021,c_10336])).

cnf(c_3782,plain,
    ( k5_relat_1(sK2,k5_relat_1(X0,X1)) = k5_relat_1(k5_relat_1(sK2,X0),X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2254,c_1284])).

cnf(c_6024,plain,
    ( k5_relat_1(k5_relat_1(sK2,sK3),X0) = k5_relat_1(sK2,k5_relat_1(sK3,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2253,c_3782])).

cnf(c_4980,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1260,c_1268])).

cnf(c_5067,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4980,c_43])).

cnf(c_5068,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_5067])).

cnf(c_5075,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1257,c_5068])).

cnf(c_5076,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5075,c_2059])).

cnf(c_5149,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5076,c_40])).

cnf(c_6027,plain,
    ( k5_relat_1(sK2,k5_relat_1(sK3,X0)) = k5_relat_1(k6_partfun1(sK0),X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6024,c_5149])).

cnf(c_9623,plain,
    ( k5_relat_1(sK2,k5_relat_1(sK3,sK2)) = k5_relat_1(k6_partfun1(sK0),sK2) ),
    inference(superposition,[status(thm)],[c_2254,c_6027])).

cnf(c_9628,plain,
    ( k5_relat_1(sK2,k5_relat_1(sK3,sK2)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_9623,c_3553])).

cnf(c_10366,plain,
    ( k5_relat_1(k6_partfun1(sK1),k5_relat_1(sK3,sK2)) = k6_partfun1(sK1) ),
    inference(light_normalisation,[status(thm)],[c_10365,c_4735,c_9628])).

cnf(c_18940,plain,
    ( k5_relat_1(sK3,sK2) = k6_partfun1(sK1) ),
    inference(light_normalisation,[status(thm)],[c_18937,c_10366])).

cnf(c_3781,plain,
    ( k5_relat_1(sK3,k5_relat_1(X0,X1)) = k5_relat_1(k5_relat_1(sK3,X0),X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2253,c_1284])).

cnf(c_4781,plain,
    ( k5_relat_1(k5_relat_1(sK3,sK2),X0) = k5_relat_1(sK3,k5_relat_1(sK2,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2254,c_3781])).

cnf(c_5152,plain,
    ( k5_relat_1(sK3,k5_relat_1(sK2,k2_funct_1(X0))) = k5_relat_1(k5_relat_1(sK3,sK2),k2_funct_1(X0))
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1280,c_4781])).

cnf(c_9883,plain,
    ( k5_relat_1(k5_relat_1(sK3,sK2),k2_funct_1(sK2)) = k5_relat_1(sK3,k5_relat_1(sK2,k2_funct_1(sK2)))
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1255,c_5152])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1282,plain,
    ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2829,plain,
    ( k5_relat_1(sK3,k6_partfun1(k2_relat_1(sK3))) = sK3 ),
    inference(superposition,[status(thm)],[c_2253,c_1282])).

cnf(c_2830,plain,
    ( k5_relat_1(sK3,k6_partfun1(sK0)) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_2829,c_2301])).

cnf(c_9887,plain,
    ( k5_relat_1(k5_relat_1(sK3,sK2),k2_funct_1(sK2)) = sK3
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9883,c_2830,c_3270])).

cnf(c_9900,plain,
    ( k5_relat_1(k5_relat_1(sK3,sK2),k2_funct_1(sK2)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9887,c_2254])).

cnf(c_19178,plain,
    ( k5_relat_1(k6_partfun1(sK1),k2_funct_1(sK2)) = sK3 ),
    inference(demodulation,[status(thm)],[c_18940,c_9900])).

cnf(c_2334,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1(X0))),k2_funct_1(X0)) = k2_funct_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1280,c_1283])).

cnf(c_3376,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1(sK2))),k2_funct_1(sK2)) = k2_funct_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1255,c_2334])).

cnf(c_10,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1276,plain,
    ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3201,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1261,c_1276])).

cnf(c_2299,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1257,c_1272])).

cnf(c_2300,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2299,c_33])).

cnf(c_3202,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK1
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3201,c_2300])).

cnf(c_3310,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3202,c_40,c_2254])).

cnf(c_3377,plain,
    ( k5_relat_1(k6_partfun1(sK1),k2_funct_1(sK2)) = k2_funct_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3376,c_3310])).

cnf(c_3465,plain,
    ( k5_relat_1(k6_partfun1(sK1),k2_funct_1(sK2)) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3377,c_2254])).

cnf(c_19380,plain,
    ( k2_funct_1(sK2) = sK3 ),
    inference(demodulation,[status(thm)],[c_19178,c_3465])).

cnf(c_28,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f92])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_19380,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:13:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 7.77/1.51  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.77/1.51  
% 7.77/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.77/1.51  
% 7.77/1.51  ------  iProver source info
% 7.77/1.51  
% 7.77/1.51  git: date: 2020-06-30 10:37:57 +0100
% 7.77/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.77/1.51  git: non_committed_changes: false
% 7.77/1.51  git: last_make_outside_of_git: false
% 7.77/1.51  
% 7.77/1.51  ------ 
% 7.77/1.51  
% 7.77/1.51  ------ Input Options
% 7.77/1.51  
% 7.77/1.51  --out_options                           all
% 7.77/1.51  --tptp_safe_out                         true
% 7.77/1.51  --problem_path                          ""
% 7.77/1.51  --include_path                          ""
% 7.77/1.51  --clausifier                            res/vclausify_rel
% 7.77/1.51  --clausifier_options                    ""
% 7.77/1.51  --stdin                                 false
% 7.77/1.51  --stats_out                             all
% 7.77/1.51  
% 7.77/1.51  ------ General Options
% 7.77/1.51  
% 7.77/1.51  --fof                                   false
% 7.77/1.51  --time_out_real                         305.
% 7.77/1.51  --time_out_virtual                      -1.
% 7.77/1.51  --symbol_type_check                     false
% 7.77/1.51  --clausify_out                          false
% 7.77/1.51  --sig_cnt_out                           false
% 7.77/1.51  --trig_cnt_out                          false
% 7.77/1.51  --trig_cnt_out_tolerance                1.
% 7.77/1.51  --trig_cnt_out_sk_spl                   false
% 7.77/1.51  --abstr_cl_out                          false
% 7.77/1.51  
% 7.77/1.51  ------ Global Options
% 7.77/1.51  
% 7.77/1.51  --schedule                              default
% 7.77/1.51  --add_important_lit                     false
% 7.77/1.51  --prop_solver_per_cl                    1000
% 7.77/1.51  --min_unsat_core                        false
% 7.77/1.51  --soft_assumptions                      false
% 7.77/1.51  --soft_lemma_size                       3
% 7.77/1.51  --prop_impl_unit_size                   0
% 7.77/1.51  --prop_impl_unit                        []
% 7.77/1.51  --share_sel_clauses                     true
% 7.77/1.51  --reset_solvers                         false
% 7.77/1.51  --bc_imp_inh                            [conj_cone]
% 7.77/1.51  --conj_cone_tolerance                   3.
% 7.77/1.51  --extra_neg_conj                        none
% 7.77/1.51  --large_theory_mode                     true
% 7.77/1.51  --prolific_symb_bound                   200
% 7.77/1.51  --lt_threshold                          2000
% 7.77/1.51  --clause_weak_htbl                      true
% 7.77/1.51  --gc_record_bc_elim                     false
% 7.77/1.51  
% 7.77/1.51  ------ Preprocessing Options
% 7.77/1.51  
% 7.77/1.51  --preprocessing_flag                    true
% 7.77/1.51  --time_out_prep_mult                    0.1
% 7.77/1.51  --splitting_mode                        input
% 7.77/1.51  --splitting_grd                         true
% 7.77/1.51  --splitting_cvd                         false
% 7.77/1.51  --splitting_cvd_svl                     false
% 7.77/1.51  --splitting_nvd                         32
% 7.77/1.51  --sub_typing                            true
% 7.77/1.51  --prep_gs_sim                           true
% 7.77/1.51  --prep_unflatten                        true
% 7.77/1.51  --prep_res_sim                          true
% 7.77/1.51  --prep_upred                            true
% 7.77/1.51  --prep_sem_filter                       exhaustive
% 7.77/1.51  --prep_sem_filter_out                   false
% 7.77/1.51  --pred_elim                             true
% 7.77/1.51  --res_sim_input                         true
% 7.77/1.51  --eq_ax_congr_red                       true
% 7.77/1.51  --pure_diseq_elim                       true
% 7.77/1.51  --brand_transform                       false
% 7.77/1.51  --non_eq_to_eq                          false
% 7.77/1.51  --prep_def_merge                        true
% 7.77/1.51  --prep_def_merge_prop_impl              false
% 7.77/1.51  --prep_def_merge_mbd                    true
% 7.77/1.51  --prep_def_merge_tr_red                 false
% 7.77/1.51  --prep_def_merge_tr_cl                  false
% 7.77/1.51  --smt_preprocessing                     true
% 7.77/1.51  --smt_ac_axioms                         fast
% 7.77/1.51  --preprocessed_out                      false
% 7.77/1.51  --preprocessed_stats                    false
% 7.77/1.51  
% 7.77/1.51  ------ Abstraction refinement Options
% 7.77/1.51  
% 7.77/1.51  --abstr_ref                             []
% 7.77/1.51  --abstr_ref_prep                        false
% 7.77/1.51  --abstr_ref_until_sat                   false
% 7.77/1.51  --abstr_ref_sig_restrict                funpre
% 7.77/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.77/1.51  --abstr_ref_under                       []
% 7.77/1.51  
% 7.77/1.51  ------ SAT Options
% 7.77/1.51  
% 7.77/1.51  --sat_mode                              false
% 7.77/1.51  --sat_fm_restart_options                ""
% 7.77/1.51  --sat_gr_def                            false
% 7.77/1.51  --sat_epr_types                         true
% 7.77/1.51  --sat_non_cyclic_types                  false
% 7.77/1.51  --sat_finite_models                     false
% 7.77/1.51  --sat_fm_lemmas                         false
% 7.77/1.51  --sat_fm_prep                           false
% 7.77/1.51  --sat_fm_uc_incr                        true
% 7.77/1.51  --sat_out_model                         small
% 7.77/1.51  --sat_out_clauses                       false
% 7.77/1.51  
% 7.77/1.51  ------ QBF Options
% 7.77/1.51  
% 7.77/1.51  --qbf_mode                              false
% 7.77/1.51  --qbf_elim_univ                         false
% 7.77/1.51  --qbf_dom_inst                          none
% 7.77/1.51  --qbf_dom_pre_inst                      false
% 7.77/1.51  --qbf_sk_in                             false
% 7.77/1.51  --qbf_pred_elim                         true
% 7.77/1.51  --qbf_split                             512
% 7.77/1.51  
% 7.77/1.51  ------ BMC1 Options
% 7.77/1.51  
% 7.77/1.51  --bmc1_incremental                      false
% 7.77/1.51  --bmc1_axioms                           reachable_all
% 7.77/1.51  --bmc1_min_bound                        0
% 7.77/1.51  --bmc1_max_bound                        -1
% 7.77/1.51  --bmc1_max_bound_default                -1
% 7.77/1.51  --bmc1_symbol_reachability              true
% 7.77/1.51  --bmc1_property_lemmas                  false
% 7.77/1.51  --bmc1_k_induction                      false
% 7.77/1.51  --bmc1_non_equiv_states                 false
% 7.77/1.51  --bmc1_deadlock                         false
% 7.77/1.51  --bmc1_ucm                              false
% 7.77/1.51  --bmc1_add_unsat_core                   none
% 7.77/1.51  --bmc1_unsat_core_children              false
% 7.77/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.77/1.51  --bmc1_out_stat                         full
% 7.77/1.51  --bmc1_ground_init                      false
% 7.77/1.51  --bmc1_pre_inst_next_state              false
% 7.77/1.51  --bmc1_pre_inst_state                   false
% 7.77/1.51  --bmc1_pre_inst_reach_state             false
% 7.77/1.51  --bmc1_out_unsat_core                   false
% 7.77/1.51  --bmc1_aig_witness_out                  false
% 7.77/1.51  --bmc1_verbose                          false
% 7.77/1.51  --bmc1_dump_clauses_tptp                false
% 7.77/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.77/1.51  --bmc1_dump_file                        -
% 7.77/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.77/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.77/1.51  --bmc1_ucm_extend_mode                  1
% 7.77/1.51  --bmc1_ucm_init_mode                    2
% 7.77/1.51  --bmc1_ucm_cone_mode                    none
% 7.77/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.77/1.51  --bmc1_ucm_relax_model                  4
% 7.77/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.77/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.77/1.51  --bmc1_ucm_layered_model                none
% 7.77/1.51  --bmc1_ucm_max_lemma_size               10
% 7.77/1.51  
% 7.77/1.51  ------ AIG Options
% 7.77/1.51  
% 7.77/1.51  --aig_mode                              false
% 7.77/1.51  
% 7.77/1.51  ------ Instantiation Options
% 7.77/1.51  
% 7.77/1.51  --instantiation_flag                    true
% 7.77/1.51  --inst_sos_flag                         true
% 7.77/1.51  --inst_sos_phase                        true
% 7.77/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.77/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.77/1.51  --inst_lit_sel_side                     num_symb
% 7.77/1.51  --inst_solver_per_active                1400
% 7.77/1.51  --inst_solver_calls_frac                1.
% 7.77/1.51  --inst_passive_queue_type               priority_queues
% 7.77/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.77/1.51  --inst_passive_queues_freq              [25;2]
% 7.77/1.51  --inst_dismatching                      true
% 7.77/1.51  --inst_eager_unprocessed_to_passive     true
% 7.77/1.51  --inst_prop_sim_given                   true
% 7.77/1.51  --inst_prop_sim_new                     false
% 7.77/1.51  --inst_subs_new                         false
% 7.77/1.51  --inst_eq_res_simp                      false
% 7.77/1.51  --inst_subs_given                       false
% 7.77/1.51  --inst_orphan_elimination               true
% 7.77/1.51  --inst_learning_loop_flag               true
% 7.77/1.51  --inst_learning_start                   3000
% 7.77/1.51  --inst_learning_factor                  2
% 7.77/1.51  --inst_start_prop_sim_after_learn       3
% 7.77/1.51  --inst_sel_renew                        solver
% 7.77/1.51  --inst_lit_activity_flag                true
% 7.77/1.51  --inst_restr_to_given                   false
% 7.77/1.51  --inst_activity_threshold               500
% 7.77/1.51  --inst_out_proof                        true
% 7.77/1.51  
% 7.77/1.51  ------ Resolution Options
% 7.77/1.51  
% 7.77/1.51  --resolution_flag                       true
% 7.77/1.51  --res_lit_sel                           adaptive
% 7.77/1.51  --res_lit_sel_side                      none
% 7.77/1.51  --res_ordering                          kbo
% 7.77/1.51  --res_to_prop_solver                    active
% 7.77/1.51  --res_prop_simpl_new                    false
% 7.77/1.51  --res_prop_simpl_given                  true
% 7.77/1.51  --res_passive_queue_type                priority_queues
% 7.77/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.77/1.51  --res_passive_queues_freq               [15;5]
% 7.77/1.51  --res_forward_subs                      full
% 7.77/1.51  --res_backward_subs                     full
% 7.77/1.51  --res_forward_subs_resolution           true
% 7.77/1.51  --res_backward_subs_resolution          true
% 7.77/1.51  --res_orphan_elimination                true
% 7.77/1.51  --res_time_limit                        2.
% 7.77/1.51  --res_out_proof                         true
% 7.77/1.51  
% 7.77/1.51  ------ Superposition Options
% 7.77/1.51  
% 7.77/1.51  --superposition_flag                    true
% 7.77/1.51  --sup_passive_queue_type                priority_queues
% 7.77/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.77/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.77/1.51  --demod_completeness_check              fast
% 7.77/1.51  --demod_use_ground                      true
% 7.77/1.51  --sup_to_prop_solver                    passive
% 7.77/1.51  --sup_prop_simpl_new                    true
% 7.77/1.51  --sup_prop_simpl_given                  true
% 7.77/1.51  --sup_fun_splitting                     true
% 7.77/1.51  --sup_smt_interval                      50000
% 7.77/1.51  
% 7.77/1.51  ------ Superposition Simplification Setup
% 7.77/1.51  
% 7.77/1.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.77/1.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.77/1.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.77/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.77/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.77/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.77/1.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.77/1.51  --sup_immed_triv                        [TrivRules]
% 7.77/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.77/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.77/1.51  --sup_immed_bw_main                     []
% 7.77/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.77/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.77/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.77/1.51  --sup_input_bw                          []
% 7.77/1.51  
% 7.77/1.51  ------ Combination Options
% 7.77/1.51  
% 7.77/1.51  --comb_res_mult                         3
% 7.77/1.51  --comb_sup_mult                         2
% 7.77/1.51  --comb_inst_mult                        10
% 7.77/1.51  
% 7.77/1.51  ------ Debug Options
% 7.77/1.51  
% 7.77/1.51  --dbg_backtrace                         false
% 7.77/1.51  --dbg_dump_prop_clauses                 false
% 7.77/1.51  --dbg_dump_prop_clauses_file            -
% 7.77/1.51  --dbg_out_stat                          false
% 7.77/1.51  ------ Parsing...
% 7.77/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.77/1.51  
% 7.77/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.77/1.51  
% 7.77/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.77/1.51  
% 7.77/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.77/1.51  ------ Proving...
% 7.77/1.51  ------ Problem Properties 
% 7.77/1.51  
% 7.77/1.51  
% 7.77/1.51  clauses                                 39
% 7.77/1.51  conjectures                             11
% 7.77/1.51  EPR                                     7
% 7.77/1.51  Horn                                    35
% 7.77/1.51  unary                                   14
% 7.77/1.51  binary                                  5
% 7.77/1.51  lits                                    147
% 7.77/1.51  lits eq                                 34
% 7.77/1.51  fd_pure                                 0
% 7.77/1.51  fd_pseudo                               0
% 7.77/1.51  fd_cond                                 4
% 7.77/1.51  fd_pseudo_cond                          0
% 7.77/1.51  AC symbols                              0
% 7.77/1.51  
% 7.77/1.51  ------ Schedule dynamic 5 is on 
% 7.77/1.51  
% 7.77/1.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.77/1.51  
% 7.77/1.51  
% 7.77/1.51  ------ 
% 7.77/1.51  Current options:
% 7.77/1.51  ------ 
% 7.77/1.51  
% 7.77/1.51  ------ Input Options
% 7.77/1.51  
% 7.77/1.51  --out_options                           all
% 7.77/1.51  --tptp_safe_out                         true
% 7.77/1.51  --problem_path                          ""
% 7.77/1.51  --include_path                          ""
% 7.77/1.51  --clausifier                            res/vclausify_rel
% 7.77/1.51  --clausifier_options                    ""
% 7.77/1.51  --stdin                                 false
% 7.77/1.51  --stats_out                             all
% 7.77/1.51  
% 7.77/1.51  ------ General Options
% 7.77/1.51  
% 7.77/1.51  --fof                                   false
% 7.77/1.51  --time_out_real                         305.
% 7.77/1.51  --time_out_virtual                      -1.
% 7.77/1.51  --symbol_type_check                     false
% 7.77/1.51  --clausify_out                          false
% 7.77/1.51  --sig_cnt_out                           false
% 7.77/1.51  --trig_cnt_out                          false
% 7.77/1.51  --trig_cnt_out_tolerance                1.
% 7.77/1.51  --trig_cnt_out_sk_spl                   false
% 7.77/1.51  --abstr_cl_out                          false
% 7.77/1.51  
% 7.77/1.51  ------ Global Options
% 7.77/1.51  
% 7.77/1.51  --schedule                              default
% 7.77/1.51  --add_important_lit                     false
% 7.77/1.51  --prop_solver_per_cl                    1000
% 7.77/1.51  --min_unsat_core                        false
% 7.77/1.51  --soft_assumptions                      false
% 7.77/1.51  --soft_lemma_size                       3
% 7.77/1.51  --prop_impl_unit_size                   0
% 7.77/1.51  --prop_impl_unit                        []
% 7.77/1.51  --share_sel_clauses                     true
% 7.77/1.51  --reset_solvers                         false
% 7.77/1.51  --bc_imp_inh                            [conj_cone]
% 7.77/1.51  --conj_cone_tolerance                   3.
% 7.77/1.51  --extra_neg_conj                        none
% 7.77/1.51  --large_theory_mode                     true
% 7.77/1.51  --prolific_symb_bound                   200
% 7.77/1.51  --lt_threshold                          2000
% 7.77/1.51  --clause_weak_htbl                      true
% 7.77/1.51  --gc_record_bc_elim                     false
% 7.77/1.51  
% 7.77/1.51  ------ Preprocessing Options
% 7.77/1.51  
% 7.77/1.51  --preprocessing_flag                    true
% 7.77/1.51  --time_out_prep_mult                    0.1
% 7.77/1.51  --splitting_mode                        input
% 7.77/1.51  --splitting_grd                         true
% 7.77/1.51  --splitting_cvd                         false
% 7.77/1.51  --splitting_cvd_svl                     false
% 7.77/1.51  --splitting_nvd                         32
% 7.77/1.51  --sub_typing                            true
% 7.77/1.51  --prep_gs_sim                           true
% 7.77/1.51  --prep_unflatten                        true
% 7.77/1.51  --prep_res_sim                          true
% 7.77/1.51  --prep_upred                            true
% 7.77/1.51  --prep_sem_filter                       exhaustive
% 7.77/1.51  --prep_sem_filter_out                   false
% 7.77/1.51  --pred_elim                             true
% 7.77/1.51  --res_sim_input                         true
% 7.77/1.51  --eq_ax_congr_red                       true
% 7.77/1.51  --pure_diseq_elim                       true
% 7.77/1.51  --brand_transform                       false
% 7.77/1.51  --non_eq_to_eq                          false
% 7.77/1.51  --prep_def_merge                        true
% 7.77/1.51  --prep_def_merge_prop_impl              false
% 7.77/1.51  --prep_def_merge_mbd                    true
% 7.77/1.51  --prep_def_merge_tr_red                 false
% 7.77/1.51  --prep_def_merge_tr_cl                  false
% 7.77/1.51  --smt_preprocessing                     true
% 7.77/1.51  --smt_ac_axioms                         fast
% 7.77/1.51  --preprocessed_out                      false
% 7.77/1.51  --preprocessed_stats                    false
% 7.77/1.51  
% 7.77/1.51  ------ Abstraction refinement Options
% 7.77/1.51  
% 7.77/1.51  --abstr_ref                             []
% 7.77/1.51  --abstr_ref_prep                        false
% 7.77/1.51  --abstr_ref_until_sat                   false
% 7.77/1.51  --abstr_ref_sig_restrict                funpre
% 7.77/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.77/1.51  --abstr_ref_under                       []
% 7.77/1.51  
% 7.77/1.51  ------ SAT Options
% 7.77/1.51  
% 7.77/1.51  --sat_mode                              false
% 7.77/1.51  --sat_fm_restart_options                ""
% 7.77/1.51  --sat_gr_def                            false
% 7.77/1.51  --sat_epr_types                         true
% 7.77/1.51  --sat_non_cyclic_types                  false
% 7.77/1.51  --sat_finite_models                     false
% 7.77/1.51  --sat_fm_lemmas                         false
% 7.77/1.51  --sat_fm_prep                           false
% 7.77/1.51  --sat_fm_uc_incr                        true
% 7.77/1.51  --sat_out_model                         small
% 7.77/1.51  --sat_out_clauses                       false
% 7.77/1.51  
% 7.77/1.51  ------ QBF Options
% 7.77/1.51  
% 7.77/1.51  --qbf_mode                              false
% 7.77/1.51  --qbf_elim_univ                         false
% 7.77/1.51  --qbf_dom_inst                          none
% 7.77/1.51  --qbf_dom_pre_inst                      false
% 7.77/1.51  --qbf_sk_in                             false
% 7.77/1.51  --qbf_pred_elim                         true
% 7.77/1.51  --qbf_split                             512
% 7.77/1.51  
% 7.77/1.51  ------ BMC1 Options
% 7.77/1.51  
% 7.77/1.51  --bmc1_incremental                      false
% 7.77/1.51  --bmc1_axioms                           reachable_all
% 7.77/1.51  --bmc1_min_bound                        0
% 7.77/1.51  --bmc1_max_bound                        -1
% 7.77/1.51  --bmc1_max_bound_default                -1
% 7.77/1.51  --bmc1_symbol_reachability              true
% 7.77/1.51  --bmc1_property_lemmas                  false
% 7.77/1.51  --bmc1_k_induction                      false
% 7.77/1.51  --bmc1_non_equiv_states                 false
% 7.77/1.51  --bmc1_deadlock                         false
% 7.77/1.51  --bmc1_ucm                              false
% 7.77/1.51  --bmc1_add_unsat_core                   none
% 7.77/1.51  --bmc1_unsat_core_children              false
% 7.77/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.77/1.51  --bmc1_out_stat                         full
% 7.77/1.51  --bmc1_ground_init                      false
% 7.77/1.51  --bmc1_pre_inst_next_state              false
% 7.77/1.51  --bmc1_pre_inst_state                   false
% 7.77/1.51  --bmc1_pre_inst_reach_state             false
% 7.77/1.51  --bmc1_out_unsat_core                   false
% 7.77/1.51  --bmc1_aig_witness_out                  false
% 7.77/1.51  --bmc1_verbose                          false
% 7.77/1.51  --bmc1_dump_clauses_tptp                false
% 7.77/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.77/1.51  --bmc1_dump_file                        -
% 7.77/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.77/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.77/1.51  --bmc1_ucm_extend_mode                  1
% 7.77/1.51  --bmc1_ucm_init_mode                    2
% 7.77/1.51  --bmc1_ucm_cone_mode                    none
% 7.77/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.77/1.51  --bmc1_ucm_relax_model                  4
% 7.77/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.77/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.77/1.51  --bmc1_ucm_layered_model                none
% 7.77/1.51  --bmc1_ucm_max_lemma_size               10
% 7.77/1.51  
% 7.77/1.51  ------ AIG Options
% 7.77/1.51  
% 7.77/1.51  --aig_mode                              false
% 7.77/1.51  
% 7.77/1.51  ------ Instantiation Options
% 7.77/1.51  
% 7.77/1.51  --instantiation_flag                    true
% 7.77/1.51  --inst_sos_flag                         true
% 7.77/1.51  --inst_sos_phase                        true
% 7.77/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.77/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.77/1.51  --inst_lit_sel_side                     none
% 7.77/1.51  --inst_solver_per_active                1400
% 7.77/1.51  --inst_solver_calls_frac                1.
% 7.77/1.51  --inst_passive_queue_type               priority_queues
% 7.77/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.77/1.51  --inst_passive_queues_freq              [25;2]
% 7.77/1.51  --inst_dismatching                      true
% 7.77/1.51  --inst_eager_unprocessed_to_passive     true
% 7.77/1.51  --inst_prop_sim_given                   true
% 7.77/1.51  --inst_prop_sim_new                     false
% 7.77/1.51  --inst_subs_new                         false
% 7.77/1.51  --inst_eq_res_simp                      false
% 7.77/1.51  --inst_subs_given                       false
% 7.77/1.51  --inst_orphan_elimination               true
% 7.77/1.51  --inst_learning_loop_flag               true
% 7.77/1.51  --inst_learning_start                   3000
% 7.77/1.51  --inst_learning_factor                  2
% 7.77/1.51  --inst_start_prop_sim_after_learn       3
% 7.77/1.51  --inst_sel_renew                        solver
% 7.77/1.51  --inst_lit_activity_flag                true
% 7.77/1.51  --inst_restr_to_given                   false
% 7.77/1.51  --inst_activity_threshold               500
% 7.77/1.51  --inst_out_proof                        true
% 7.77/1.51  
% 7.77/1.51  ------ Resolution Options
% 7.77/1.51  
% 7.77/1.51  --resolution_flag                       false
% 7.77/1.51  --res_lit_sel                           adaptive
% 7.77/1.51  --res_lit_sel_side                      none
% 7.77/1.51  --res_ordering                          kbo
% 7.77/1.51  --res_to_prop_solver                    active
% 7.77/1.51  --res_prop_simpl_new                    false
% 7.77/1.51  --res_prop_simpl_given                  true
% 7.77/1.51  --res_passive_queue_type                priority_queues
% 7.77/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.77/1.51  --res_passive_queues_freq               [15;5]
% 7.77/1.51  --res_forward_subs                      full
% 7.77/1.51  --res_backward_subs                     full
% 7.77/1.51  --res_forward_subs_resolution           true
% 7.77/1.51  --res_backward_subs_resolution          true
% 7.77/1.51  --res_orphan_elimination                true
% 7.77/1.51  --res_time_limit                        2.
% 7.77/1.51  --res_out_proof                         true
% 7.77/1.51  
% 7.77/1.51  ------ Superposition Options
% 7.77/1.51  
% 7.77/1.51  --superposition_flag                    true
% 7.77/1.51  --sup_passive_queue_type                priority_queues
% 7.77/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.77/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.77/1.51  --demod_completeness_check              fast
% 7.77/1.51  --demod_use_ground                      true
% 7.77/1.51  --sup_to_prop_solver                    passive
% 7.77/1.51  --sup_prop_simpl_new                    true
% 7.77/1.51  --sup_prop_simpl_given                  true
% 7.77/1.51  --sup_fun_splitting                     true
% 7.77/1.51  --sup_smt_interval                      50000
% 7.77/1.51  
% 7.77/1.51  ------ Superposition Simplification Setup
% 7.77/1.51  
% 7.77/1.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.77/1.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.77/1.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.77/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.77/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.77/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.77/1.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.77/1.51  --sup_immed_triv                        [TrivRules]
% 7.77/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.77/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.77/1.51  --sup_immed_bw_main                     []
% 7.77/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.77/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.77/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.77/1.51  --sup_input_bw                          []
% 7.77/1.51  
% 7.77/1.51  ------ Combination Options
% 7.77/1.51  
% 7.77/1.51  --comb_res_mult                         3
% 7.77/1.51  --comb_sup_mult                         2
% 7.77/1.51  --comb_inst_mult                        10
% 7.77/1.51  
% 7.77/1.51  ------ Debug Options
% 7.77/1.51  
% 7.77/1.51  --dbg_backtrace                         false
% 7.77/1.51  --dbg_dump_prop_clauses                 false
% 7.77/1.51  --dbg_dump_prop_clauses_file            -
% 7.77/1.51  --dbg_out_stat                          false
% 7.77/1.51  
% 7.77/1.51  
% 7.77/1.51  
% 7.77/1.51  
% 7.77/1.51  ------ Proving...
% 7.77/1.51  
% 7.77/1.51  
% 7.77/1.51  % SZS status Theorem for theBenchmark.p
% 7.77/1.51  
% 7.77/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 7.77/1.51  
% 7.77/1.51  fof(f19,conjecture,(
% 7.77/1.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 7.77/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.51  
% 7.77/1.51  fof(f20,negated_conjecture,(
% 7.77/1.51    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 7.77/1.51    inference(negated_conjecture,[],[f19])).
% 7.77/1.51  
% 7.77/1.51  fof(f46,plain,(
% 7.77/1.51    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 7.77/1.51    inference(ennf_transformation,[],[f20])).
% 7.77/1.51  
% 7.77/1.51  fof(f47,plain,(
% 7.77/1.51    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 7.77/1.51    inference(flattening,[],[f46])).
% 7.77/1.51  
% 7.77/1.51  fof(f50,plain,(
% 7.77/1.51    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 7.77/1.51    introduced(choice_axiom,[])).
% 7.77/1.51  
% 7.77/1.51  fof(f49,plain,(
% 7.77/1.51    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 7.77/1.51    introduced(choice_axiom,[])).
% 7.77/1.51  
% 7.77/1.51  fof(f51,plain,(
% 7.77/1.51    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 7.77/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f47,f50,f49])).
% 7.77/1.51  
% 7.77/1.51  fof(f86,plain,(
% 7.77/1.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 7.77/1.51    inference(cnf_transformation,[],[f51])).
% 7.77/1.51  
% 7.77/1.51  fof(f10,axiom,(
% 7.77/1.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 7.77/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.51  
% 7.77/1.51  fof(f33,plain,(
% 7.77/1.51    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.77/1.51    inference(ennf_transformation,[],[f10])).
% 7.77/1.51  
% 7.77/1.51  fof(f66,plain,(
% 7.77/1.51    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.77/1.51    inference(cnf_transformation,[],[f33])).
% 7.77/1.51  
% 7.77/1.51  fof(f16,axiom,(
% 7.77/1.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 7.77/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.51  
% 7.77/1.51  fof(f40,plain,(
% 7.77/1.51    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 7.77/1.51    inference(ennf_transformation,[],[f16])).
% 7.77/1.51  
% 7.77/1.51  fof(f41,plain,(
% 7.77/1.51    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.77/1.51    inference(flattening,[],[f40])).
% 7.77/1.51  
% 7.77/1.51  fof(f74,plain,(
% 7.77/1.51    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.77/1.51    inference(cnf_transformation,[],[f41])).
% 7.77/1.51  
% 7.77/1.51  fof(f88,plain,(
% 7.77/1.51    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 7.77/1.51    inference(cnf_transformation,[],[f51])).
% 7.77/1.51  
% 7.77/1.51  fof(f81,plain,(
% 7.77/1.51    v1_funct_1(sK2)),
% 7.77/1.51    inference(cnf_transformation,[],[f51])).
% 7.77/1.51  
% 7.77/1.51  fof(f82,plain,(
% 7.77/1.51    v1_funct_2(sK2,sK0,sK1)),
% 7.77/1.51    inference(cnf_transformation,[],[f51])).
% 7.77/1.51  
% 7.77/1.51  fof(f83,plain,(
% 7.77/1.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 7.77/1.51    inference(cnf_transformation,[],[f51])).
% 7.77/1.51  
% 7.77/1.51  fof(f84,plain,(
% 7.77/1.51    v1_funct_1(sK3)),
% 7.77/1.51    inference(cnf_transformation,[],[f51])).
% 7.77/1.51  
% 7.77/1.51  fof(f85,plain,(
% 7.77/1.51    v1_funct_2(sK3,sK1,sK0)),
% 7.77/1.51    inference(cnf_transformation,[],[f51])).
% 7.77/1.51  
% 7.77/1.51  fof(f2,axiom,(
% 7.77/1.51    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 7.77/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.51  
% 7.77/1.51  fof(f53,plain,(
% 7.77/1.51    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 7.77/1.51    inference(cnf_transformation,[],[f2])).
% 7.77/1.51  
% 7.77/1.51  fof(f15,axiom,(
% 7.77/1.51    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 7.77/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.51  
% 7.77/1.51  fof(f73,plain,(
% 7.77/1.51    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 7.77/1.51    inference(cnf_transformation,[],[f15])).
% 7.77/1.51  
% 7.77/1.51  fof(f94,plain,(
% 7.77/1.51    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 7.77/1.51    inference(definition_unfolding,[],[f53,f73])).
% 7.77/1.51  
% 7.77/1.51  fof(f6,axiom,(
% 7.77/1.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 7.77/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.51  
% 7.77/1.51  fof(f26,plain,(
% 7.77/1.51    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.77/1.51    inference(ennf_transformation,[],[f6])).
% 7.77/1.51  
% 7.77/1.51  fof(f27,plain,(
% 7.77/1.51    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.77/1.51    inference(flattening,[],[f26])).
% 7.77/1.51  
% 7.77/1.51  fof(f59,plain,(
% 7.77/1.51    ( ! [X0,X1] : (v2_funct_1(X1) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.77/1.51    inference(cnf_transformation,[],[f27])).
% 7.77/1.51  
% 7.77/1.51  fof(f89,plain,(
% 7.77/1.51    v2_funct_1(sK2)),
% 7.77/1.51    inference(cnf_transformation,[],[f51])).
% 7.77/1.51  
% 7.77/1.51  fof(f11,axiom,(
% 7.77/1.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 7.77/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.51  
% 7.77/1.51  fof(f34,plain,(
% 7.77/1.51    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 7.77/1.51    inference(ennf_transformation,[],[f11])).
% 7.77/1.51  
% 7.77/1.51  fof(f35,plain,(
% 7.77/1.51    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.77/1.51    inference(flattening,[],[f34])).
% 7.77/1.51  
% 7.77/1.51  fof(f48,plain,(
% 7.77/1.51    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.77/1.51    inference(nnf_transformation,[],[f35])).
% 7.77/1.51  
% 7.77/1.51  fof(f67,plain,(
% 7.77/1.51    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.77/1.51    inference(cnf_transformation,[],[f48])).
% 7.77/1.51  
% 7.77/1.51  fof(f12,axiom,(
% 7.77/1.51    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 7.77/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.51  
% 7.77/1.51  fof(f69,plain,(
% 7.77/1.51    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 7.77/1.51    inference(cnf_transformation,[],[f12])).
% 7.77/1.51  
% 7.77/1.51  fof(f97,plain,(
% 7.77/1.51    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 7.77/1.51    inference(definition_unfolding,[],[f69,f73])).
% 7.77/1.51  
% 7.77/1.51  fof(f13,axiom,(
% 7.77/1.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 7.77/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.51  
% 7.77/1.51  fof(f36,plain,(
% 7.77/1.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 7.77/1.51    inference(ennf_transformation,[],[f13])).
% 7.77/1.51  
% 7.77/1.51  fof(f37,plain,(
% 7.77/1.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 7.77/1.51    inference(flattening,[],[f36])).
% 7.77/1.51  
% 7.77/1.51  fof(f71,plain,(
% 7.77/1.51    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 7.77/1.51    inference(cnf_transformation,[],[f37])).
% 7.77/1.51  
% 7.77/1.51  fof(f70,plain,(
% 7.77/1.51    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 7.77/1.51    inference(cnf_transformation,[],[f37])).
% 7.77/1.51  
% 7.77/1.51  fof(f87,plain,(
% 7.77/1.51    k2_relset_1(sK0,sK1,sK2) = sK1),
% 7.77/1.51    inference(cnf_transformation,[],[f51])).
% 7.77/1.51  
% 7.77/1.51  fof(f17,axiom,(
% 7.77/1.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 7.77/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.51  
% 7.77/1.51  fof(f42,plain,(
% 7.77/1.51    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 7.77/1.51    inference(ennf_transformation,[],[f17])).
% 7.77/1.51  
% 7.77/1.51  fof(f43,plain,(
% 7.77/1.51    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 7.77/1.51    inference(flattening,[],[f42])).
% 7.77/1.51  
% 7.77/1.51  fof(f77,plain,(
% 7.77/1.51    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X4) | k1_xboole_0 = X2 | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 7.77/1.51    inference(cnf_transformation,[],[f43])).
% 7.77/1.51  
% 7.77/1.51  fof(f90,plain,(
% 7.77/1.51    k1_xboole_0 != sK0),
% 7.77/1.51    inference(cnf_transformation,[],[f51])).
% 7.77/1.51  
% 7.77/1.51  fof(f54,plain,(
% 7.77/1.51    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 7.77/1.51    inference(cnf_transformation,[],[f2])).
% 7.77/1.51  
% 7.77/1.51  fof(f93,plain,(
% 7.77/1.51    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 7.77/1.51    inference(definition_unfolding,[],[f54,f73])).
% 7.77/1.51  
% 7.77/1.51  fof(f8,axiom,(
% 7.77/1.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 7.77/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.51  
% 7.77/1.51  fof(f30,plain,(
% 7.77/1.51    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.77/1.51    inference(ennf_transformation,[],[f8])).
% 7.77/1.51  
% 7.77/1.51  fof(f31,plain,(
% 7.77/1.51    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.77/1.51    inference(flattening,[],[f30])).
% 7.77/1.51  
% 7.77/1.51  fof(f63,plain,(
% 7.77/1.51    ( ! [X0] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.77/1.51    inference(cnf_transformation,[],[f31])).
% 7.77/1.51  
% 7.77/1.51  fof(f18,axiom,(
% 7.77/1.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 7.77/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.51  
% 7.77/1.51  fof(f44,plain,(
% 7.77/1.51    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 7.77/1.51    inference(ennf_transformation,[],[f18])).
% 7.77/1.51  
% 7.77/1.51  fof(f45,plain,(
% 7.77/1.51    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.77/1.51    inference(flattening,[],[f44])).
% 7.77/1.51  
% 7.77/1.51  fof(f79,plain,(
% 7.77/1.51    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.77/1.51    inference(cnf_transformation,[],[f45])).
% 7.77/1.51  
% 7.77/1.51  fof(f91,plain,(
% 7.77/1.51    k1_xboole_0 != sK1),
% 7.77/1.51    inference(cnf_transformation,[],[f51])).
% 7.77/1.51  
% 7.77/1.51  fof(f9,axiom,(
% 7.77/1.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.77/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.51  
% 7.77/1.51  fof(f32,plain,(
% 7.77/1.51    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.77/1.51    inference(ennf_transformation,[],[f9])).
% 7.77/1.51  
% 7.77/1.51  fof(f65,plain,(
% 7.77/1.51    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.77/1.51    inference(cnf_transformation,[],[f32])).
% 7.77/1.51  
% 7.77/1.51  fof(f3,axiom,(
% 7.77/1.51    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 7.77/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.51  
% 7.77/1.51  fof(f22,plain,(
% 7.77/1.51    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 7.77/1.51    inference(ennf_transformation,[],[f3])).
% 7.77/1.51  
% 7.77/1.51  fof(f55,plain,(
% 7.77/1.51    ( ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 7.77/1.51    inference(cnf_transformation,[],[f22])).
% 7.77/1.51  
% 7.77/1.51  fof(f95,plain,(
% 7.77/1.51    ( ! [X0] : (k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 7.77/1.51    inference(definition_unfolding,[],[f55,f73])).
% 7.77/1.51  
% 7.77/1.51  fof(f1,axiom,(
% 7.77/1.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2))))),
% 7.77/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.51  
% 7.77/1.51  fof(f21,plain,(
% 7.77/1.51    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.77/1.51    inference(ennf_transformation,[],[f1])).
% 7.77/1.51  
% 7.77/1.51  fof(f52,plain,(
% 7.77/1.51    ( ! [X2,X0,X1] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.77/1.51    inference(cnf_transformation,[],[f21])).
% 7.77/1.51  
% 7.77/1.51  fof(f14,axiom,(
% 7.77/1.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 7.77/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.51  
% 7.77/1.51  fof(f38,plain,(
% 7.77/1.51    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 7.77/1.51    inference(ennf_transformation,[],[f14])).
% 7.77/1.51  
% 7.77/1.51  fof(f39,plain,(
% 7.77/1.51    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 7.77/1.51    inference(flattening,[],[f38])).
% 7.77/1.51  
% 7.77/1.51  fof(f72,plain,(
% 7.77/1.51    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 7.77/1.51    inference(cnf_transformation,[],[f39])).
% 7.77/1.51  
% 7.77/1.51  fof(f5,axiom,(
% 7.77/1.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 7.77/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.51  
% 7.77/1.51  fof(f24,plain,(
% 7.77/1.51    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.77/1.51    inference(ennf_transformation,[],[f5])).
% 7.77/1.51  
% 7.77/1.51  fof(f25,plain,(
% 7.77/1.51    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.77/1.51    inference(flattening,[],[f24])).
% 7.77/1.51  
% 7.77/1.51  fof(f57,plain,(
% 7.77/1.51    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.77/1.51    inference(cnf_transformation,[],[f25])).
% 7.77/1.51  
% 7.77/1.51  fof(f80,plain,(
% 7.77/1.51    ( ! [X2,X0,X1] : (k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.77/1.51    inference(cnf_transformation,[],[f45])).
% 7.77/1.51  
% 7.77/1.51  fof(f4,axiom,(
% 7.77/1.51    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 7.77/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.51  
% 7.77/1.51  fof(f23,plain,(
% 7.77/1.51    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 7.77/1.51    inference(ennf_transformation,[],[f4])).
% 7.77/1.51  
% 7.77/1.51  fof(f56,plain,(
% 7.77/1.51    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 7.77/1.51    inference(cnf_transformation,[],[f23])).
% 7.77/1.51  
% 7.77/1.51  fof(f96,plain,(
% 7.77/1.51    ( ! [X0] : (k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 7.77/1.51    inference(definition_unfolding,[],[f56,f73])).
% 7.77/1.51  
% 7.77/1.51  fof(f7,axiom,(
% 7.77/1.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 7.77/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.77/1.51  
% 7.77/1.51  fof(f28,plain,(
% 7.77/1.51    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.77/1.51    inference(ennf_transformation,[],[f7])).
% 7.77/1.51  
% 7.77/1.51  fof(f29,plain,(
% 7.77/1.51    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.77/1.51    inference(flattening,[],[f28])).
% 7.77/1.51  
% 7.77/1.51  fof(f61,plain,(
% 7.77/1.51    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.77/1.51    inference(cnf_transformation,[],[f29])).
% 7.77/1.51  
% 7.77/1.51  fof(f92,plain,(
% 7.77/1.51    k2_funct_1(sK2) != sK3),
% 7.77/1.51    inference(cnf_transformation,[],[f51])).
% 7.77/1.51  
% 7.77/1.51  cnf(c_34,negated_conjecture,
% 7.77/1.51      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 7.77/1.51      inference(cnf_transformation,[],[f86]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_1260,plain,
% 7.77/1.51      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 7.77/1.51      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_14,plain,
% 7.77/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.77/1.51      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 7.77/1.51      inference(cnf_transformation,[],[f66]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_1272,plain,
% 7.77/1.51      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 7.77/1.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.77/1.51      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_2298,plain,
% 7.77/1.51      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 7.77/1.51      inference(superposition,[status(thm)],[c_1260,c_1272]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_21,plain,
% 7.77/1.51      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 7.77/1.51      | ~ v1_funct_2(X2,X0,X1)
% 7.77/1.51      | ~ v1_funct_2(X3,X1,X0)
% 7.77/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 7.77/1.51      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.77/1.51      | ~ v1_funct_1(X2)
% 7.77/1.51      | ~ v1_funct_1(X3)
% 7.77/1.51      | k2_relset_1(X1,X0,X3) = X0 ),
% 7.77/1.51      inference(cnf_transformation,[],[f74]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_32,negated_conjecture,
% 7.77/1.51      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 7.77/1.51      inference(cnf_transformation,[],[f88]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_433,plain,
% 7.77/1.51      ( ~ v1_funct_2(X0,X1,X2)
% 7.77/1.51      | ~ v1_funct_2(X3,X2,X1)
% 7.77/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 7.77/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.77/1.51      | ~ v1_funct_1(X0)
% 7.77/1.51      | ~ v1_funct_1(X3)
% 7.77/1.51      | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.77/1.51      | k2_relset_1(X1,X2,X0) = X2
% 7.77/1.51      | k6_partfun1(X2) != k6_partfun1(sK0)
% 7.77/1.51      | sK0 != X2 ),
% 7.77/1.51      inference(resolution_lifted,[status(thm)],[c_21,c_32]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_434,plain,
% 7.77/1.51      ( ~ v1_funct_2(X0,X1,sK0)
% 7.77/1.51      | ~ v1_funct_2(X2,sK0,X1)
% 7.77/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 7.77/1.51      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 7.77/1.51      | ~ v1_funct_1(X0)
% 7.77/1.51      | ~ v1_funct_1(X2)
% 7.77/1.51      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.77/1.51      | k2_relset_1(X1,sK0,X0) = sK0
% 7.77/1.51      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 7.77/1.51      inference(unflattening,[status(thm)],[c_433]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_521,plain,
% 7.77/1.51      ( ~ v1_funct_2(X0,X1,sK0)
% 7.77/1.51      | ~ v1_funct_2(X2,sK0,X1)
% 7.77/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 7.77/1.51      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 7.77/1.51      | ~ v1_funct_1(X0)
% 7.77/1.51      | ~ v1_funct_1(X2)
% 7.77/1.51      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.77/1.51      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 7.77/1.51      inference(equality_resolution_simp,[status(thm)],[c_434]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_1252,plain,
% 7.77/1.51      ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.77/1.51      | k2_relset_1(X0,sK0,X2) = sK0
% 7.77/1.51      | v1_funct_2(X2,X0,sK0) != iProver_top
% 7.77/1.51      | v1_funct_2(X1,sK0,X0) != iProver_top
% 7.77/1.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 7.77/1.51      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 7.77/1.51      | v1_funct_1(X2) != iProver_top
% 7.77/1.51      | v1_funct_1(X1) != iProver_top ),
% 7.77/1.51      inference(predicate_to_equality,[status(thm)],[c_521]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_1823,plain,
% 7.77/1.51      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 7.77/1.51      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 7.77/1.51      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 7.77/1.51      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.77/1.51      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.77/1.51      | v1_funct_1(sK3) != iProver_top
% 7.77/1.51      | v1_funct_1(sK2) != iProver_top ),
% 7.77/1.51      inference(equality_resolution,[status(thm)],[c_1252]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_39,negated_conjecture,
% 7.77/1.51      ( v1_funct_1(sK2) ),
% 7.77/1.51      inference(cnf_transformation,[],[f81]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_40,plain,
% 7.77/1.51      ( v1_funct_1(sK2) = iProver_top ),
% 7.77/1.51      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_38,negated_conjecture,
% 7.77/1.51      ( v1_funct_2(sK2,sK0,sK1) ),
% 7.77/1.51      inference(cnf_transformation,[],[f82]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_41,plain,
% 7.77/1.51      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 7.77/1.51      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_37,negated_conjecture,
% 7.77/1.51      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 7.77/1.51      inference(cnf_transformation,[],[f83]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_42,plain,
% 7.77/1.51      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.77/1.51      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_36,negated_conjecture,
% 7.77/1.51      ( v1_funct_1(sK3) ),
% 7.77/1.51      inference(cnf_transformation,[],[f84]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_43,plain,
% 7.77/1.51      ( v1_funct_1(sK3) = iProver_top ),
% 7.77/1.51      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_35,negated_conjecture,
% 7.77/1.51      ( v1_funct_2(sK3,sK1,sK0) ),
% 7.77/1.51      inference(cnf_transformation,[],[f85]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_44,plain,
% 7.77/1.51      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 7.77/1.51      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_45,plain,
% 7.77/1.51      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 7.77/1.51      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_2066,plain,
% 7.77/1.51      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 7.77/1.51      inference(global_propositional_subsumption,
% 7.77/1.51                [status(thm)],
% 7.77/1.51                [c_1823,c_40,c_41,c_42,c_43,c_44,c_45]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_2301,plain,
% 7.77/1.51      ( k2_relat_1(sK3) = sK0 ),
% 7.77/1.51      inference(light_normalisation,[status(thm)],[c_2298,c_2066]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_2,plain,
% 7.77/1.51      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 7.77/1.51      inference(cnf_transformation,[],[f94]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_8,plain,
% 7.77/1.51      ( v2_funct_1(X0)
% 7.77/1.51      | ~ v2_funct_1(k5_relat_1(X0,X1))
% 7.77/1.51      | ~ v1_funct_1(X1)
% 7.77/1.51      | ~ v1_funct_1(X0)
% 7.77/1.51      | ~ v1_relat_1(X0)
% 7.77/1.51      | ~ v1_relat_1(X1)
% 7.77/1.51      | k1_relat_1(X1) != k2_relat_1(X0) ),
% 7.77/1.51      inference(cnf_transformation,[],[f59]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_1278,plain,
% 7.77/1.51      ( k1_relat_1(X0) != k2_relat_1(X1)
% 7.77/1.51      | v2_funct_1(X1) = iProver_top
% 7.77/1.51      | v2_funct_1(k5_relat_1(X1,X0)) != iProver_top
% 7.77/1.51      | v1_funct_1(X1) != iProver_top
% 7.77/1.51      | v1_funct_1(X0) != iProver_top
% 7.77/1.51      | v1_relat_1(X1) != iProver_top
% 7.77/1.51      | v1_relat_1(X0) != iProver_top ),
% 7.77/1.51      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_4992,plain,
% 7.77/1.51      ( k2_relat_1(X0) != X1
% 7.77/1.51      | v2_funct_1(X0) = iProver_top
% 7.77/1.51      | v2_funct_1(k5_relat_1(X0,k6_partfun1(X1))) != iProver_top
% 7.77/1.51      | v1_funct_1(X0) != iProver_top
% 7.77/1.51      | v1_funct_1(k6_partfun1(X1)) != iProver_top
% 7.77/1.51      | v1_relat_1(X0) != iProver_top
% 7.77/1.51      | v1_relat_1(k6_partfun1(X1)) != iProver_top ),
% 7.77/1.51      inference(superposition,[status(thm)],[c_2,c_1278]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_5727,plain,
% 7.77/1.51      ( sK0 != X0
% 7.77/1.51      | v2_funct_1(k5_relat_1(sK3,k6_partfun1(X0))) != iProver_top
% 7.77/1.51      | v2_funct_1(sK3) = iProver_top
% 7.77/1.51      | v1_funct_1(k6_partfun1(X0)) != iProver_top
% 7.77/1.51      | v1_funct_1(sK3) != iProver_top
% 7.77/1.51      | v1_relat_1(k6_partfun1(X0)) != iProver_top
% 7.77/1.51      | v1_relat_1(sK3) != iProver_top ),
% 7.77/1.51      inference(superposition,[status(thm)],[c_2301,c_4992]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_31,negated_conjecture,
% 7.77/1.51      ( v2_funct_1(sK2) ),
% 7.77/1.51      inference(cnf_transformation,[],[f89]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_47,plain,
% 7.77/1.51      ( v2_funct_1(sK2) = iProver_top ),
% 7.77/1.51      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_16,plain,
% 7.77/1.51      ( ~ r2_relset_1(X0,X1,X2,X3)
% 7.77/1.51      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.77/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.77/1.51      | X3 = X2 ),
% 7.77/1.51      inference(cnf_transformation,[],[f67]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_420,plain,
% 7.77/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.77/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.77/1.51      | X3 = X0
% 7.77/1.51      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 7.77/1.51      | k6_partfun1(sK0) != X3
% 7.77/1.51      | sK0 != X2
% 7.77/1.51      | sK0 != X1 ),
% 7.77/1.51      inference(resolution_lifted,[status(thm)],[c_16,c_32]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_421,plain,
% 7.77/1.51      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.77/1.51      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.77/1.51      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.77/1.51      inference(unflattening,[status(thm)],[c_420]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_17,plain,
% 7.77/1.51      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 7.77/1.51      inference(cnf_transformation,[],[f97]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_429,plain,
% 7.77/1.51      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.77/1.51      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.77/1.51      inference(forward_subsumption_resolution,
% 7.77/1.51                [status(thm)],
% 7.77/1.51                [c_421,c_17]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_1253,plain,
% 7.77/1.51      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.77/1.51      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 7.77/1.51      inference(predicate_to_equality,[status(thm)],[c_429]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_18,plain,
% 7.77/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.77/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.77/1.51      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.77/1.51      | ~ v1_funct_1(X0)
% 7.77/1.51      | ~ v1_funct_1(X3) ),
% 7.77/1.51      inference(cnf_transformation,[],[f71]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_1369,plain,
% 7.77/1.51      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.77/1.51      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 7.77/1.51      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.77/1.51      | ~ v1_funct_1(sK3)
% 7.77/1.51      | ~ v1_funct_1(sK2) ),
% 7.77/1.51      inference(instantiation,[status(thm)],[c_18]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_2059,plain,
% 7.77/1.51      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.77/1.51      inference(global_propositional_subsumption,
% 7.77/1.51                [status(thm)],
% 7.77/1.51                [c_1253,c_39,c_37,c_36,c_34,c_429,c_1369]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_19,plain,
% 7.77/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.77/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.77/1.51      | ~ v1_funct_1(X0)
% 7.77/1.51      | ~ v1_funct_1(X3)
% 7.77/1.51      | v1_funct_1(k1_partfun1(X4,X5,X1,X2,X3,X0)) ),
% 7.77/1.51      inference(cnf_transformation,[],[f70]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_1269,plain,
% 7.77/1.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.77/1.51      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 7.77/1.51      | v1_funct_1(X0) != iProver_top
% 7.77/1.51      | v1_funct_1(X3) != iProver_top
% 7.77/1.51      | v1_funct_1(k1_partfun1(X4,X5,X1,X2,X3,X0)) = iProver_top ),
% 7.77/1.51      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_4926,plain,
% 7.77/1.51      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.77/1.51      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.77/1.51      | v1_funct_1(k6_partfun1(sK0)) = iProver_top
% 7.77/1.51      | v1_funct_1(sK3) != iProver_top
% 7.77/1.51      | v1_funct_1(sK2) != iProver_top ),
% 7.77/1.51      inference(superposition,[status(thm)],[c_2059,c_1269]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_33,negated_conjecture,
% 7.77/1.51      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 7.77/1.51      inference(cnf_transformation,[],[f87]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_23,plain,
% 7.77/1.51      ( ~ v1_funct_2(X0,X1,X2)
% 7.77/1.51      | ~ v1_funct_2(X3,X4,X1)
% 7.77/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 7.77/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.77/1.51      | v2_funct_1(X0)
% 7.77/1.51      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 7.77/1.51      | ~ v1_funct_1(X0)
% 7.77/1.51      | ~ v1_funct_1(X3)
% 7.77/1.51      | k2_relset_1(X4,X1,X3) != X1
% 7.77/1.51      | k1_xboole_0 = X2 ),
% 7.77/1.51      inference(cnf_transformation,[],[f77]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_1266,plain,
% 7.77/1.51      ( k2_relset_1(X0,X1,X2) != X1
% 7.77/1.51      | k1_xboole_0 = X3
% 7.77/1.51      | v1_funct_2(X4,X1,X3) != iProver_top
% 7.77/1.51      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.77/1.51      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
% 7.77/1.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.77/1.51      | v2_funct_1(X4) = iProver_top
% 7.77/1.51      | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top
% 7.77/1.51      | v1_funct_1(X4) != iProver_top
% 7.77/1.51      | v1_funct_1(X2) != iProver_top ),
% 7.77/1.51      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_6713,plain,
% 7.77/1.51      ( k1_xboole_0 = X0
% 7.77/1.51      | v1_funct_2(X1,sK1,X0) != iProver_top
% 7.77/1.51      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 7.77/1.51      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 7.77/1.51      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.77/1.51      | v2_funct_1(X1) = iProver_top
% 7.77/1.51      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
% 7.77/1.51      | v1_funct_1(X1) != iProver_top
% 7.77/1.51      | v1_funct_1(sK2) != iProver_top ),
% 7.77/1.51      inference(superposition,[status(thm)],[c_33,c_1266]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_6861,plain,
% 7.77/1.51      ( v1_funct_1(X1) != iProver_top
% 7.77/1.51      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
% 7.77/1.51      | v2_funct_1(X1) = iProver_top
% 7.77/1.51      | v1_funct_2(X1,sK1,X0) != iProver_top
% 7.77/1.51      | k1_xboole_0 = X0
% 7.77/1.51      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top ),
% 7.77/1.51      inference(global_propositional_subsumption,
% 7.77/1.51                [status(thm)],
% 7.77/1.51                [c_6713,c_40,c_41,c_42]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_6862,plain,
% 7.77/1.51      ( k1_xboole_0 = X0
% 7.77/1.51      | v1_funct_2(X1,sK1,X0) != iProver_top
% 7.77/1.51      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 7.77/1.51      | v2_funct_1(X1) = iProver_top
% 7.77/1.51      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
% 7.77/1.51      | v1_funct_1(X1) != iProver_top ),
% 7.77/1.51      inference(renaming,[status(thm)],[c_6861]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_6865,plain,
% 7.77/1.51      ( sK0 = k1_xboole_0
% 7.77/1.51      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 7.77/1.51      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.77/1.51      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 7.77/1.51      | v2_funct_1(sK3) = iProver_top
% 7.77/1.51      | v1_funct_1(sK3) != iProver_top ),
% 7.77/1.51      inference(superposition,[status(thm)],[c_2059,c_6862]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_30,negated_conjecture,
% 7.77/1.51      ( k1_xboole_0 != sK0 ),
% 7.77/1.51      inference(cnf_transformation,[],[f90]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_712,plain,( X0 = X0 ),theory(equality) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_743,plain,
% 7.77/1.51      ( k1_xboole_0 = k1_xboole_0 ),
% 7.77/1.51      inference(instantiation,[status(thm)],[c_712]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_713,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_1367,plain,
% 7.77/1.51      ( sK0 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK0 ),
% 7.77/1.51      inference(instantiation,[status(thm)],[c_713]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_1368,plain,
% 7.77/1.51      ( sK0 != k1_xboole_0
% 7.77/1.51      | k1_xboole_0 = sK0
% 7.77/1.51      | k1_xboole_0 != k1_xboole_0 ),
% 7.77/1.51      inference(instantiation,[status(thm)],[c_1367]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_6903,plain,
% 7.77/1.51      ( v2_funct_1(sK3) = iProver_top
% 7.77/1.51      | v2_funct_1(k6_partfun1(sK0)) != iProver_top ),
% 7.77/1.51      inference(global_propositional_subsumption,
% 7.77/1.51                [status(thm)],
% 7.77/1.51                [c_6865,c_43,c_44,c_45,c_30,c_743,c_1368]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_6904,plain,
% 7.77/1.51      ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 7.77/1.51      | v2_funct_1(sK3) = iProver_top ),
% 7.77/1.51      inference(renaming,[status(thm)],[c_6903]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_1,plain,
% 7.77/1.51      ( k2_relat_1(k6_partfun1(X0)) = X0 ),
% 7.77/1.51      inference(cnf_transformation,[],[f93]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_1261,plain,
% 7.77/1.51      ( v2_funct_1(sK2) = iProver_top ),
% 7.77/1.51      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_12,plain,
% 7.77/1.51      ( ~ v2_funct_1(X0)
% 7.77/1.51      | ~ v1_funct_1(X0)
% 7.77/1.51      | ~ v1_relat_1(X0)
% 7.77/1.51      | k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ),
% 7.77/1.51      inference(cnf_transformation,[],[f63]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_1274,plain,
% 7.77/1.51      ( k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
% 7.77/1.51      | v2_funct_1(X0) != iProver_top
% 7.77/1.51      | v1_funct_1(X0) != iProver_top
% 7.77/1.51      | v1_relat_1(X0) != iProver_top ),
% 7.77/1.51      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_3545,plain,
% 7.77/1.51      ( k1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) = k1_relat_1(sK2)
% 7.77/1.51      | v1_funct_1(sK2) != iProver_top
% 7.77/1.51      | v1_relat_1(sK2) != iProver_top ),
% 7.77/1.51      inference(superposition,[status(thm)],[c_1261,c_1274]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_27,plain,
% 7.77/1.51      ( ~ v1_funct_2(X0,X1,X2)
% 7.77/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.77/1.51      | ~ v2_funct_1(X0)
% 7.77/1.51      | ~ v1_funct_1(X0)
% 7.77/1.51      | k2_relset_1(X1,X2,X0) != X2
% 7.77/1.51      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 7.77/1.51      | k1_xboole_0 = X2 ),
% 7.77/1.51      inference(cnf_transformation,[],[f79]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_1262,plain,
% 7.77/1.51      ( k2_relset_1(X0,X1,X2) != X1
% 7.77/1.51      | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
% 7.77/1.51      | k1_xboole_0 = X1
% 7.77/1.51      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.77/1.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.77/1.51      | v2_funct_1(X2) != iProver_top
% 7.77/1.51      | v1_funct_1(X2) != iProver_top ),
% 7.77/1.51      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_3166,plain,
% 7.77/1.51      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
% 7.77/1.51      | sK1 = k1_xboole_0
% 7.77/1.51      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 7.77/1.51      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.77/1.51      | v2_funct_1(sK2) != iProver_top
% 7.77/1.51      | v1_funct_1(sK2) != iProver_top ),
% 7.77/1.51      inference(superposition,[status(thm)],[c_33,c_1262]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_29,negated_conjecture,
% 7.77/1.51      ( k1_xboole_0 != sK1 ),
% 7.77/1.51      inference(cnf_transformation,[],[f91]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_1332,plain,
% 7.77/1.51      ( ~ v1_funct_2(X0,X1,sK1)
% 7.77/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 7.77/1.51      | ~ v2_funct_1(X0)
% 7.77/1.51      | ~ v1_funct_1(X0)
% 7.77/1.51      | k2_relset_1(X1,sK1,X0) != sK1
% 7.77/1.51      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 7.77/1.51      | k1_xboole_0 = sK1 ),
% 7.77/1.51      inference(instantiation,[status(thm)],[c_27]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_1440,plain,
% 7.77/1.51      ( ~ v1_funct_2(sK2,X0,sK1)
% 7.77/1.51      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
% 7.77/1.51      | ~ v2_funct_1(sK2)
% 7.77/1.51      | ~ v1_funct_1(sK2)
% 7.77/1.51      | k2_relset_1(X0,sK1,sK2) != sK1
% 7.77/1.51      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
% 7.77/1.51      | k1_xboole_0 = sK1 ),
% 7.77/1.51      inference(instantiation,[status(thm)],[c_1332]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_1659,plain,
% 7.77/1.51      ( ~ v1_funct_2(sK2,sK0,sK1)
% 7.77/1.51      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.77/1.51      | ~ v2_funct_1(sK2)
% 7.77/1.51      | ~ v1_funct_1(sK2)
% 7.77/1.51      | k2_relset_1(sK0,sK1,sK2) != sK1
% 7.77/1.51      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
% 7.77/1.51      | k1_xboole_0 = sK1 ),
% 7.77/1.51      inference(instantiation,[status(thm)],[c_1440]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_3270,plain,
% 7.77/1.51      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
% 7.77/1.51      inference(global_propositional_subsumption,
% 7.77/1.51                [status(thm)],
% 7.77/1.51                [c_3166,c_39,c_38,c_37,c_33,c_31,c_29,c_1659]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_3546,plain,
% 7.77/1.51      ( k1_relat_1(k6_partfun1(sK0)) = k1_relat_1(sK2)
% 7.77/1.51      | v1_funct_1(sK2) != iProver_top
% 7.77/1.51      | v1_relat_1(sK2) != iProver_top ),
% 7.77/1.51      inference(light_normalisation,[status(thm)],[c_3545,c_3270]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_3547,plain,
% 7.77/1.51      ( k1_relat_1(sK2) = sK0
% 7.77/1.51      | v1_funct_1(sK2) != iProver_top
% 7.77/1.51      | v1_relat_1(sK2) != iProver_top ),
% 7.77/1.51      inference(demodulation,[status(thm)],[c_3546,c_2]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_1257,plain,
% 7.77/1.51      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.77/1.51      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_13,plain,
% 7.77/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.77/1.51      | v1_relat_1(X0) ),
% 7.77/1.51      inference(cnf_transformation,[],[f65]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_1273,plain,
% 7.77/1.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.77/1.51      | v1_relat_1(X0) = iProver_top ),
% 7.77/1.51      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_2254,plain,
% 7.77/1.51      ( v1_relat_1(sK2) = iProver_top ),
% 7.77/1.51      inference(superposition,[status(thm)],[c_1257,c_1273]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_3550,plain,
% 7.77/1.51      ( k1_relat_1(sK2) = sK0 ),
% 7.77/1.51      inference(global_propositional_subsumption,
% 7.77/1.51                [status(thm)],
% 7.77/1.51                [c_3547,c_40,c_2254]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_4993,plain,
% 7.77/1.51      ( k2_relat_1(X0) != sK0
% 7.77/1.51      | v2_funct_1(X0) = iProver_top
% 7.77/1.51      | v2_funct_1(k5_relat_1(X0,sK2)) != iProver_top
% 7.77/1.51      | v1_funct_1(X0) != iProver_top
% 7.77/1.51      | v1_funct_1(sK2) != iProver_top
% 7.77/1.51      | v1_relat_1(X0) != iProver_top
% 7.77/1.51      | v1_relat_1(sK2) != iProver_top ),
% 7.77/1.51      inference(superposition,[status(thm)],[c_3550,c_1278]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_15564,plain,
% 7.77/1.51      ( v1_relat_1(X0) != iProver_top
% 7.77/1.51      | k2_relat_1(X0) != sK0
% 7.77/1.51      | v2_funct_1(X0) = iProver_top
% 7.77/1.51      | v2_funct_1(k5_relat_1(X0,sK2)) != iProver_top
% 7.77/1.51      | v1_funct_1(X0) != iProver_top ),
% 7.77/1.51      inference(global_propositional_subsumption,
% 7.77/1.51                [status(thm)],
% 7.77/1.51                [c_4993,c_40,c_2254]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_15565,plain,
% 7.77/1.51      ( k2_relat_1(X0) != sK0
% 7.77/1.51      | v2_funct_1(X0) = iProver_top
% 7.77/1.51      | v2_funct_1(k5_relat_1(X0,sK2)) != iProver_top
% 7.77/1.51      | v1_funct_1(X0) != iProver_top
% 7.77/1.51      | v1_relat_1(X0) != iProver_top ),
% 7.77/1.51      inference(renaming,[status(thm)],[c_15564]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_15570,plain,
% 7.77/1.51      ( sK0 != X0
% 7.77/1.51      | v2_funct_1(k5_relat_1(k6_partfun1(X0),sK2)) != iProver_top
% 7.77/1.51      | v2_funct_1(k6_partfun1(X0)) = iProver_top
% 7.77/1.51      | v1_funct_1(k6_partfun1(X0)) != iProver_top
% 7.77/1.51      | v1_relat_1(k6_partfun1(X0)) != iProver_top ),
% 7.77/1.51      inference(superposition,[status(thm)],[c_1,c_15565]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_1271,plain,
% 7.77/1.51      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 7.77/1.51      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_2252,plain,
% 7.77/1.51      ( v1_relat_1(k6_partfun1(X0)) = iProver_top ),
% 7.77/1.51      inference(superposition,[status(thm)],[c_1271,c_1273]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_15581,plain,
% 7.77/1.51      ( v1_funct_1(k6_partfun1(X0)) != iProver_top
% 7.77/1.51      | v2_funct_1(k6_partfun1(X0)) = iProver_top
% 7.77/1.51      | v2_funct_1(k5_relat_1(k6_partfun1(X0),sK2)) != iProver_top
% 7.77/1.51      | sK0 != X0 ),
% 7.77/1.51      inference(global_propositional_subsumption,
% 7.77/1.51                [status(thm)],
% 7.77/1.51                [c_15570,c_2252]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_15582,plain,
% 7.77/1.51      ( sK0 != X0
% 7.77/1.51      | v2_funct_1(k5_relat_1(k6_partfun1(X0),sK2)) != iProver_top
% 7.77/1.51      | v2_funct_1(k6_partfun1(X0)) = iProver_top
% 7.77/1.51      | v1_funct_1(k6_partfun1(X0)) != iProver_top ),
% 7.77/1.51      inference(renaming,[status(thm)],[c_15581]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_15587,plain,
% 7.77/1.51      ( v2_funct_1(k5_relat_1(k6_partfun1(sK0),sK2)) != iProver_top
% 7.77/1.51      | v2_funct_1(k6_partfun1(sK0)) = iProver_top
% 7.77/1.51      | v1_funct_1(k6_partfun1(sK0)) != iProver_top ),
% 7.77/1.51      inference(equality_resolution,[status(thm)],[c_15582]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_3,plain,
% 7.77/1.51      ( ~ v1_relat_1(X0)
% 7.77/1.51      | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 ),
% 7.77/1.51      inference(cnf_transformation,[],[f95]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_1283,plain,
% 7.77/1.51      ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
% 7.77/1.51      | v1_relat_1(X0) != iProver_top ),
% 7.77/1.51      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_2832,plain,
% 7.77/1.51      ( k5_relat_1(k6_partfun1(k1_relat_1(sK2)),sK2) = sK2 ),
% 7.77/1.51      inference(superposition,[status(thm)],[c_2254,c_1283]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_3553,plain,
% 7.77/1.51      ( k5_relat_1(k6_partfun1(sK0),sK2) = sK2 ),
% 7.77/1.51      inference(demodulation,[status(thm)],[c_3550,c_2832]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_15588,plain,
% 7.77/1.51      ( v2_funct_1(k6_partfun1(sK0)) = iProver_top
% 7.77/1.51      | v2_funct_1(sK2) != iProver_top
% 7.77/1.51      | v1_funct_1(k6_partfun1(sK0)) != iProver_top ),
% 7.77/1.51      inference(light_normalisation,[status(thm)],[c_15587,c_3553]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_18856,plain,
% 7.77/1.51      ( v2_funct_1(sK3) = iProver_top ),
% 7.77/1.51      inference(global_propositional_subsumption,
% 7.77/1.51                [status(thm)],
% 7.77/1.51                [c_5727,c_40,c_42,c_43,c_45,c_47,c_4926,c_6904,c_15588]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_18861,plain,
% 7.77/1.51      ( k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) = k1_relat_1(sK3)
% 7.77/1.51      | v1_funct_1(sK3) != iProver_top
% 7.77/1.51      | v1_relat_1(sK3) != iProver_top ),
% 7.77/1.51      inference(superposition,[status(thm)],[c_18856,c_1274]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_3167,plain,
% 7.77/1.51      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 7.77/1.51      | sK0 = k1_xboole_0
% 7.77/1.51      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 7.77/1.51      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.77/1.51      | v2_funct_1(sK3) != iProver_top
% 7.77/1.51      | v1_funct_1(sK3) != iProver_top ),
% 7.77/1.51      inference(superposition,[status(thm)],[c_2066,c_1262]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_3369,plain,
% 7.77/1.51      ( v2_funct_1(sK3) != iProver_top
% 7.77/1.51      | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
% 7.77/1.51      inference(global_propositional_subsumption,
% 7.77/1.51                [status(thm)],
% 7.77/1.51                [c_3167,c_43,c_44,c_45,c_30,c_743,c_1368]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_3370,plain,
% 7.77/1.51      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 7.77/1.51      | v2_funct_1(sK3) != iProver_top ),
% 7.77/1.51      inference(renaming,[status(thm)],[c_3369]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_18865,plain,
% 7.77/1.51      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
% 7.77/1.51      inference(superposition,[status(thm)],[c_18856,c_3370]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_18867,plain,
% 7.77/1.51      ( k1_relat_1(k6_partfun1(sK1)) = k1_relat_1(sK3)
% 7.77/1.51      | v1_funct_1(sK3) != iProver_top
% 7.77/1.51      | v1_relat_1(sK3) != iProver_top ),
% 7.77/1.51      inference(demodulation,[status(thm)],[c_18861,c_18865]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_18868,plain,
% 7.77/1.51      ( k1_relat_1(sK3) = sK1
% 7.77/1.51      | v1_funct_1(sK3) != iProver_top
% 7.77/1.51      | v1_relat_1(sK3) != iProver_top ),
% 7.77/1.51      inference(demodulation,[status(thm)],[c_18867,c_2]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_2253,plain,
% 7.77/1.51      ( v1_relat_1(sK3) = iProver_top ),
% 7.77/1.51      inference(superposition,[status(thm)],[c_1260,c_1273]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_18932,plain,
% 7.77/1.51      ( k1_relat_1(sK3) = sK1 ),
% 7.77/1.51      inference(global_propositional_subsumption,
% 7.77/1.51                [status(thm)],
% 7.77/1.51                [c_18868,c_43,c_2253]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_2828,plain,
% 7.77/1.51      ( k5_relat_1(k6_partfun1(k1_relat_1(sK3)),sK3) = sK3 ),
% 7.77/1.51      inference(superposition,[status(thm)],[c_2253,c_1283]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_0,plain,
% 7.77/1.51      ( ~ v1_relat_1(X0)
% 7.77/1.51      | ~ v1_relat_1(X1)
% 7.77/1.51      | ~ v1_relat_1(X2)
% 7.77/1.51      | k5_relat_1(k5_relat_1(X2,X1),X0) = k5_relat_1(X2,k5_relat_1(X1,X0)) ),
% 7.77/1.51      inference(cnf_transformation,[],[f52]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_1284,plain,
% 7.77/1.51      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
% 7.77/1.51      | v1_relat_1(X2) != iProver_top
% 7.77/1.51      | v1_relat_1(X1) != iProver_top
% 7.77/1.51      | v1_relat_1(X0) != iProver_top ),
% 7.77/1.51      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_3783,plain,
% 7.77/1.51      ( k5_relat_1(k6_partfun1(X0),k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(k6_partfun1(X0),X1),X2)
% 7.77/1.51      | v1_relat_1(X1) != iProver_top
% 7.77/1.51      | v1_relat_1(X2) != iProver_top ),
% 7.77/1.51      inference(superposition,[status(thm)],[c_2252,c_1284]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_9724,plain,
% 7.77/1.51      ( k5_relat_1(k5_relat_1(k6_partfun1(X0),sK3),X1) = k5_relat_1(k6_partfun1(X0),k5_relat_1(sK3,X1))
% 7.77/1.51      | v1_relat_1(X1) != iProver_top ),
% 7.77/1.51      inference(superposition,[status(thm)],[c_2253,c_3783]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_9754,plain,
% 7.77/1.51      ( k5_relat_1(k5_relat_1(k6_partfun1(X0),sK3),sK2) = k5_relat_1(k6_partfun1(X0),k5_relat_1(sK3,sK2)) ),
% 7.77/1.51      inference(superposition,[status(thm)],[c_2254,c_9724]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_9777,plain,
% 7.77/1.51      ( k5_relat_1(k6_partfun1(k1_relat_1(sK3)),k5_relat_1(sK3,sK2)) = k5_relat_1(sK3,sK2) ),
% 7.77/1.51      inference(superposition,[status(thm)],[c_2828,c_9754]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_18937,plain,
% 7.77/1.51      ( k5_relat_1(k6_partfun1(sK1),k5_relat_1(sK3,sK2)) = k5_relat_1(sK3,sK2) ),
% 7.77/1.51      inference(demodulation,[status(thm)],[c_18932,c_9777]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_20,plain,
% 7.77/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.77/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.77/1.51      | ~ v1_funct_1(X0)
% 7.77/1.51      | ~ v1_funct_1(X3)
% 7.77/1.51      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 7.77/1.51      inference(cnf_transformation,[],[f72]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_1268,plain,
% 7.77/1.51      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 7.77/1.51      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 7.77/1.51      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.77/1.51      | v1_funct_1(X5) != iProver_top
% 7.77/1.51      | v1_funct_1(X4) != iProver_top ),
% 7.77/1.51      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_4981,plain,
% 7.77/1.51      ( k1_partfun1(X0,X1,sK0,sK1,X2,sK2) = k5_relat_1(X2,sK2)
% 7.77/1.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.77/1.51      | v1_funct_1(X2) != iProver_top
% 7.77/1.51      | v1_funct_1(sK2) != iProver_top ),
% 7.77/1.51      inference(superposition,[status(thm)],[c_1257,c_1268]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_5098,plain,
% 7.77/1.51      ( v1_funct_1(X2) != iProver_top
% 7.77/1.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.77/1.51      | k1_partfun1(X0,X1,sK0,sK1,X2,sK2) = k5_relat_1(X2,sK2) ),
% 7.77/1.51      inference(global_propositional_subsumption,
% 7.77/1.51                [status(thm)],
% 7.77/1.51                [c_4981,c_40]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_5099,plain,
% 7.77/1.51      ( k1_partfun1(X0,X1,sK0,sK1,X2,sK2) = k5_relat_1(X2,sK2)
% 7.77/1.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.77/1.51      | v1_funct_1(X2) != iProver_top ),
% 7.77/1.51      inference(renaming,[status(thm)],[c_5098]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_5105,plain,
% 7.77/1.51      ( k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) = k5_relat_1(sK3,sK2)
% 7.77/1.51      | v1_funct_1(sK3) != iProver_top ),
% 7.77/1.51      inference(superposition,[status(thm)],[c_1260,c_5099]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_5123,plain,
% 7.77/1.51      ( k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) = k5_relat_1(sK3,sK2) ),
% 7.77/1.51      inference(global_propositional_subsumption,
% 7.77/1.51                [status(thm)],
% 7.77/1.51                [c_5105,c_43]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_1270,plain,
% 7.77/1.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.77/1.51      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 7.77/1.51      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 7.77/1.51      | v1_funct_1(X0) != iProver_top
% 7.77/1.51      | v1_funct_1(X3) != iProver_top ),
% 7.77/1.51      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_5767,plain,
% 7.77/1.51      ( m1_subset_1(k5_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
% 7.77/1.51      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.77/1.51      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.77/1.51      | v1_funct_1(sK3) != iProver_top
% 7.77/1.51      | v1_funct_1(sK2) != iProver_top ),
% 7.77/1.51      inference(superposition,[status(thm)],[c_5123,c_1270]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_7014,plain,
% 7.77/1.51      ( m1_subset_1(k5_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 7.77/1.51      inference(global_propositional_subsumption,
% 7.77/1.51                [status(thm)],
% 7.77/1.51                [c_5767,c_40,c_42,c_43,c_45]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_7021,plain,
% 7.77/1.51      ( v1_relat_1(k5_relat_1(sK3,sK2)) = iProver_top ),
% 7.77/1.51      inference(superposition,[status(thm)],[c_7014,c_1273]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_1255,plain,
% 7.77/1.51      ( v1_funct_1(sK2) = iProver_top ),
% 7.77/1.51      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_6,plain,
% 7.77/1.51      ( ~ v1_funct_1(X0)
% 7.77/1.51      | ~ v1_relat_1(X0)
% 7.77/1.51      | v1_relat_1(k2_funct_1(X0)) ),
% 7.77/1.51      inference(cnf_transformation,[],[f57]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_1280,plain,
% 7.77/1.51      ( v1_funct_1(X0) != iProver_top
% 7.77/1.51      | v1_relat_1(X0) != iProver_top
% 7.77/1.51      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 7.77/1.51      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_3780,plain,
% 7.77/1.51      ( k5_relat_1(k2_funct_1(X0),k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(k2_funct_1(X0),X1),X2)
% 7.77/1.51      | v1_funct_1(X0) != iProver_top
% 7.77/1.51      | v1_relat_1(X0) != iProver_top
% 7.77/1.51      | v1_relat_1(X1) != iProver_top
% 7.77/1.51      | v1_relat_1(X2) != iProver_top ),
% 7.77/1.51      inference(superposition,[status(thm)],[c_1280,c_1284]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_10065,plain,
% 7.77/1.51      ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1))
% 7.77/1.51      | v1_relat_1(X0) != iProver_top
% 7.77/1.51      | v1_relat_1(X1) != iProver_top
% 7.77/1.51      | v1_relat_1(sK2) != iProver_top ),
% 7.77/1.51      inference(superposition,[status(thm)],[c_1255,c_3780]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_10323,plain,
% 7.77/1.51      ( v1_relat_1(X1) != iProver_top
% 7.77/1.51      | v1_relat_1(X0) != iProver_top
% 7.77/1.51      | k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1)) ),
% 7.77/1.51      inference(global_propositional_subsumption,
% 7.77/1.51                [status(thm)],
% 7.77/1.51                [c_10065,c_2254]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_10324,plain,
% 7.77/1.51      ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1))
% 7.77/1.51      | v1_relat_1(X0) != iProver_top
% 7.77/1.51      | v1_relat_1(X1) != iProver_top ),
% 7.77/1.51      inference(renaming,[status(thm)],[c_10323]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_10331,plain,
% 7.77/1.51      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),X0)
% 7.77/1.51      | v1_relat_1(X0) != iProver_top ),
% 7.77/1.51      inference(superposition,[status(thm)],[c_2254,c_10324]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_26,plain,
% 7.77/1.51      ( ~ v1_funct_2(X0,X1,X2)
% 7.77/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.77/1.51      | ~ v2_funct_1(X0)
% 7.77/1.51      | ~ v1_funct_1(X0)
% 7.77/1.51      | k2_relset_1(X1,X2,X0) != X2
% 7.77/1.51      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
% 7.77/1.51      | k1_xboole_0 = X2 ),
% 7.77/1.51      inference(cnf_transformation,[],[f80]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_1263,plain,
% 7.77/1.51      ( k2_relset_1(X0,X1,X2) != X1
% 7.77/1.51      | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
% 7.77/1.51      | k1_xboole_0 = X1
% 7.77/1.51      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.77/1.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.77/1.51      | v2_funct_1(X2) != iProver_top
% 7.77/1.51      | v1_funct_1(X2) != iProver_top ),
% 7.77/1.51      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_3510,plain,
% 7.77/1.51      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 7.77/1.51      | sK1 = k1_xboole_0
% 7.77/1.51      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 7.77/1.51      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.77/1.51      | v2_funct_1(sK2) != iProver_top
% 7.77/1.51      | v1_funct_1(sK2) != iProver_top ),
% 7.77/1.51      inference(superposition,[status(thm)],[c_33,c_1263]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_1331,plain,
% 7.77/1.51      ( ~ v1_funct_2(X0,X1,sK1)
% 7.77/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 7.77/1.51      | ~ v2_funct_1(X0)
% 7.77/1.51      | ~ v1_funct_1(X0)
% 7.77/1.51      | k2_relset_1(X1,sK1,X0) != sK1
% 7.77/1.51      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(sK1)
% 7.77/1.51      | k1_xboole_0 = sK1 ),
% 7.77/1.51      inference(instantiation,[status(thm)],[c_26]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_1420,plain,
% 7.77/1.51      ( ~ v1_funct_2(sK2,X0,sK1)
% 7.77/1.51      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
% 7.77/1.51      | ~ v2_funct_1(sK2)
% 7.77/1.51      | ~ v1_funct_1(sK2)
% 7.77/1.51      | k2_relset_1(X0,sK1,sK2) != sK1
% 7.77/1.51      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 7.77/1.51      | k1_xboole_0 = sK1 ),
% 7.77/1.51      inference(instantiation,[status(thm)],[c_1331]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_1644,plain,
% 7.77/1.51      ( ~ v1_funct_2(sK2,sK0,sK1)
% 7.77/1.51      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.77/1.51      | ~ v2_funct_1(sK2)
% 7.77/1.51      | ~ v1_funct_1(sK2)
% 7.77/1.51      | k2_relset_1(sK0,sK1,sK2) != sK1
% 7.77/1.51      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 7.77/1.51      | k1_xboole_0 = sK1 ),
% 7.77/1.51      inference(instantiation,[status(thm)],[c_1420]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_4735,plain,
% 7.77/1.51      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
% 7.77/1.51      inference(global_propositional_subsumption,
% 7.77/1.51                [status(thm)],
% 7.77/1.51                [c_3510,c_39,c_38,c_37,c_33,c_31,c_29,c_1644]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_10336,plain,
% 7.77/1.51      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k6_partfun1(sK1),X0)
% 7.77/1.51      | v1_relat_1(X0) != iProver_top ),
% 7.77/1.51      inference(light_normalisation,[status(thm)],[c_10331,c_4735]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_10365,plain,
% 7.77/1.51      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,k5_relat_1(sK3,sK2))) = k5_relat_1(k6_partfun1(sK1),k5_relat_1(sK3,sK2)) ),
% 7.77/1.51      inference(superposition,[status(thm)],[c_7021,c_10336]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_3782,plain,
% 7.77/1.51      ( k5_relat_1(sK2,k5_relat_1(X0,X1)) = k5_relat_1(k5_relat_1(sK2,X0),X1)
% 7.77/1.51      | v1_relat_1(X0) != iProver_top
% 7.77/1.51      | v1_relat_1(X1) != iProver_top ),
% 7.77/1.51      inference(superposition,[status(thm)],[c_2254,c_1284]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_6024,plain,
% 7.77/1.51      ( k5_relat_1(k5_relat_1(sK2,sK3),X0) = k5_relat_1(sK2,k5_relat_1(sK3,X0))
% 7.77/1.51      | v1_relat_1(X0) != iProver_top ),
% 7.77/1.51      inference(superposition,[status(thm)],[c_2253,c_3782]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_4980,plain,
% 7.77/1.51      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 7.77/1.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.77/1.51      | v1_funct_1(X2) != iProver_top
% 7.77/1.51      | v1_funct_1(sK3) != iProver_top ),
% 7.77/1.51      inference(superposition,[status(thm)],[c_1260,c_1268]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_5067,plain,
% 7.77/1.51      ( v1_funct_1(X2) != iProver_top
% 7.77/1.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.77/1.51      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 7.77/1.51      inference(global_propositional_subsumption,
% 7.77/1.51                [status(thm)],
% 7.77/1.51                [c_4980,c_43]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_5068,plain,
% 7.77/1.51      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 7.77/1.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.77/1.51      | v1_funct_1(X2) != iProver_top ),
% 7.77/1.51      inference(renaming,[status(thm)],[c_5067]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_5075,plain,
% 7.77/1.51      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 7.77/1.51      | v1_funct_1(sK2) != iProver_top ),
% 7.77/1.51      inference(superposition,[status(thm)],[c_1257,c_5068]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_5076,plain,
% 7.77/1.51      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 7.77/1.51      | v1_funct_1(sK2) != iProver_top ),
% 7.77/1.51      inference(light_normalisation,[status(thm)],[c_5075,c_2059]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_5149,plain,
% 7.77/1.51      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 7.77/1.51      inference(global_propositional_subsumption,
% 7.77/1.51                [status(thm)],
% 7.77/1.51                [c_5076,c_40]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_6027,plain,
% 7.77/1.51      ( k5_relat_1(sK2,k5_relat_1(sK3,X0)) = k5_relat_1(k6_partfun1(sK0),X0)
% 7.77/1.51      | v1_relat_1(X0) != iProver_top ),
% 7.77/1.51      inference(light_normalisation,[status(thm)],[c_6024,c_5149]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_9623,plain,
% 7.77/1.51      ( k5_relat_1(sK2,k5_relat_1(sK3,sK2)) = k5_relat_1(k6_partfun1(sK0),sK2) ),
% 7.77/1.51      inference(superposition,[status(thm)],[c_2254,c_6027]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_9628,plain,
% 7.77/1.51      ( k5_relat_1(sK2,k5_relat_1(sK3,sK2)) = sK2 ),
% 7.77/1.51      inference(light_normalisation,[status(thm)],[c_9623,c_3553]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_10366,plain,
% 7.77/1.51      ( k5_relat_1(k6_partfun1(sK1),k5_relat_1(sK3,sK2)) = k6_partfun1(sK1) ),
% 7.77/1.51      inference(light_normalisation,
% 7.77/1.51                [status(thm)],
% 7.77/1.51                [c_10365,c_4735,c_9628]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_18940,plain,
% 7.77/1.51      ( k5_relat_1(sK3,sK2) = k6_partfun1(sK1) ),
% 7.77/1.51      inference(light_normalisation,[status(thm)],[c_18937,c_10366]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_3781,plain,
% 7.77/1.51      ( k5_relat_1(sK3,k5_relat_1(X0,X1)) = k5_relat_1(k5_relat_1(sK3,X0),X1)
% 7.77/1.51      | v1_relat_1(X0) != iProver_top
% 7.77/1.51      | v1_relat_1(X1) != iProver_top ),
% 7.77/1.51      inference(superposition,[status(thm)],[c_2253,c_1284]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_4781,plain,
% 7.77/1.51      ( k5_relat_1(k5_relat_1(sK3,sK2),X0) = k5_relat_1(sK3,k5_relat_1(sK2,X0))
% 7.77/1.51      | v1_relat_1(X0) != iProver_top ),
% 7.77/1.51      inference(superposition,[status(thm)],[c_2254,c_3781]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_5152,plain,
% 7.77/1.51      ( k5_relat_1(sK3,k5_relat_1(sK2,k2_funct_1(X0))) = k5_relat_1(k5_relat_1(sK3,sK2),k2_funct_1(X0))
% 7.77/1.51      | v1_funct_1(X0) != iProver_top
% 7.77/1.51      | v1_relat_1(X0) != iProver_top ),
% 7.77/1.51      inference(superposition,[status(thm)],[c_1280,c_4781]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_9883,plain,
% 7.77/1.51      ( k5_relat_1(k5_relat_1(sK3,sK2),k2_funct_1(sK2)) = k5_relat_1(sK3,k5_relat_1(sK2,k2_funct_1(sK2)))
% 7.77/1.51      | v1_relat_1(sK2) != iProver_top ),
% 7.77/1.51      inference(superposition,[status(thm)],[c_1255,c_5152]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_4,plain,
% 7.77/1.51      ( ~ v1_relat_1(X0)
% 7.77/1.51      | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ),
% 7.77/1.51      inference(cnf_transformation,[],[f96]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_1282,plain,
% 7.77/1.51      ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
% 7.77/1.51      | v1_relat_1(X0) != iProver_top ),
% 7.77/1.51      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_2829,plain,
% 7.77/1.51      ( k5_relat_1(sK3,k6_partfun1(k2_relat_1(sK3))) = sK3 ),
% 7.77/1.51      inference(superposition,[status(thm)],[c_2253,c_1282]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_2830,plain,
% 7.77/1.51      ( k5_relat_1(sK3,k6_partfun1(sK0)) = sK3 ),
% 7.77/1.51      inference(light_normalisation,[status(thm)],[c_2829,c_2301]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_9887,plain,
% 7.77/1.51      ( k5_relat_1(k5_relat_1(sK3,sK2),k2_funct_1(sK2)) = sK3
% 7.77/1.51      | v1_relat_1(sK2) != iProver_top ),
% 7.77/1.51      inference(light_normalisation,[status(thm)],[c_9883,c_2830,c_3270]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_9900,plain,
% 7.77/1.51      ( k5_relat_1(k5_relat_1(sK3,sK2),k2_funct_1(sK2)) = sK3 ),
% 7.77/1.51      inference(global_propositional_subsumption,
% 7.77/1.51                [status(thm)],
% 7.77/1.51                [c_9887,c_2254]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_19178,plain,
% 7.77/1.51      ( k5_relat_1(k6_partfun1(sK1),k2_funct_1(sK2)) = sK3 ),
% 7.77/1.51      inference(demodulation,[status(thm)],[c_18940,c_9900]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_2334,plain,
% 7.77/1.51      ( k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1(X0))),k2_funct_1(X0)) = k2_funct_1(X0)
% 7.77/1.51      | v1_funct_1(X0) != iProver_top
% 7.77/1.51      | v1_relat_1(X0) != iProver_top ),
% 7.77/1.51      inference(superposition,[status(thm)],[c_1280,c_1283]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_3376,plain,
% 7.77/1.51      ( k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1(sK2))),k2_funct_1(sK2)) = k2_funct_1(sK2)
% 7.77/1.51      | v1_relat_1(sK2) != iProver_top ),
% 7.77/1.51      inference(superposition,[status(thm)],[c_1255,c_2334]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_10,plain,
% 7.77/1.51      ( ~ v2_funct_1(X0)
% 7.77/1.51      | ~ v1_funct_1(X0)
% 7.77/1.51      | ~ v1_relat_1(X0)
% 7.77/1.51      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 7.77/1.51      inference(cnf_transformation,[],[f61]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_1276,plain,
% 7.77/1.51      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 7.77/1.51      | v2_funct_1(X0) != iProver_top
% 7.77/1.51      | v1_funct_1(X0) != iProver_top
% 7.77/1.51      | v1_relat_1(X0) != iProver_top ),
% 7.77/1.51      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_3201,plain,
% 7.77/1.51      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 7.77/1.51      | v1_funct_1(sK2) != iProver_top
% 7.77/1.51      | v1_relat_1(sK2) != iProver_top ),
% 7.77/1.51      inference(superposition,[status(thm)],[c_1261,c_1276]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_2299,plain,
% 7.77/1.51      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 7.77/1.51      inference(superposition,[status(thm)],[c_1257,c_1272]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_2300,plain,
% 7.77/1.51      ( k2_relat_1(sK2) = sK1 ),
% 7.77/1.51      inference(light_normalisation,[status(thm)],[c_2299,c_33]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_3202,plain,
% 7.77/1.51      ( k1_relat_1(k2_funct_1(sK2)) = sK1
% 7.77/1.51      | v1_funct_1(sK2) != iProver_top
% 7.77/1.51      | v1_relat_1(sK2) != iProver_top ),
% 7.77/1.51      inference(light_normalisation,[status(thm)],[c_3201,c_2300]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_3310,plain,
% 7.77/1.51      ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
% 7.77/1.51      inference(global_propositional_subsumption,
% 7.77/1.51                [status(thm)],
% 7.77/1.51                [c_3202,c_40,c_2254]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_3377,plain,
% 7.77/1.51      ( k5_relat_1(k6_partfun1(sK1),k2_funct_1(sK2)) = k2_funct_1(sK2)
% 7.77/1.51      | v1_relat_1(sK2) != iProver_top ),
% 7.77/1.51      inference(light_normalisation,[status(thm)],[c_3376,c_3310]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_3465,plain,
% 7.77/1.51      ( k5_relat_1(k6_partfun1(sK1),k2_funct_1(sK2)) = k2_funct_1(sK2) ),
% 7.77/1.51      inference(global_propositional_subsumption,
% 7.77/1.51                [status(thm)],
% 7.77/1.51                [c_3377,c_2254]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_19380,plain,
% 7.77/1.51      ( k2_funct_1(sK2) = sK3 ),
% 7.77/1.51      inference(demodulation,[status(thm)],[c_19178,c_3465]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(c_28,negated_conjecture,
% 7.77/1.51      ( k2_funct_1(sK2) != sK3 ),
% 7.77/1.51      inference(cnf_transformation,[],[f92]) ).
% 7.77/1.51  
% 7.77/1.51  cnf(contradiction,plain,
% 7.77/1.51      ( $false ),
% 7.77/1.51      inference(minisat,[status(thm)],[c_19380,c_28]) ).
% 7.77/1.51  
% 7.77/1.51  
% 7.77/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.77/1.51  
% 7.77/1.51  ------                               Statistics
% 7.77/1.51  
% 7.77/1.51  ------ General
% 7.77/1.51  
% 7.77/1.51  abstr_ref_over_cycles:                  0
% 7.77/1.51  abstr_ref_under_cycles:                 0
% 7.77/1.51  gc_basic_clause_elim:                   0
% 7.77/1.51  forced_gc_time:                         0
% 7.77/1.51  parsing_time:                           0.013
% 7.77/1.51  unif_index_cands_time:                  0.
% 7.77/1.51  unif_index_add_time:                    0.
% 7.77/1.51  orderings_time:                         0.
% 7.77/1.51  out_proof_time:                         0.022
% 7.77/1.51  total_time:                             0.89
% 7.77/1.51  num_of_symbols:                         51
% 7.77/1.51  num_of_terms:                           30333
% 7.77/1.51  
% 7.77/1.51  ------ Preprocessing
% 7.77/1.51  
% 7.77/1.51  num_of_splits:                          0
% 7.77/1.51  num_of_split_atoms:                     0
% 7.77/1.51  num_of_reused_defs:                     0
% 7.77/1.51  num_eq_ax_congr_red:                    0
% 7.77/1.51  num_of_sem_filtered_clauses:            1
% 7.77/1.51  num_of_subtypes:                        0
% 7.77/1.51  monotx_restored_types:                  0
% 7.77/1.51  sat_num_of_epr_types:                   0
% 7.77/1.51  sat_num_of_non_cyclic_types:            0
% 7.77/1.51  sat_guarded_non_collapsed_types:        0
% 7.77/1.51  num_pure_diseq_elim:                    0
% 7.77/1.51  simp_replaced_by:                       0
% 7.77/1.51  res_preprocessed:                       190
% 7.77/1.51  prep_upred:                             0
% 7.77/1.51  prep_unflattend:                        12
% 7.77/1.51  smt_new_axioms:                         0
% 7.77/1.51  pred_elim_cands:                        5
% 7.77/1.51  pred_elim:                              1
% 7.77/1.51  pred_elim_cl:                           1
% 7.77/1.51  pred_elim_cycles:                       3
% 7.77/1.51  merged_defs:                            0
% 7.77/1.51  merged_defs_ncl:                        0
% 7.77/1.51  bin_hyper_res:                          0
% 7.77/1.51  prep_cycles:                            4
% 7.77/1.51  pred_elim_time:                         0.006
% 7.77/1.51  splitting_time:                         0.
% 7.77/1.51  sem_filter_time:                        0.
% 7.77/1.51  monotx_time:                            0.001
% 7.77/1.51  subtype_inf_time:                       0.
% 7.77/1.51  
% 7.77/1.51  ------ Problem properties
% 7.77/1.51  
% 7.77/1.51  clauses:                                39
% 7.77/1.51  conjectures:                            11
% 7.77/1.51  epr:                                    7
% 7.77/1.51  horn:                                   35
% 7.77/1.51  ground:                                 12
% 7.77/1.51  unary:                                  14
% 7.77/1.51  binary:                                 5
% 7.77/1.51  lits:                                   147
% 7.77/1.51  lits_eq:                                34
% 7.77/1.51  fd_pure:                                0
% 7.77/1.51  fd_pseudo:                              0
% 7.77/1.51  fd_cond:                                4
% 7.77/1.51  fd_pseudo_cond:                         0
% 7.77/1.51  ac_symbols:                             0
% 7.77/1.51  
% 7.77/1.51  ------ Propositional Solver
% 7.77/1.51  
% 7.77/1.51  prop_solver_calls:                      32
% 7.77/1.51  prop_fast_solver_calls:                 2554
% 7.77/1.51  smt_solver_calls:                       0
% 7.77/1.51  smt_fast_solver_calls:                  0
% 7.77/1.51  prop_num_of_clauses:                    10928
% 7.77/1.51  prop_preprocess_simplified:             21026
% 7.77/1.51  prop_fo_subsumed:                       208
% 7.77/1.51  prop_solver_time:                       0.
% 7.77/1.51  smt_solver_time:                        0.
% 7.77/1.51  smt_fast_solver_time:                   0.
% 7.77/1.51  prop_fast_solver_time:                  0.
% 7.77/1.51  prop_unsat_core_time:                   0.001
% 7.77/1.51  
% 7.77/1.51  ------ QBF
% 7.77/1.51  
% 7.77/1.51  qbf_q_res:                              0
% 7.77/1.51  qbf_num_tautologies:                    0
% 7.77/1.51  qbf_prep_cycles:                        0
% 7.77/1.51  
% 7.77/1.51  ------ BMC1
% 7.77/1.51  
% 7.77/1.51  bmc1_current_bound:                     -1
% 7.77/1.51  bmc1_last_solved_bound:                 -1
% 7.77/1.51  bmc1_unsat_core_size:                   -1
% 7.77/1.51  bmc1_unsat_core_parents_size:           -1
% 7.77/1.51  bmc1_merge_next_fun:                    0
% 7.77/1.51  bmc1_unsat_core_clauses_time:           0.
% 7.77/1.51  
% 7.77/1.51  ------ Instantiation
% 7.77/1.51  
% 7.77/1.51  inst_num_of_clauses:                    2633
% 7.77/1.51  inst_num_in_passive:                    764
% 7.77/1.51  inst_num_in_active:                     1553
% 7.77/1.51  inst_num_in_unprocessed:                316
% 7.77/1.51  inst_num_of_loops:                      1760
% 7.77/1.51  inst_num_of_learning_restarts:          0
% 7.77/1.51  inst_num_moves_active_passive:          205
% 7.77/1.51  inst_lit_activity:                      0
% 7.77/1.51  inst_lit_activity_moves:                2
% 7.77/1.51  inst_num_tautologies:                   0
% 7.77/1.51  inst_num_prop_implied:                  0
% 7.77/1.51  inst_num_existing_simplified:           0
% 7.77/1.51  inst_num_eq_res_simplified:             0
% 7.77/1.51  inst_num_child_elim:                    0
% 7.77/1.51  inst_num_of_dismatching_blockings:      249
% 7.77/1.51  inst_num_of_non_proper_insts:           1985
% 7.77/1.51  inst_num_of_duplicates:                 0
% 7.77/1.51  inst_inst_num_from_inst_to_res:         0
% 7.77/1.51  inst_dismatching_checking_time:         0.
% 7.77/1.51  
% 7.77/1.51  ------ Resolution
% 7.77/1.51  
% 7.77/1.51  res_num_of_clauses:                     0
% 7.77/1.51  res_num_in_passive:                     0
% 7.77/1.51  res_num_in_active:                      0
% 7.77/1.51  res_num_of_loops:                       194
% 7.77/1.51  res_forward_subset_subsumed:            152
% 7.77/1.51  res_backward_subset_subsumed:           0
% 7.77/1.51  res_forward_subsumed:                   0
% 7.77/1.51  res_backward_subsumed:                  0
% 7.77/1.51  res_forward_subsumption_resolution:     2
% 7.77/1.51  res_backward_subsumption_resolution:    0
% 7.77/1.51  res_clause_to_clause_subsumption:       1818
% 7.77/1.51  res_orphan_elimination:                 0
% 7.77/1.51  res_tautology_del:                      62
% 7.77/1.51  res_num_eq_res_simplified:              1
% 7.77/1.51  res_num_sel_changes:                    0
% 7.77/1.51  res_moves_from_active_to_pass:          0
% 7.77/1.51  
% 7.77/1.51  ------ Superposition
% 7.77/1.51  
% 7.77/1.51  sup_time_total:                         0.
% 7.77/1.51  sup_time_generating:                    0.
% 7.77/1.51  sup_time_sim_full:                      0.
% 7.77/1.51  sup_time_sim_immed:                     0.
% 7.77/1.51  
% 7.77/1.51  sup_num_of_clauses:                     731
% 7.77/1.51  sup_num_in_active:                      286
% 7.77/1.51  sup_num_in_passive:                     445
% 7.77/1.51  sup_num_of_loops:                       350
% 7.77/1.51  sup_fw_superposition:                   610
% 7.77/1.51  sup_bw_superposition:                   153
% 7.77/1.51  sup_immediate_simplified:               205
% 7.77/1.51  sup_given_eliminated:                   0
% 7.77/1.51  comparisons_done:                       0
% 7.77/1.51  comparisons_avoided:                    4
% 7.77/1.51  
% 7.77/1.51  ------ Simplifications
% 7.77/1.51  
% 7.77/1.51  
% 7.77/1.51  sim_fw_subset_subsumed:                 14
% 7.77/1.51  sim_bw_subset_subsumed:                 16
% 7.77/1.51  sim_fw_subsumed:                        13
% 7.77/1.51  sim_bw_subsumed:                        4
% 7.77/1.51  sim_fw_subsumption_res:                 0
% 7.77/1.51  sim_bw_subsumption_res:                 0
% 7.77/1.51  sim_tautology_del:                      4
% 7.77/1.51  sim_eq_tautology_del:                   17
% 7.77/1.51  sim_eq_res_simp:                        0
% 7.77/1.51  sim_fw_demodulated:                     22
% 7.77/1.51  sim_bw_demodulated:                     56
% 7.77/1.51  sim_light_normalised:                   174
% 7.77/1.51  sim_joinable_taut:                      0
% 7.77/1.51  sim_joinable_simp:                      0
% 7.77/1.51  sim_ac_normalised:                      0
% 7.77/1.51  sim_smt_subsumption:                    0
% 7.77/1.51  
%------------------------------------------------------------------------------
