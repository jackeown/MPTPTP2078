%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:01 EST 2020

% Result     : Theorem 23.66s
% Output     : CNFRefutation 23.66s
% Verified   : 
% Statistics : Number of formulae       :  193 ( 719 expanded)
%              Number of clauses        :  118 ( 222 expanded)
%              Number of leaves         :   18 ( 175 expanded)
%              Depth                    :   23
%              Number of atoms          :  642 (5782 expanded)
%              Number of equality atoms :  280 (2071 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
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

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f41,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f45,plain,(
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

fof(f44,plain,
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

fof(f46,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f42,f45,f44])).

fof(f73,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f46])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f14,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_partfun1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f50,f65])).

fof(f70,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f46])).

fof(f68,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f51,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f69,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f15,axiom,(
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

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f76,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f74,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f46])).

fof(f78,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f46])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f37])).

fof(f64,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f71,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f33])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f75,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f46])).

fof(f12,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f63,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f35])).

fof(f62,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f49,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f80,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f49,f65])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f28,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f54,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f30,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f55,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f83,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f55,f65])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f79,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_729,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_1161,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_729])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_738,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | v1_relat_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1156,plain,
    ( m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_relat_1(X0_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_738])).

cnf(c_1758,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1161,c_1156])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_partfun1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_741,plain,
    ( ~ v1_relat_1(X0_50)
    | k5_relat_1(k6_partfun1(X0_51),X0_50) = k7_relat_1(X0_50,X0_51) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1153,plain,
    ( k5_relat_1(k6_partfun1(X0_51),X0_50) = k7_relat_1(X0_50,X0_51)
    | v1_relat_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_741])).

cnf(c_1924,plain,
    ( k5_relat_1(k6_partfun1(X0_51),sK3) = k7_relat_1(sK3,X0_51) ),
    inference(superposition,[status(thm)],[c_1758,c_1153])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_727,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_1163,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_727])).

cnf(c_1759,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1163,c_1156])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_726,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_1164,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_726])).

cnf(c_5,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_739,plain,
    ( ~ v1_funct_1(X0_50)
    | ~ v1_relat_1(X0_50)
    | v1_relat_1(k2_funct_1(X0_50)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1155,plain,
    ( v1_funct_1(X0_50) != iProver_top
    | v1_relat_1(X0_50) != iProver_top
    | v1_relat_1(k2_funct_1(X0_50)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_739])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k5_relat_1(k5_relat_1(X2,X0),X1) = k5_relat_1(X2,k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_743,plain,
    ( ~ v1_relat_1(X0_50)
    | ~ v1_relat_1(X1_50)
    | ~ v1_relat_1(X2_50)
    | k5_relat_1(k5_relat_1(X2_50,X0_50),X1_50) = k5_relat_1(X2_50,k5_relat_1(X0_50,X1_50)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1151,plain,
    ( k5_relat_1(k5_relat_1(X0_50,X1_50),X2_50) = k5_relat_1(X0_50,k5_relat_1(X1_50,X2_50))
    | v1_relat_1(X1_50) != iProver_top
    | v1_relat_1(X2_50) != iProver_top
    | v1_relat_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_743])).

cnf(c_1867,plain,
    ( k5_relat_1(k2_funct_1(X0_50),k5_relat_1(X1_50,X2_50)) = k5_relat_1(k5_relat_1(k2_funct_1(X0_50),X1_50),X2_50)
    | v1_funct_1(X0_50) != iProver_top
    | v1_relat_1(X0_50) != iProver_top
    | v1_relat_1(X1_50) != iProver_top
    | v1_relat_1(X2_50) != iProver_top ),
    inference(superposition,[status(thm)],[c_1155,c_1151])).

cnf(c_4217,plain,
    ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0_50),X1_50) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0_50,X1_50))
    | v1_relat_1(X0_50) != iProver_top
    | v1_relat_1(X1_50) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1164,c_1867])).

cnf(c_34,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_1215,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_738])).

cnf(c_1243,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1215])).

cnf(c_1244,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1243])).

cnf(c_4666,plain,
    ( v1_relat_1(X1_50) != iProver_top
    | v1_relat_1(X0_50) != iProver_top
    | k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0_50),X1_50) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0_50,X1_50)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4217,c_34,c_1244])).

cnf(c_4667,plain,
    ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0_50),X1_50) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0_50,X1_50))
    | v1_relat_1(X0_50) != iProver_top
    | v1_relat_1(X1_50) != iProver_top ),
    inference(renaming,[status(thm)],[c_4666])).

cnf(c_4670,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0_50)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),X0_50)
    | v1_relat_1(X0_50) != iProver_top ),
    inference(superposition,[status(thm)],[c_1759,c_4667])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_23,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_385,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_23])).

cnf(c_386,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(X1)
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_385])).

cnf(c_390,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_relset_1(X0,X1,sK2) != X1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(X1)
    | k1_xboole_0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_386,c_31])).

cnf(c_391,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_relset_1(X0,X1,sK2) != X1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(X1)
    | k1_xboole_0 = X1 ),
    inference(renaming,[status(thm)],[c_390])).

cnf(c_532,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_relset_1(X0,X1,sK2) != X1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(X1)
    | sK0 != X0
    | sK1 != X1
    | sK2 != sK2
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_391])).

cnf(c_533,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k2_relset_1(sK0,sK1,sK2) != sK1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_532])).

cnf(c_25,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_21,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_535,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_533,c_29,c_25,c_21])).

cnf(c_717,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(subtyping,[status(esa)],[c_535])).

cnf(c_4676,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0_50)) = k5_relat_1(k6_partfun1(sK1),X0_50)
    | v1_relat_1(X0_50) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4670,c_717])).

cnf(c_4795,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
    inference(superposition,[status(thm)],[c_1758,c_4676])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_734,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51)))
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(X1_50)
    | k1_partfun1(X2_51,X3_51,X0_51,X1_51,X1_50,X0_50) = k5_relat_1(X1_50,X0_50) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1160,plain,
    ( k1_partfun1(X0_51,X1_51,X2_51,X3_51,X0_50,X1_50) = k5_relat_1(X0_50,X1_50)
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51))) != iProver_top
    | v1_funct_1(X1_50) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_734])).

cnf(c_2217,plain,
    ( k1_partfun1(X0_51,X1_51,sK1,sK0,X0_50,sK3) = k5_relat_1(X0_50,sK3)
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1161,c_1160])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_35,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2435,plain,
    ( v1_funct_1(X0_50) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | k1_partfun1(X0_51,X1_51,sK1,sK0,X0_50,sK3) = k5_relat_1(X0_50,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2217,c_35])).

cnf(c_2436,plain,
    ( k1_partfun1(X0_51,X1_51,sK1,sK0,X0_50,sK3) = k5_relat_1(X0_50,sK3)
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(renaming,[status(thm)],[c_2435])).

cnf(c_2442,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1163,c_2436])).

cnf(c_13,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_24,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_341,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_24])).

cnf(c_342,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_341])).

cnf(c_16,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_50,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_344,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_342,c_50])).

cnf(c_724,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_344])).

cnf(c_1166,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_724])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_737,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51)))
    | m1_subset_1(k1_partfun1(X2_51,X3_51,X0_51,X1_51,X1_50,X0_50),k1_zfmisc_1(k2_zfmisc_1(X2_51,X1_51)))
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(X1_50) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1227,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_737])).

cnf(c_1597,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1166,c_31,c_29,c_28,c_26,c_724,c_1227])).

cnf(c_2450,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2442,c_1597])).

cnf(c_32,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_2796,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2450,c_32])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_742,plain,
    ( ~ v1_relat_1(X0_50)
    | k5_relat_1(X0_50,k6_partfun1(k2_relat_1(X0_50))) = X0_50 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1152,plain,
    ( k5_relat_1(X0_50,k6_partfun1(k2_relat_1(X0_50))) = X0_50
    | v1_relat_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_742])).

cnf(c_1770,plain,
    ( k5_relat_1(k2_funct_1(X0_50),k6_partfun1(k2_relat_1(k2_funct_1(X0_50)))) = k2_funct_1(X0_50)
    | v1_funct_1(X0_50) != iProver_top
    | v1_relat_1(X0_50) != iProver_top ),
    inference(superposition,[status(thm)],[c_1155,c_1152])).

cnf(c_3424,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(k2_relat_1(k2_funct_1(sK2)))) = k2_funct_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1164,c_1770])).

cnf(c_6,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_454,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_23])).

cnf(c_455,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_454])).

cnf(c_457,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_455,c_31])).

cnf(c_720,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_457])).

cnf(c_1170,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_720])).

cnf(c_1486,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1170,c_29,c_720,c_1243])).

cnf(c_9,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_412,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_23])).

cnf(c_413,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
    inference(unflattening,[status(thm)],[c_412])).

cnf(c_415,plain,
    ( ~ v1_relat_1(sK2)
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_413,c_31])).

cnf(c_723,plain,
    ( ~ v1_relat_1(sK2)
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
    inference(subtyping,[status(esa)],[c_415])).

cnf(c_1167,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_723])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_358,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_23])).

cnf(c_359,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_358])).

cnf(c_363,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_relset_1(X0,X1,sK2) != X1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_359,c_31])).

cnf(c_364,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_relset_1(X0,X1,sK2) != X1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1 ),
    inference(renaming,[status(thm)],[c_363])).

cnf(c_540,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_relset_1(X0,X1,sK2) != X1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
    | sK0 != X0
    | sK1 != X1
    | sK2 != sK2
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_364])).

cnf(c_541,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k2_relset_1(sK0,sK1,sK2) != sK1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_540])).

cnf(c_543,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_541,c_29,c_25,c_21])).

cnf(c_716,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
    inference(subtyping,[status(esa)],[c_543])).

cnf(c_1173,plain,
    ( k6_partfun1(k1_relat_1(sK2)) = k6_partfun1(sK0)
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1167,c_716])).

cnf(c_1190,plain,
    ( ~ v1_relat_1(sK2)
    | k6_partfun1(k1_relat_1(sK2)) = k6_partfun1(sK0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1173])).

cnf(c_1489,plain,
    ( k6_partfun1(k1_relat_1(sK2)) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1173,c_29,c_1190,c_1243])).

cnf(c_3427,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k2_funct_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3424,c_1486,c_1489])).

cnf(c_3762,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3427,c_34,c_1244])).

cnf(c_4802,plain,
    ( k5_relat_1(k6_partfun1(sK1),sK3) = k2_funct_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_4795,c_2796,c_3762])).

cnf(c_83878,plain,
    ( k7_relat_1(sK3,sK1) = k2_funct_1(sK2) ),
    inference(superposition,[status(thm)],[c_1924,c_4802])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v4_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_0,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_319,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_11,c_0])).

cnf(c_323,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_319,c_11,c_10,c_0])).

cnf(c_725,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | k7_relat_1(X0_50,X0_51) = X0_50 ),
    inference(subtyping,[status(esa)],[c_323])).

cnf(c_1165,plain,
    ( k7_relat_1(X0_50,X0_51) = X0_50
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_725])).

cnf(c_2800,plain,
    ( k7_relat_1(sK3,sK1) = sK3 ),
    inference(superposition,[status(thm)],[c_1161,c_1165])).

cnf(c_83880,plain,
    ( k2_funct_1(sK2) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_83878,c_2800])).

cnf(c_20,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_733,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_83880,c_733])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:23:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  % Running in FOF mode
% 23.66/3.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.66/3.49  
% 23.66/3.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.66/3.49  
% 23.66/3.49  ------  iProver source info
% 23.66/3.49  
% 23.66/3.49  git: date: 2020-06-30 10:37:57 +0100
% 23.66/3.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.66/3.49  git: non_committed_changes: false
% 23.66/3.49  git: last_make_outside_of_git: false
% 23.66/3.49  
% 23.66/3.49  ------ 
% 23.66/3.49  
% 23.66/3.49  ------ Input Options
% 23.66/3.49  
% 23.66/3.49  --out_options                           all
% 23.66/3.49  --tptp_safe_out                         true
% 23.66/3.49  --problem_path                          ""
% 23.66/3.49  --include_path                          ""
% 23.66/3.49  --clausifier                            res/vclausify_rel
% 23.66/3.49  --clausifier_options                    ""
% 23.66/3.49  --stdin                                 false
% 23.66/3.49  --stats_out                             all
% 23.66/3.49  
% 23.66/3.49  ------ General Options
% 23.66/3.49  
% 23.66/3.49  --fof                                   false
% 23.66/3.49  --time_out_real                         305.
% 23.66/3.49  --time_out_virtual                      -1.
% 23.66/3.49  --symbol_type_check                     false
% 23.66/3.49  --clausify_out                          false
% 23.66/3.49  --sig_cnt_out                           false
% 23.66/3.49  --trig_cnt_out                          false
% 23.66/3.49  --trig_cnt_out_tolerance                1.
% 23.66/3.49  --trig_cnt_out_sk_spl                   false
% 23.66/3.49  --abstr_cl_out                          false
% 23.66/3.49  
% 23.66/3.49  ------ Global Options
% 23.66/3.49  
% 23.66/3.49  --schedule                              default
% 23.66/3.49  --add_important_lit                     false
% 23.66/3.49  --prop_solver_per_cl                    1000
% 23.66/3.49  --min_unsat_core                        false
% 23.66/3.49  --soft_assumptions                      false
% 23.66/3.49  --soft_lemma_size                       3
% 23.66/3.49  --prop_impl_unit_size                   0
% 23.66/3.49  --prop_impl_unit                        []
% 23.66/3.49  --share_sel_clauses                     true
% 23.66/3.49  --reset_solvers                         false
% 23.66/3.49  --bc_imp_inh                            [conj_cone]
% 23.66/3.49  --conj_cone_tolerance                   3.
% 23.66/3.49  --extra_neg_conj                        none
% 23.66/3.49  --large_theory_mode                     true
% 23.66/3.49  --prolific_symb_bound                   200
% 23.66/3.49  --lt_threshold                          2000
% 23.66/3.49  --clause_weak_htbl                      true
% 23.66/3.49  --gc_record_bc_elim                     false
% 23.66/3.49  
% 23.66/3.49  ------ Preprocessing Options
% 23.66/3.49  
% 23.66/3.49  --preprocessing_flag                    true
% 23.66/3.49  --time_out_prep_mult                    0.1
% 23.66/3.49  --splitting_mode                        input
% 23.66/3.49  --splitting_grd                         true
% 23.66/3.49  --splitting_cvd                         false
% 23.66/3.49  --splitting_cvd_svl                     false
% 23.66/3.49  --splitting_nvd                         32
% 23.66/3.49  --sub_typing                            true
% 23.66/3.49  --prep_gs_sim                           true
% 23.66/3.49  --prep_unflatten                        true
% 23.66/3.49  --prep_res_sim                          true
% 23.66/3.49  --prep_upred                            true
% 23.66/3.49  --prep_sem_filter                       exhaustive
% 23.66/3.49  --prep_sem_filter_out                   false
% 23.66/3.49  --pred_elim                             true
% 23.66/3.49  --res_sim_input                         true
% 23.66/3.49  --eq_ax_congr_red                       true
% 23.66/3.49  --pure_diseq_elim                       true
% 23.66/3.49  --brand_transform                       false
% 23.66/3.49  --non_eq_to_eq                          false
% 23.66/3.49  --prep_def_merge                        true
% 23.66/3.49  --prep_def_merge_prop_impl              false
% 23.66/3.49  --prep_def_merge_mbd                    true
% 23.66/3.49  --prep_def_merge_tr_red                 false
% 23.66/3.49  --prep_def_merge_tr_cl                  false
% 23.66/3.49  --smt_preprocessing                     true
% 23.66/3.49  --smt_ac_axioms                         fast
% 23.66/3.49  --preprocessed_out                      false
% 23.66/3.49  --preprocessed_stats                    false
% 23.66/3.49  
% 23.66/3.49  ------ Abstraction refinement Options
% 23.66/3.49  
% 23.66/3.49  --abstr_ref                             []
% 23.66/3.49  --abstr_ref_prep                        false
% 23.66/3.49  --abstr_ref_until_sat                   false
% 23.66/3.49  --abstr_ref_sig_restrict                funpre
% 23.66/3.49  --abstr_ref_af_restrict_to_split_sk     false
% 23.66/3.49  --abstr_ref_under                       []
% 23.66/3.49  
% 23.66/3.49  ------ SAT Options
% 23.66/3.49  
% 23.66/3.49  --sat_mode                              false
% 23.66/3.49  --sat_fm_restart_options                ""
% 23.66/3.49  --sat_gr_def                            false
% 23.66/3.49  --sat_epr_types                         true
% 23.66/3.49  --sat_non_cyclic_types                  false
% 23.66/3.49  --sat_finite_models                     false
% 23.66/3.49  --sat_fm_lemmas                         false
% 23.66/3.49  --sat_fm_prep                           false
% 23.66/3.49  --sat_fm_uc_incr                        true
% 23.66/3.49  --sat_out_model                         small
% 23.66/3.49  --sat_out_clauses                       false
% 23.66/3.49  
% 23.66/3.49  ------ QBF Options
% 23.66/3.49  
% 23.66/3.49  --qbf_mode                              false
% 23.66/3.49  --qbf_elim_univ                         false
% 23.66/3.49  --qbf_dom_inst                          none
% 23.66/3.49  --qbf_dom_pre_inst                      false
% 23.66/3.49  --qbf_sk_in                             false
% 23.66/3.49  --qbf_pred_elim                         true
% 23.66/3.49  --qbf_split                             512
% 23.66/3.49  
% 23.66/3.49  ------ BMC1 Options
% 23.66/3.49  
% 23.66/3.49  --bmc1_incremental                      false
% 23.66/3.49  --bmc1_axioms                           reachable_all
% 23.66/3.49  --bmc1_min_bound                        0
% 23.66/3.49  --bmc1_max_bound                        -1
% 23.66/3.49  --bmc1_max_bound_default                -1
% 23.66/3.49  --bmc1_symbol_reachability              true
% 23.66/3.49  --bmc1_property_lemmas                  false
% 23.66/3.49  --bmc1_k_induction                      false
% 23.66/3.49  --bmc1_non_equiv_states                 false
% 23.66/3.49  --bmc1_deadlock                         false
% 23.66/3.49  --bmc1_ucm                              false
% 23.66/3.49  --bmc1_add_unsat_core                   none
% 23.66/3.49  --bmc1_unsat_core_children              false
% 23.66/3.49  --bmc1_unsat_core_extrapolate_axioms    false
% 23.66/3.49  --bmc1_out_stat                         full
% 23.66/3.49  --bmc1_ground_init                      false
% 23.66/3.49  --bmc1_pre_inst_next_state              false
% 23.66/3.49  --bmc1_pre_inst_state                   false
% 23.66/3.49  --bmc1_pre_inst_reach_state             false
% 23.66/3.49  --bmc1_out_unsat_core                   false
% 23.66/3.49  --bmc1_aig_witness_out                  false
% 23.66/3.49  --bmc1_verbose                          false
% 23.66/3.49  --bmc1_dump_clauses_tptp                false
% 23.66/3.49  --bmc1_dump_unsat_core_tptp             false
% 23.66/3.49  --bmc1_dump_file                        -
% 23.66/3.49  --bmc1_ucm_expand_uc_limit              128
% 23.66/3.49  --bmc1_ucm_n_expand_iterations          6
% 23.66/3.49  --bmc1_ucm_extend_mode                  1
% 23.66/3.49  --bmc1_ucm_init_mode                    2
% 23.66/3.49  --bmc1_ucm_cone_mode                    none
% 23.66/3.49  --bmc1_ucm_reduced_relation_type        0
% 23.66/3.49  --bmc1_ucm_relax_model                  4
% 23.66/3.49  --bmc1_ucm_full_tr_after_sat            true
% 23.66/3.49  --bmc1_ucm_expand_neg_assumptions       false
% 23.66/3.49  --bmc1_ucm_layered_model                none
% 23.66/3.49  --bmc1_ucm_max_lemma_size               10
% 23.66/3.49  
% 23.66/3.49  ------ AIG Options
% 23.66/3.49  
% 23.66/3.49  --aig_mode                              false
% 23.66/3.49  
% 23.66/3.49  ------ Instantiation Options
% 23.66/3.49  
% 23.66/3.49  --instantiation_flag                    true
% 23.66/3.49  --inst_sos_flag                         true
% 23.66/3.49  --inst_sos_phase                        true
% 23.66/3.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.66/3.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.66/3.49  --inst_lit_sel_side                     num_symb
% 23.66/3.49  --inst_solver_per_active                1400
% 23.66/3.49  --inst_solver_calls_frac                1.
% 23.66/3.49  --inst_passive_queue_type               priority_queues
% 23.66/3.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.66/3.49  --inst_passive_queues_freq              [25;2]
% 23.66/3.49  --inst_dismatching                      true
% 23.66/3.49  --inst_eager_unprocessed_to_passive     true
% 23.66/3.49  --inst_prop_sim_given                   true
% 23.66/3.49  --inst_prop_sim_new                     false
% 23.66/3.49  --inst_subs_new                         false
% 23.66/3.49  --inst_eq_res_simp                      false
% 23.66/3.49  --inst_subs_given                       false
% 23.66/3.49  --inst_orphan_elimination               true
% 23.66/3.49  --inst_learning_loop_flag               true
% 23.66/3.49  --inst_learning_start                   3000
% 23.66/3.49  --inst_learning_factor                  2
% 23.66/3.49  --inst_start_prop_sim_after_learn       3
% 23.66/3.49  --inst_sel_renew                        solver
% 23.66/3.49  --inst_lit_activity_flag                true
% 23.66/3.49  --inst_restr_to_given                   false
% 23.66/3.49  --inst_activity_threshold               500
% 23.66/3.49  --inst_out_proof                        true
% 23.66/3.49  
% 23.66/3.49  ------ Resolution Options
% 23.66/3.49  
% 23.66/3.49  --resolution_flag                       true
% 23.66/3.49  --res_lit_sel                           adaptive
% 23.66/3.49  --res_lit_sel_side                      none
% 23.66/3.49  --res_ordering                          kbo
% 23.66/3.49  --res_to_prop_solver                    active
% 23.66/3.49  --res_prop_simpl_new                    false
% 23.66/3.49  --res_prop_simpl_given                  true
% 23.66/3.49  --res_passive_queue_type                priority_queues
% 23.66/3.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.66/3.49  --res_passive_queues_freq               [15;5]
% 23.66/3.49  --res_forward_subs                      full
% 23.66/3.49  --res_backward_subs                     full
% 23.66/3.49  --res_forward_subs_resolution           true
% 23.66/3.49  --res_backward_subs_resolution          true
% 23.66/3.49  --res_orphan_elimination                true
% 23.66/3.49  --res_time_limit                        2.
% 23.66/3.49  --res_out_proof                         true
% 23.66/3.49  
% 23.66/3.49  ------ Superposition Options
% 23.66/3.49  
% 23.66/3.49  --superposition_flag                    true
% 23.66/3.49  --sup_passive_queue_type                priority_queues
% 23.66/3.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.66/3.49  --sup_passive_queues_freq               [8;1;4]
% 23.66/3.49  --demod_completeness_check              fast
% 23.66/3.49  --demod_use_ground                      true
% 23.66/3.49  --sup_to_prop_solver                    passive
% 23.66/3.49  --sup_prop_simpl_new                    true
% 23.66/3.49  --sup_prop_simpl_given                  true
% 23.66/3.49  --sup_fun_splitting                     true
% 23.66/3.49  --sup_smt_interval                      50000
% 23.66/3.49  
% 23.66/3.49  ------ Superposition Simplification Setup
% 23.66/3.49  
% 23.66/3.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 23.66/3.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 23.66/3.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 23.66/3.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 23.66/3.49  --sup_full_triv                         [TrivRules;PropSubs]
% 23.66/3.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 23.66/3.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 23.66/3.49  --sup_immed_triv                        [TrivRules]
% 23.66/3.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.66/3.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.66/3.49  --sup_immed_bw_main                     []
% 23.66/3.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 23.66/3.49  --sup_input_triv                        [Unflattening;TrivRules]
% 23.66/3.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.66/3.49  --sup_input_bw                          []
% 23.66/3.49  
% 23.66/3.49  ------ Combination Options
% 23.66/3.49  
% 23.66/3.49  --comb_res_mult                         3
% 23.66/3.49  --comb_sup_mult                         2
% 23.66/3.49  --comb_inst_mult                        10
% 23.66/3.49  
% 23.66/3.49  ------ Debug Options
% 23.66/3.49  
% 23.66/3.49  --dbg_backtrace                         false
% 23.66/3.49  --dbg_dump_prop_clauses                 false
% 23.66/3.49  --dbg_dump_prop_clauses_file            -
% 23.66/3.49  --dbg_out_stat                          false
% 23.66/3.49  ------ Parsing...
% 23.66/3.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.66/3.49  
% 23.66/3.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 23.66/3.49  
% 23.66/3.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.66/3.49  
% 23.66/3.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.66/3.49  ------ Proving...
% 23.66/3.49  ------ Problem Properties 
% 23.66/3.49  
% 23.66/3.49  
% 23.66/3.49  clauses                                 28
% 23.66/3.49  conjectures                             8
% 23.66/3.49  EPR                                     4
% 23.66/3.49  Horn                                    28
% 23.66/3.49  unary                                   11
% 23.66/3.49  binary                                  9
% 23.66/3.49  lits                                    62
% 23.66/3.49  lits eq                                 22
% 23.66/3.49  fd_pure                                 0
% 23.66/3.49  fd_pseudo                               0
% 23.66/3.49  fd_cond                                 0
% 23.66/3.49  fd_pseudo_cond                          0
% 23.66/3.49  AC symbols                              0
% 23.66/3.49  
% 23.66/3.49  ------ Schedule dynamic 5 is on 
% 23.66/3.49  
% 23.66/3.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 23.66/3.49  
% 23.66/3.49  
% 23.66/3.49  ------ 
% 23.66/3.49  Current options:
% 23.66/3.49  ------ 
% 23.66/3.49  
% 23.66/3.49  ------ Input Options
% 23.66/3.49  
% 23.66/3.49  --out_options                           all
% 23.66/3.49  --tptp_safe_out                         true
% 23.66/3.49  --problem_path                          ""
% 23.66/3.49  --include_path                          ""
% 23.66/3.49  --clausifier                            res/vclausify_rel
% 23.66/3.49  --clausifier_options                    ""
% 23.66/3.49  --stdin                                 false
% 23.66/3.49  --stats_out                             all
% 23.66/3.49  
% 23.66/3.49  ------ General Options
% 23.66/3.49  
% 23.66/3.49  --fof                                   false
% 23.66/3.49  --time_out_real                         305.
% 23.66/3.49  --time_out_virtual                      -1.
% 23.66/3.49  --symbol_type_check                     false
% 23.66/3.49  --clausify_out                          false
% 23.66/3.49  --sig_cnt_out                           false
% 23.66/3.49  --trig_cnt_out                          false
% 23.66/3.49  --trig_cnt_out_tolerance                1.
% 23.66/3.49  --trig_cnt_out_sk_spl                   false
% 23.66/3.49  --abstr_cl_out                          false
% 23.66/3.49  
% 23.66/3.49  ------ Global Options
% 23.66/3.49  
% 23.66/3.49  --schedule                              default
% 23.66/3.49  --add_important_lit                     false
% 23.66/3.49  --prop_solver_per_cl                    1000
% 23.66/3.49  --min_unsat_core                        false
% 23.66/3.49  --soft_assumptions                      false
% 23.66/3.49  --soft_lemma_size                       3
% 23.66/3.49  --prop_impl_unit_size                   0
% 23.66/3.49  --prop_impl_unit                        []
% 23.66/3.49  --share_sel_clauses                     true
% 23.66/3.49  --reset_solvers                         false
% 23.66/3.49  --bc_imp_inh                            [conj_cone]
% 23.66/3.49  --conj_cone_tolerance                   3.
% 23.66/3.49  --extra_neg_conj                        none
% 23.66/3.49  --large_theory_mode                     true
% 23.66/3.49  --prolific_symb_bound                   200
% 23.66/3.49  --lt_threshold                          2000
% 23.66/3.49  --clause_weak_htbl                      true
% 23.66/3.49  --gc_record_bc_elim                     false
% 23.66/3.49  
% 23.66/3.49  ------ Preprocessing Options
% 23.66/3.49  
% 23.66/3.49  --preprocessing_flag                    true
% 23.66/3.49  --time_out_prep_mult                    0.1
% 23.66/3.49  --splitting_mode                        input
% 23.66/3.49  --splitting_grd                         true
% 23.66/3.49  --splitting_cvd                         false
% 23.66/3.49  --splitting_cvd_svl                     false
% 23.66/3.49  --splitting_nvd                         32
% 23.66/3.49  --sub_typing                            true
% 23.66/3.49  --prep_gs_sim                           true
% 23.66/3.49  --prep_unflatten                        true
% 23.66/3.49  --prep_res_sim                          true
% 23.66/3.49  --prep_upred                            true
% 23.66/3.49  --prep_sem_filter                       exhaustive
% 23.66/3.49  --prep_sem_filter_out                   false
% 23.66/3.49  --pred_elim                             true
% 23.66/3.49  --res_sim_input                         true
% 23.66/3.49  --eq_ax_congr_red                       true
% 23.66/3.49  --pure_diseq_elim                       true
% 23.66/3.49  --brand_transform                       false
% 23.66/3.49  --non_eq_to_eq                          false
% 23.66/3.49  --prep_def_merge                        true
% 23.66/3.49  --prep_def_merge_prop_impl              false
% 23.66/3.49  --prep_def_merge_mbd                    true
% 23.66/3.49  --prep_def_merge_tr_red                 false
% 23.66/3.49  --prep_def_merge_tr_cl                  false
% 23.66/3.49  --smt_preprocessing                     true
% 23.66/3.49  --smt_ac_axioms                         fast
% 23.66/3.49  --preprocessed_out                      false
% 23.66/3.49  --preprocessed_stats                    false
% 23.66/3.49  
% 23.66/3.49  ------ Abstraction refinement Options
% 23.66/3.49  
% 23.66/3.49  --abstr_ref                             []
% 23.66/3.49  --abstr_ref_prep                        false
% 23.66/3.49  --abstr_ref_until_sat                   false
% 23.66/3.49  --abstr_ref_sig_restrict                funpre
% 23.66/3.49  --abstr_ref_af_restrict_to_split_sk     false
% 23.66/3.49  --abstr_ref_under                       []
% 23.66/3.49  
% 23.66/3.49  ------ SAT Options
% 23.66/3.49  
% 23.66/3.49  --sat_mode                              false
% 23.66/3.49  --sat_fm_restart_options                ""
% 23.66/3.49  --sat_gr_def                            false
% 23.66/3.49  --sat_epr_types                         true
% 23.66/3.49  --sat_non_cyclic_types                  false
% 23.66/3.49  --sat_finite_models                     false
% 23.66/3.49  --sat_fm_lemmas                         false
% 23.66/3.49  --sat_fm_prep                           false
% 23.66/3.49  --sat_fm_uc_incr                        true
% 23.66/3.49  --sat_out_model                         small
% 23.66/3.49  --sat_out_clauses                       false
% 23.66/3.49  
% 23.66/3.49  ------ QBF Options
% 23.66/3.49  
% 23.66/3.49  --qbf_mode                              false
% 23.66/3.49  --qbf_elim_univ                         false
% 23.66/3.49  --qbf_dom_inst                          none
% 23.66/3.49  --qbf_dom_pre_inst                      false
% 23.66/3.49  --qbf_sk_in                             false
% 23.66/3.49  --qbf_pred_elim                         true
% 23.66/3.49  --qbf_split                             512
% 23.66/3.49  
% 23.66/3.49  ------ BMC1 Options
% 23.66/3.49  
% 23.66/3.49  --bmc1_incremental                      false
% 23.66/3.49  --bmc1_axioms                           reachable_all
% 23.66/3.49  --bmc1_min_bound                        0
% 23.66/3.49  --bmc1_max_bound                        -1
% 23.66/3.49  --bmc1_max_bound_default                -1
% 23.66/3.49  --bmc1_symbol_reachability              true
% 23.66/3.49  --bmc1_property_lemmas                  false
% 23.66/3.49  --bmc1_k_induction                      false
% 23.66/3.49  --bmc1_non_equiv_states                 false
% 23.66/3.49  --bmc1_deadlock                         false
% 23.66/3.49  --bmc1_ucm                              false
% 23.66/3.49  --bmc1_add_unsat_core                   none
% 23.66/3.49  --bmc1_unsat_core_children              false
% 23.66/3.49  --bmc1_unsat_core_extrapolate_axioms    false
% 23.66/3.49  --bmc1_out_stat                         full
% 23.66/3.49  --bmc1_ground_init                      false
% 23.66/3.49  --bmc1_pre_inst_next_state              false
% 23.66/3.49  --bmc1_pre_inst_state                   false
% 23.66/3.49  --bmc1_pre_inst_reach_state             false
% 23.66/3.49  --bmc1_out_unsat_core                   false
% 23.66/3.49  --bmc1_aig_witness_out                  false
% 23.66/3.49  --bmc1_verbose                          false
% 23.66/3.49  --bmc1_dump_clauses_tptp                false
% 23.66/3.49  --bmc1_dump_unsat_core_tptp             false
% 23.66/3.49  --bmc1_dump_file                        -
% 23.66/3.49  --bmc1_ucm_expand_uc_limit              128
% 23.66/3.49  --bmc1_ucm_n_expand_iterations          6
% 23.66/3.49  --bmc1_ucm_extend_mode                  1
% 23.66/3.49  --bmc1_ucm_init_mode                    2
% 23.66/3.49  --bmc1_ucm_cone_mode                    none
% 23.66/3.49  --bmc1_ucm_reduced_relation_type        0
% 23.66/3.49  --bmc1_ucm_relax_model                  4
% 23.66/3.49  --bmc1_ucm_full_tr_after_sat            true
% 23.66/3.49  --bmc1_ucm_expand_neg_assumptions       false
% 23.66/3.49  --bmc1_ucm_layered_model                none
% 23.66/3.49  --bmc1_ucm_max_lemma_size               10
% 23.66/3.49  
% 23.66/3.49  ------ AIG Options
% 23.66/3.49  
% 23.66/3.49  --aig_mode                              false
% 23.66/3.49  
% 23.66/3.49  ------ Instantiation Options
% 23.66/3.49  
% 23.66/3.49  --instantiation_flag                    true
% 23.66/3.49  --inst_sos_flag                         true
% 23.66/3.49  --inst_sos_phase                        true
% 23.66/3.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.66/3.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.66/3.49  --inst_lit_sel_side                     none
% 23.66/3.49  --inst_solver_per_active                1400
% 23.66/3.49  --inst_solver_calls_frac                1.
% 23.66/3.49  --inst_passive_queue_type               priority_queues
% 23.66/3.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.66/3.49  --inst_passive_queues_freq              [25;2]
% 23.66/3.49  --inst_dismatching                      true
% 23.66/3.49  --inst_eager_unprocessed_to_passive     true
% 23.66/3.49  --inst_prop_sim_given                   true
% 23.66/3.49  --inst_prop_sim_new                     false
% 23.66/3.49  --inst_subs_new                         false
% 23.66/3.49  --inst_eq_res_simp                      false
% 23.66/3.49  --inst_subs_given                       false
% 23.66/3.49  --inst_orphan_elimination               true
% 23.66/3.49  --inst_learning_loop_flag               true
% 23.66/3.49  --inst_learning_start                   3000
% 23.66/3.49  --inst_learning_factor                  2
% 23.66/3.49  --inst_start_prop_sim_after_learn       3
% 23.66/3.49  --inst_sel_renew                        solver
% 23.66/3.49  --inst_lit_activity_flag                true
% 23.66/3.49  --inst_restr_to_given                   false
% 23.66/3.49  --inst_activity_threshold               500
% 23.66/3.49  --inst_out_proof                        true
% 23.66/3.49  
% 23.66/3.49  ------ Resolution Options
% 23.66/3.49  
% 23.66/3.49  --resolution_flag                       false
% 23.66/3.49  --res_lit_sel                           adaptive
% 23.66/3.49  --res_lit_sel_side                      none
% 23.66/3.49  --res_ordering                          kbo
% 23.66/3.49  --res_to_prop_solver                    active
% 23.66/3.49  --res_prop_simpl_new                    false
% 23.66/3.49  --res_prop_simpl_given                  true
% 23.66/3.49  --res_passive_queue_type                priority_queues
% 23.66/3.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.66/3.49  --res_passive_queues_freq               [15;5]
% 23.66/3.49  --res_forward_subs                      full
% 23.66/3.49  --res_backward_subs                     full
% 23.66/3.49  --res_forward_subs_resolution           true
% 23.66/3.49  --res_backward_subs_resolution          true
% 23.66/3.49  --res_orphan_elimination                true
% 23.66/3.49  --res_time_limit                        2.
% 23.66/3.49  --res_out_proof                         true
% 23.66/3.49  
% 23.66/3.49  ------ Superposition Options
% 23.66/3.49  
% 23.66/3.49  --superposition_flag                    true
% 23.66/3.49  --sup_passive_queue_type                priority_queues
% 23.66/3.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.66/3.49  --sup_passive_queues_freq               [8;1;4]
% 23.66/3.49  --demod_completeness_check              fast
% 23.66/3.49  --demod_use_ground                      true
% 23.66/3.49  --sup_to_prop_solver                    passive
% 23.66/3.49  --sup_prop_simpl_new                    true
% 23.66/3.49  --sup_prop_simpl_given                  true
% 23.66/3.49  --sup_fun_splitting                     true
% 23.66/3.49  --sup_smt_interval                      50000
% 23.66/3.49  
% 23.66/3.49  ------ Superposition Simplification Setup
% 23.66/3.49  
% 23.66/3.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 23.66/3.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 23.66/3.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 23.66/3.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 23.66/3.49  --sup_full_triv                         [TrivRules;PropSubs]
% 23.66/3.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 23.66/3.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 23.66/3.49  --sup_immed_triv                        [TrivRules]
% 23.66/3.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.66/3.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.66/3.49  --sup_immed_bw_main                     []
% 23.66/3.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 23.66/3.49  --sup_input_triv                        [Unflattening;TrivRules]
% 23.66/3.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.66/3.49  --sup_input_bw                          []
% 23.66/3.49  
% 23.66/3.49  ------ Combination Options
% 23.66/3.49  
% 23.66/3.49  --comb_res_mult                         3
% 23.66/3.49  --comb_sup_mult                         2
% 23.66/3.49  --comb_inst_mult                        10
% 23.66/3.49  
% 23.66/3.49  ------ Debug Options
% 23.66/3.49  
% 23.66/3.49  --dbg_backtrace                         false
% 23.66/3.49  --dbg_dump_prop_clauses                 false
% 23.66/3.49  --dbg_dump_prop_clauses_file            -
% 23.66/3.49  --dbg_out_stat                          false
% 23.66/3.49  
% 23.66/3.49  
% 23.66/3.49  
% 23.66/3.49  
% 23.66/3.49  ------ Proving...
% 23.66/3.49  
% 23.66/3.49  
% 23.66/3.49  % SZS status Theorem for theBenchmark.p
% 23.66/3.49  
% 23.66/3.49  % SZS output start CNFRefutation for theBenchmark.p
% 23.66/3.49  
% 23.66/3.49  fof(f16,conjecture,(
% 23.66/3.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 23.66/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.66/3.49  
% 23.66/3.49  fof(f17,negated_conjecture,(
% 23.66/3.49    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 23.66/3.49    inference(negated_conjecture,[],[f16])).
% 23.66/3.49  
% 23.66/3.49  fof(f41,plain,(
% 23.66/3.49    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 23.66/3.49    inference(ennf_transformation,[],[f17])).
% 23.66/3.49  
% 23.66/3.49  fof(f42,plain,(
% 23.66/3.49    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 23.66/3.49    inference(flattening,[],[f41])).
% 23.66/3.49  
% 23.66/3.49  fof(f45,plain,(
% 23.66/3.49    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 23.66/3.49    introduced(choice_axiom,[])).
% 23.66/3.49  
% 23.66/3.49  fof(f44,plain,(
% 23.66/3.49    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 23.66/3.49    introduced(choice_axiom,[])).
% 23.66/3.49  
% 23.66/3.49  fof(f46,plain,(
% 23.66/3.49    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 23.66/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f42,f45,f44])).
% 23.66/3.49  
% 23.66/3.49  fof(f73,plain,(
% 23.66/3.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 23.66/3.49    inference(cnf_transformation,[],[f46])).
% 23.66/3.49  
% 23.66/3.49  fof(f8,axiom,(
% 23.66/3.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 23.66/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.66/3.49  
% 23.66/3.49  fof(f31,plain,(
% 23.66/3.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 23.66/3.49    inference(ennf_transformation,[],[f8])).
% 23.66/3.49  
% 23.66/3.49  fof(f57,plain,(
% 23.66/3.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 23.66/3.49    inference(cnf_transformation,[],[f31])).
% 23.66/3.49  
% 23.66/3.49  fof(f4,axiom,(
% 23.66/3.49    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 23.66/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.66/3.49  
% 23.66/3.49  fof(f24,plain,(
% 23.66/3.49    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 23.66/3.49    inference(ennf_transformation,[],[f4])).
% 23.66/3.49  
% 23.66/3.49  fof(f50,plain,(
% 23.66/3.49    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 23.66/3.49    inference(cnf_transformation,[],[f24])).
% 23.66/3.49  
% 23.66/3.49  fof(f14,axiom,(
% 23.66/3.49    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 23.66/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.66/3.49  
% 23.66/3.49  fof(f65,plain,(
% 23.66/3.49    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 23.66/3.49    inference(cnf_transformation,[],[f14])).
% 23.66/3.49  
% 23.66/3.49  fof(f81,plain,(
% 23.66/3.49    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_partfun1(X0),X1) | ~v1_relat_1(X1)) )),
% 23.66/3.49    inference(definition_unfolding,[],[f50,f65])).
% 23.66/3.49  
% 23.66/3.49  fof(f70,plain,(
% 23.66/3.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 23.66/3.49    inference(cnf_transformation,[],[f46])).
% 23.66/3.49  
% 23.66/3.49  fof(f68,plain,(
% 23.66/3.49    v1_funct_1(sK2)),
% 23.66/3.49    inference(cnf_transformation,[],[f46])).
% 23.66/3.49  
% 23.66/3.49  fof(f5,axiom,(
% 23.66/3.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 23.66/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.66/3.49  
% 23.66/3.49  fof(f25,plain,(
% 23.66/3.49    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 23.66/3.49    inference(ennf_transformation,[],[f5])).
% 23.66/3.49  
% 23.66/3.49  fof(f26,plain,(
% 23.66/3.49    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 23.66/3.49    inference(flattening,[],[f25])).
% 23.66/3.49  
% 23.66/3.49  fof(f51,plain,(
% 23.66/3.49    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 23.66/3.49    inference(cnf_transformation,[],[f26])).
% 23.66/3.49  
% 23.66/3.49  fof(f2,axiom,(
% 23.66/3.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2))))),
% 23.66/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.66/3.49  
% 23.66/3.49  fof(f22,plain,(
% 23.66/3.49    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 23.66/3.49    inference(ennf_transformation,[],[f2])).
% 23.66/3.49  
% 23.66/3.49  fof(f48,plain,(
% 23.66/3.49    ( ! [X2,X0,X1] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 23.66/3.49    inference(cnf_transformation,[],[f22])).
% 23.66/3.49  
% 23.66/3.49  fof(f69,plain,(
% 23.66/3.49    v1_funct_2(sK2,sK0,sK1)),
% 23.66/3.49    inference(cnf_transformation,[],[f46])).
% 23.66/3.49  
% 23.66/3.49  fof(f15,axiom,(
% 23.66/3.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 23.66/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.66/3.49  
% 23.66/3.49  fof(f39,plain,(
% 23.66/3.49    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 23.66/3.49    inference(ennf_transformation,[],[f15])).
% 23.66/3.49  
% 23.66/3.49  fof(f40,plain,(
% 23.66/3.49    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 23.66/3.49    inference(flattening,[],[f39])).
% 23.66/3.49  
% 23.66/3.49  fof(f67,plain,(
% 23.66/3.49    ( ! [X2,X0,X1] : (k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 23.66/3.49    inference(cnf_transformation,[],[f40])).
% 23.66/3.49  
% 23.66/3.49  fof(f76,plain,(
% 23.66/3.49    v2_funct_1(sK2)),
% 23.66/3.49    inference(cnf_transformation,[],[f46])).
% 23.66/3.49  
% 23.66/3.49  fof(f74,plain,(
% 23.66/3.49    k2_relset_1(sK0,sK1,sK2) = sK1),
% 23.66/3.49    inference(cnf_transformation,[],[f46])).
% 23.66/3.49  
% 23.66/3.49  fof(f78,plain,(
% 23.66/3.49    k1_xboole_0 != sK1),
% 23.66/3.49    inference(cnf_transformation,[],[f46])).
% 23.66/3.49  
% 23.66/3.49  fof(f13,axiom,(
% 23.66/3.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 23.66/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.66/3.49  
% 23.66/3.49  fof(f37,plain,(
% 23.66/3.49    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 23.66/3.49    inference(ennf_transformation,[],[f13])).
% 23.66/3.49  
% 23.66/3.49  fof(f38,plain,(
% 23.66/3.49    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 23.66/3.49    inference(flattening,[],[f37])).
% 23.66/3.49  
% 23.66/3.49  fof(f64,plain,(
% 23.66/3.49    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 23.66/3.49    inference(cnf_transformation,[],[f38])).
% 23.66/3.49  
% 23.66/3.49  fof(f71,plain,(
% 23.66/3.49    v1_funct_1(sK3)),
% 23.66/3.49    inference(cnf_transformation,[],[f46])).
% 23.66/3.49  
% 23.66/3.49  fof(f10,axiom,(
% 23.66/3.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 23.66/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.66/3.49  
% 23.66/3.49  fof(f33,plain,(
% 23.66/3.49    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 23.66/3.49    inference(ennf_transformation,[],[f10])).
% 23.66/3.49  
% 23.66/3.49  fof(f34,plain,(
% 23.66/3.49    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 23.66/3.49    inference(flattening,[],[f33])).
% 23.66/3.49  
% 23.66/3.49  fof(f43,plain,(
% 23.66/3.49    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 23.66/3.49    inference(nnf_transformation,[],[f34])).
% 23.66/3.49  
% 23.66/3.49  fof(f59,plain,(
% 23.66/3.49    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 23.66/3.49    inference(cnf_transformation,[],[f43])).
% 23.66/3.49  
% 23.66/3.49  fof(f75,plain,(
% 23.66/3.49    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 23.66/3.49    inference(cnf_transformation,[],[f46])).
% 23.66/3.49  
% 23.66/3.49  fof(f12,axiom,(
% 23.66/3.49    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 23.66/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.66/3.49  
% 23.66/3.49  fof(f18,plain,(
% 23.66/3.49    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 23.66/3.49    inference(pure_predicate_removal,[],[f12])).
% 23.66/3.49  
% 23.66/3.49  fof(f63,plain,(
% 23.66/3.49    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 23.66/3.49    inference(cnf_transformation,[],[f18])).
% 23.66/3.49  
% 23.66/3.49  fof(f11,axiom,(
% 23.66/3.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 23.66/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.66/3.49  
% 23.66/3.49  fof(f35,plain,(
% 23.66/3.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 23.66/3.49    inference(ennf_transformation,[],[f11])).
% 23.66/3.49  
% 23.66/3.49  fof(f36,plain,(
% 23.66/3.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 23.66/3.49    inference(flattening,[],[f35])).
% 23.66/3.49  
% 23.66/3.49  fof(f62,plain,(
% 23.66/3.49    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 23.66/3.49    inference(cnf_transformation,[],[f36])).
% 23.66/3.49  
% 23.66/3.49  fof(f3,axiom,(
% 23.66/3.49    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 23.66/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.66/3.49  
% 23.66/3.49  fof(f23,plain,(
% 23.66/3.49    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 23.66/3.49    inference(ennf_transformation,[],[f3])).
% 23.66/3.49  
% 23.66/3.49  fof(f49,plain,(
% 23.66/3.49    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 23.66/3.49    inference(cnf_transformation,[],[f23])).
% 23.66/3.49  
% 23.66/3.49  fof(f80,plain,(
% 23.66/3.49    ( ! [X0] : (k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 23.66/3.49    inference(definition_unfolding,[],[f49,f65])).
% 23.66/3.49  
% 23.66/3.49  fof(f6,axiom,(
% 23.66/3.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 23.66/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.66/3.49  
% 23.66/3.49  fof(f27,plain,(
% 23.66/3.49    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 23.66/3.49    inference(ennf_transformation,[],[f6])).
% 23.66/3.49  
% 23.66/3.49  fof(f28,plain,(
% 23.66/3.49    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 23.66/3.49    inference(flattening,[],[f27])).
% 23.66/3.49  
% 23.66/3.49  fof(f54,plain,(
% 23.66/3.49    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 23.66/3.49    inference(cnf_transformation,[],[f28])).
% 23.66/3.49  
% 23.66/3.49  fof(f7,axiom,(
% 23.66/3.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 23.66/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.66/3.49  
% 23.66/3.49  fof(f29,plain,(
% 23.66/3.49    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 23.66/3.49    inference(ennf_transformation,[],[f7])).
% 23.66/3.49  
% 23.66/3.49  fof(f30,plain,(
% 23.66/3.49    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 23.66/3.49    inference(flattening,[],[f29])).
% 23.66/3.49  
% 23.66/3.49  fof(f55,plain,(
% 23.66/3.49    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 23.66/3.49    inference(cnf_transformation,[],[f30])).
% 23.66/3.49  
% 23.66/3.49  fof(f83,plain,(
% 23.66/3.49    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 23.66/3.49    inference(definition_unfolding,[],[f55,f65])).
% 23.66/3.49  
% 23.66/3.49  fof(f66,plain,(
% 23.66/3.49    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 23.66/3.49    inference(cnf_transformation,[],[f40])).
% 23.66/3.49  
% 23.66/3.49  fof(f9,axiom,(
% 23.66/3.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 23.66/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.66/3.49  
% 23.66/3.49  fof(f19,plain,(
% 23.66/3.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 23.66/3.49    inference(pure_predicate_removal,[],[f9])).
% 23.66/3.49  
% 23.66/3.49  fof(f32,plain,(
% 23.66/3.49    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 23.66/3.49    inference(ennf_transformation,[],[f19])).
% 23.66/3.49  
% 23.66/3.49  fof(f58,plain,(
% 23.66/3.49    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 23.66/3.49    inference(cnf_transformation,[],[f32])).
% 23.66/3.49  
% 23.66/3.49  fof(f1,axiom,(
% 23.66/3.49    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 23.66/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.66/3.49  
% 23.66/3.49  fof(f20,plain,(
% 23.66/3.49    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 23.66/3.49    inference(ennf_transformation,[],[f1])).
% 23.66/3.49  
% 23.66/3.49  fof(f21,plain,(
% 23.66/3.49    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 23.66/3.49    inference(flattening,[],[f20])).
% 23.66/3.49  
% 23.66/3.49  fof(f47,plain,(
% 23.66/3.49    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 23.66/3.49    inference(cnf_transformation,[],[f21])).
% 23.66/3.49  
% 23.66/3.49  fof(f79,plain,(
% 23.66/3.49    k2_funct_1(sK2) != sK3),
% 23.66/3.49    inference(cnf_transformation,[],[f46])).
% 23.66/3.49  
% 23.66/3.49  cnf(c_26,negated_conjecture,
% 23.66/3.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 23.66/3.49      inference(cnf_transformation,[],[f73]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_729,negated_conjecture,
% 23.66/3.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 23.66/3.49      inference(subtyping,[status(esa)],[c_26]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_1161,plain,
% 23.66/3.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 23.66/3.49      inference(predicate_to_equality,[status(thm)],[c_729]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_10,plain,
% 23.66/3.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.66/3.49      | v1_relat_1(X0) ),
% 23.66/3.49      inference(cnf_transformation,[],[f57]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_738,plain,
% 23.66/3.49      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 23.66/3.49      | v1_relat_1(X0_50) ),
% 23.66/3.49      inference(subtyping,[status(esa)],[c_10]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_1156,plain,
% 23.66/3.49      ( m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 23.66/3.49      | v1_relat_1(X0_50) = iProver_top ),
% 23.66/3.49      inference(predicate_to_equality,[status(thm)],[c_738]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_1758,plain,
% 23.66/3.49      ( v1_relat_1(sK3) = iProver_top ),
% 23.66/3.49      inference(superposition,[status(thm)],[c_1161,c_1156]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_3,plain,
% 23.66/3.49      ( ~ v1_relat_1(X0)
% 23.66/3.49      | k5_relat_1(k6_partfun1(X1),X0) = k7_relat_1(X0,X1) ),
% 23.66/3.49      inference(cnf_transformation,[],[f81]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_741,plain,
% 23.66/3.49      ( ~ v1_relat_1(X0_50)
% 23.66/3.49      | k5_relat_1(k6_partfun1(X0_51),X0_50) = k7_relat_1(X0_50,X0_51) ),
% 23.66/3.49      inference(subtyping,[status(esa)],[c_3]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_1153,plain,
% 23.66/3.49      ( k5_relat_1(k6_partfun1(X0_51),X0_50) = k7_relat_1(X0_50,X0_51)
% 23.66/3.49      | v1_relat_1(X0_50) != iProver_top ),
% 23.66/3.49      inference(predicate_to_equality,[status(thm)],[c_741]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_1924,plain,
% 23.66/3.49      ( k5_relat_1(k6_partfun1(X0_51),sK3) = k7_relat_1(sK3,X0_51) ),
% 23.66/3.49      inference(superposition,[status(thm)],[c_1758,c_1153]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_29,negated_conjecture,
% 23.66/3.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 23.66/3.49      inference(cnf_transformation,[],[f70]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_727,negated_conjecture,
% 23.66/3.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 23.66/3.49      inference(subtyping,[status(esa)],[c_29]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_1163,plain,
% 23.66/3.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 23.66/3.49      inference(predicate_to_equality,[status(thm)],[c_727]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_1759,plain,
% 23.66/3.49      ( v1_relat_1(sK2) = iProver_top ),
% 23.66/3.49      inference(superposition,[status(thm)],[c_1163,c_1156]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_31,negated_conjecture,
% 23.66/3.49      ( v1_funct_1(sK2) ),
% 23.66/3.49      inference(cnf_transformation,[],[f68]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_726,negated_conjecture,
% 23.66/3.49      ( v1_funct_1(sK2) ),
% 23.66/3.49      inference(subtyping,[status(esa)],[c_31]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_1164,plain,
% 23.66/3.49      ( v1_funct_1(sK2) = iProver_top ),
% 23.66/3.49      inference(predicate_to_equality,[status(thm)],[c_726]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_5,plain,
% 23.66/3.49      ( ~ v1_funct_1(X0)
% 23.66/3.49      | ~ v1_relat_1(X0)
% 23.66/3.49      | v1_relat_1(k2_funct_1(X0)) ),
% 23.66/3.49      inference(cnf_transformation,[],[f51]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_739,plain,
% 23.66/3.49      ( ~ v1_funct_1(X0_50)
% 23.66/3.49      | ~ v1_relat_1(X0_50)
% 23.66/3.49      | v1_relat_1(k2_funct_1(X0_50)) ),
% 23.66/3.49      inference(subtyping,[status(esa)],[c_5]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_1155,plain,
% 23.66/3.49      ( v1_funct_1(X0_50) != iProver_top
% 23.66/3.49      | v1_relat_1(X0_50) != iProver_top
% 23.66/3.49      | v1_relat_1(k2_funct_1(X0_50)) = iProver_top ),
% 23.66/3.49      inference(predicate_to_equality,[status(thm)],[c_739]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_1,plain,
% 23.66/3.49      ( ~ v1_relat_1(X0)
% 23.66/3.49      | ~ v1_relat_1(X1)
% 23.66/3.49      | ~ v1_relat_1(X2)
% 23.66/3.49      | k5_relat_1(k5_relat_1(X2,X0),X1) = k5_relat_1(X2,k5_relat_1(X0,X1)) ),
% 23.66/3.49      inference(cnf_transformation,[],[f48]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_743,plain,
% 23.66/3.49      ( ~ v1_relat_1(X0_50)
% 23.66/3.49      | ~ v1_relat_1(X1_50)
% 23.66/3.49      | ~ v1_relat_1(X2_50)
% 23.66/3.49      | k5_relat_1(k5_relat_1(X2_50,X0_50),X1_50) = k5_relat_1(X2_50,k5_relat_1(X0_50,X1_50)) ),
% 23.66/3.49      inference(subtyping,[status(esa)],[c_1]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_1151,plain,
% 23.66/3.49      ( k5_relat_1(k5_relat_1(X0_50,X1_50),X2_50) = k5_relat_1(X0_50,k5_relat_1(X1_50,X2_50))
% 23.66/3.49      | v1_relat_1(X1_50) != iProver_top
% 23.66/3.49      | v1_relat_1(X2_50) != iProver_top
% 23.66/3.49      | v1_relat_1(X0_50) != iProver_top ),
% 23.66/3.49      inference(predicate_to_equality,[status(thm)],[c_743]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_1867,plain,
% 23.66/3.49      ( k5_relat_1(k2_funct_1(X0_50),k5_relat_1(X1_50,X2_50)) = k5_relat_1(k5_relat_1(k2_funct_1(X0_50),X1_50),X2_50)
% 23.66/3.49      | v1_funct_1(X0_50) != iProver_top
% 23.66/3.49      | v1_relat_1(X0_50) != iProver_top
% 23.66/3.49      | v1_relat_1(X1_50) != iProver_top
% 23.66/3.49      | v1_relat_1(X2_50) != iProver_top ),
% 23.66/3.49      inference(superposition,[status(thm)],[c_1155,c_1151]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_4217,plain,
% 23.66/3.49      ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0_50),X1_50) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0_50,X1_50))
% 23.66/3.49      | v1_relat_1(X0_50) != iProver_top
% 23.66/3.49      | v1_relat_1(X1_50) != iProver_top
% 23.66/3.49      | v1_relat_1(sK2) != iProver_top ),
% 23.66/3.49      inference(superposition,[status(thm)],[c_1164,c_1867]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_34,plain,
% 23.66/3.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 23.66/3.49      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_1215,plain,
% 23.66/3.49      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 23.66/3.49      | v1_relat_1(sK2) ),
% 23.66/3.49      inference(instantiation,[status(thm)],[c_738]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_1243,plain,
% 23.66/3.49      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 23.66/3.49      | v1_relat_1(sK2) ),
% 23.66/3.49      inference(instantiation,[status(thm)],[c_1215]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_1244,plain,
% 23.66/3.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 23.66/3.49      | v1_relat_1(sK2) = iProver_top ),
% 23.66/3.49      inference(predicate_to_equality,[status(thm)],[c_1243]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_4666,plain,
% 23.66/3.49      ( v1_relat_1(X1_50) != iProver_top
% 23.66/3.49      | v1_relat_1(X0_50) != iProver_top
% 23.66/3.49      | k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0_50),X1_50) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0_50,X1_50)) ),
% 23.66/3.49      inference(global_propositional_subsumption,
% 23.66/3.49                [status(thm)],
% 23.66/3.49                [c_4217,c_34,c_1244]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_4667,plain,
% 23.66/3.49      ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0_50),X1_50) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0_50,X1_50))
% 23.66/3.49      | v1_relat_1(X0_50) != iProver_top
% 23.66/3.49      | v1_relat_1(X1_50) != iProver_top ),
% 23.66/3.49      inference(renaming,[status(thm)],[c_4666]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_4670,plain,
% 23.66/3.49      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0_50)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),X0_50)
% 23.66/3.49      | v1_relat_1(X0_50) != iProver_top ),
% 23.66/3.49      inference(superposition,[status(thm)],[c_1759,c_4667]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_30,negated_conjecture,
% 23.66/3.49      ( v1_funct_2(sK2,sK0,sK1) ),
% 23.66/3.49      inference(cnf_transformation,[],[f69]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_18,plain,
% 23.66/3.49      ( ~ v1_funct_2(X0,X1,X2)
% 23.66/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.66/3.49      | ~ v2_funct_1(X0)
% 23.66/3.49      | ~ v1_funct_1(X0)
% 23.66/3.49      | k2_relset_1(X1,X2,X0) != X2
% 23.66/3.49      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
% 23.66/3.49      | k1_xboole_0 = X2 ),
% 23.66/3.49      inference(cnf_transformation,[],[f67]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_23,negated_conjecture,
% 23.66/3.49      ( v2_funct_1(sK2) ),
% 23.66/3.49      inference(cnf_transformation,[],[f76]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_385,plain,
% 23.66/3.49      ( ~ v1_funct_2(X0,X1,X2)
% 23.66/3.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.66/3.49      | ~ v1_funct_1(X0)
% 23.66/3.49      | k2_relset_1(X1,X2,X0) != X2
% 23.66/3.49      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
% 23.66/3.49      | sK2 != X0
% 23.66/3.49      | k1_xboole_0 = X2 ),
% 23.66/3.49      inference(resolution_lifted,[status(thm)],[c_18,c_23]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_386,plain,
% 23.66/3.49      ( ~ v1_funct_2(sK2,X0,X1)
% 23.66/3.49      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 23.66/3.49      | ~ v1_funct_1(sK2)
% 23.66/3.49      | k2_relset_1(X0,X1,sK2) != X1
% 23.66/3.49      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(X1)
% 23.66/3.49      | k1_xboole_0 = X1 ),
% 23.66/3.49      inference(unflattening,[status(thm)],[c_385]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_390,plain,
% 23.66/3.49      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 23.66/3.49      | ~ v1_funct_2(sK2,X0,X1)
% 23.66/3.49      | k2_relset_1(X0,X1,sK2) != X1
% 23.66/3.49      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(X1)
% 23.66/3.49      | k1_xboole_0 = X1 ),
% 23.66/3.49      inference(global_propositional_subsumption,
% 23.66/3.49                [status(thm)],
% 23.66/3.49                [c_386,c_31]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_391,plain,
% 23.66/3.49      ( ~ v1_funct_2(sK2,X0,X1)
% 23.66/3.49      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 23.66/3.49      | k2_relset_1(X0,X1,sK2) != X1
% 23.66/3.49      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(X1)
% 23.66/3.49      | k1_xboole_0 = X1 ),
% 23.66/3.49      inference(renaming,[status(thm)],[c_390]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_532,plain,
% 23.66/3.49      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 23.66/3.49      | k2_relset_1(X0,X1,sK2) != X1
% 23.66/3.49      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(X1)
% 23.66/3.49      | sK0 != X0
% 23.66/3.49      | sK1 != X1
% 23.66/3.49      | sK2 != sK2
% 23.66/3.49      | k1_xboole_0 = X1 ),
% 23.66/3.49      inference(resolution_lifted,[status(thm)],[c_30,c_391]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_533,plain,
% 23.66/3.49      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 23.66/3.49      | k2_relset_1(sK0,sK1,sK2) != sK1
% 23.66/3.49      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 23.66/3.49      | k1_xboole_0 = sK1 ),
% 23.66/3.49      inference(unflattening,[status(thm)],[c_532]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_25,negated_conjecture,
% 23.66/3.49      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 23.66/3.49      inference(cnf_transformation,[],[f74]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_21,negated_conjecture,
% 23.66/3.49      ( k1_xboole_0 != sK1 ),
% 23.66/3.49      inference(cnf_transformation,[],[f78]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_535,plain,
% 23.66/3.49      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
% 23.66/3.49      inference(global_propositional_subsumption,
% 23.66/3.49                [status(thm)],
% 23.66/3.49                [c_533,c_29,c_25,c_21]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_717,plain,
% 23.66/3.49      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
% 23.66/3.49      inference(subtyping,[status(esa)],[c_535]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_4676,plain,
% 23.66/3.49      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0_50)) = k5_relat_1(k6_partfun1(sK1),X0_50)
% 23.66/3.49      | v1_relat_1(X0_50) != iProver_top ),
% 23.66/3.49      inference(light_normalisation,[status(thm)],[c_4670,c_717]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_4795,plain,
% 23.66/3.49      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
% 23.66/3.49      inference(superposition,[status(thm)],[c_1758,c_4676]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_17,plain,
% 23.66/3.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.66/3.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 23.66/3.49      | ~ v1_funct_1(X0)
% 23.66/3.49      | ~ v1_funct_1(X3)
% 23.66/3.49      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 23.66/3.49      inference(cnf_transformation,[],[f64]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_734,plain,
% 23.66/3.49      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 23.66/3.49      | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51)))
% 23.66/3.49      | ~ v1_funct_1(X0_50)
% 23.66/3.49      | ~ v1_funct_1(X1_50)
% 23.66/3.49      | k1_partfun1(X2_51,X3_51,X0_51,X1_51,X1_50,X0_50) = k5_relat_1(X1_50,X0_50) ),
% 23.66/3.49      inference(subtyping,[status(esa)],[c_17]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_1160,plain,
% 23.66/3.49      ( k1_partfun1(X0_51,X1_51,X2_51,X3_51,X0_50,X1_50) = k5_relat_1(X0_50,X1_50)
% 23.66/3.49      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 23.66/3.49      | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51))) != iProver_top
% 23.66/3.49      | v1_funct_1(X1_50) != iProver_top
% 23.66/3.49      | v1_funct_1(X0_50) != iProver_top ),
% 23.66/3.49      inference(predicate_to_equality,[status(thm)],[c_734]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_2217,plain,
% 23.66/3.49      ( k1_partfun1(X0_51,X1_51,sK1,sK0,X0_50,sK3) = k5_relat_1(X0_50,sK3)
% 23.66/3.49      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 23.66/3.49      | v1_funct_1(X0_50) != iProver_top
% 23.66/3.49      | v1_funct_1(sK3) != iProver_top ),
% 23.66/3.49      inference(superposition,[status(thm)],[c_1161,c_1160]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_28,negated_conjecture,
% 23.66/3.49      ( v1_funct_1(sK3) ),
% 23.66/3.49      inference(cnf_transformation,[],[f71]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_35,plain,
% 23.66/3.49      ( v1_funct_1(sK3) = iProver_top ),
% 23.66/3.49      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_2435,plain,
% 23.66/3.49      ( v1_funct_1(X0_50) != iProver_top
% 23.66/3.49      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 23.66/3.49      | k1_partfun1(X0_51,X1_51,sK1,sK0,X0_50,sK3) = k5_relat_1(X0_50,sK3) ),
% 23.66/3.49      inference(global_propositional_subsumption,
% 23.66/3.49                [status(thm)],
% 23.66/3.49                [c_2217,c_35]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_2436,plain,
% 23.66/3.49      ( k1_partfun1(X0_51,X1_51,sK1,sK0,X0_50,sK3) = k5_relat_1(X0_50,sK3)
% 23.66/3.49      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 23.66/3.49      | v1_funct_1(X0_50) != iProver_top ),
% 23.66/3.49      inference(renaming,[status(thm)],[c_2435]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_2442,plain,
% 23.66/3.49      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 23.66/3.49      | v1_funct_1(sK2) != iProver_top ),
% 23.66/3.49      inference(superposition,[status(thm)],[c_1163,c_2436]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_13,plain,
% 23.66/3.49      ( ~ r2_relset_1(X0,X1,X2,X3)
% 23.66/3.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 23.66/3.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 23.66/3.49      | X3 = X2 ),
% 23.66/3.49      inference(cnf_transformation,[],[f59]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_24,negated_conjecture,
% 23.66/3.49      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 23.66/3.49      inference(cnf_transformation,[],[f75]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_341,plain,
% 23.66/3.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.66/3.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.66/3.49      | X3 = X0
% 23.66/3.49      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 23.66/3.49      | k6_partfun1(sK0) != X3
% 23.66/3.49      | sK0 != X2
% 23.66/3.49      | sK0 != X1 ),
% 23.66/3.49      inference(resolution_lifted,[status(thm)],[c_13,c_24]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_342,plain,
% 23.66/3.49      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 23.66/3.49      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 23.66/3.49      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 23.66/3.49      inference(unflattening,[status(thm)],[c_341]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_16,plain,
% 23.66/3.49      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 23.66/3.49      inference(cnf_transformation,[],[f63]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_50,plain,
% 23.66/3.49      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 23.66/3.49      inference(instantiation,[status(thm)],[c_16]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_344,plain,
% 23.66/3.49      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 23.66/3.49      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 23.66/3.49      inference(global_propositional_subsumption,
% 23.66/3.49                [status(thm)],
% 23.66/3.49                [c_342,c_50]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_724,plain,
% 23.66/3.49      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 23.66/3.49      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 23.66/3.49      inference(subtyping,[status(esa)],[c_344]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_1166,plain,
% 23.66/3.49      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 23.66/3.49      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 23.66/3.49      inference(predicate_to_equality,[status(thm)],[c_724]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_14,plain,
% 23.66/3.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.66/3.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 23.66/3.49      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 23.66/3.49      | ~ v1_funct_1(X0)
% 23.66/3.49      | ~ v1_funct_1(X3) ),
% 23.66/3.49      inference(cnf_transformation,[],[f62]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_737,plain,
% 23.66/3.49      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 23.66/3.49      | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51)))
% 23.66/3.49      | m1_subset_1(k1_partfun1(X2_51,X3_51,X0_51,X1_51,X1_50,X0_50),k1_zfmisc_1(k2_zfmisc_1(X2_51,X1_51)))
% 23.66/3.49      | ~ v1_funct_1(X0_50)
% 23.66/3.49      | ~ v1_funct_1(X1_50) ),
% 23.66/3.49      inference(subtyping,[status(esa)],[c_14]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_1227,plain,
% 23.66/3.49      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 23.66/3.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 23.66/3.49      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 23.66/3.49      | ~ v1_funct_1(sK3)
% 23.66/3.49      | ~ v1_funct_1(sK2) ),
% 23.66/3.49      inference(instantiation,[status(thm)],[c_737]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_1597,plain,
% 23.66/3.49      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 23.66/3.49      inference(global_propositional_subsumption,
% 23.66/3.49                [status(thm)],
% 23.66/3.49                [c_1166,c_31,c_29,c_28,c_26,c_724,c_1227]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_2450,plain,
% 23.66/3.49      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 23.66/3.49      | v1_funct_1(sK2) != iProver_top ),
% 23.66/3.49      inference(light_normalisation,[status(thm)],[c_2442,c_1597]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_32,plain,
% 23.66/3.49      ( v1_funct_1(sK2) = iProver_top ),
% 23.66/3.49      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_2796,plain,
% 23.66/3.49      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 23.66/3.49      inference(global_propositional_subsumption,
% 23.66/3.49                [status(thm)],
% 23.66/3.49                [c_2450,c_32]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_2,plain,
% 23.66/3.49      ( ~ v1_relat_1(X0)
% 23.66/3.49      | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ),
% 23.66/3.49      inference(cnf_transformation,[],[f80]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_742,plain,
% 23.66/3.49      ( ~ v1_relat_1(X0_50)
% 23.66/3.49      | k5_relat_1(X0_50,k6_partfun1(k2_relat_1(X0_50))) = X0_50 ),
% 23.66/3.49      inference(subtyping,[status(esa)],[c_2]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_1152,plain,
% 23.66/3.49      ( k5_relat_1(X0_50,k6_partfun1(k2_relat_1(X0_50))) = X0_50
% 23.66/3.49      | v1_relat_1(X0_50) != iProver_top ),
% 23.66/3.49      inference(predicate_to_equality,[status(thm)],[c_742]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_1770,plain,
% 23.66/3.49      ( k5_relat_1(k2_funct_1(X0_50),k6_partfun1(k2_relat_1(k2_funct_1(X0_50)))) = k2_funct_1(X0_50)
% 23.66/3.49      | v1_funct_1(X0_50) != iProver_top
% 23.66/3.49      | v1_relat_1(X0_50) != iProver_top ),
% 23.66/3.49      inference(superposition,[status(thm)],[c_1155,c_1152]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_3424,plain,
% 23.66/3.49      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(k2_relat_1(k2_funct_1(sK2)))) = k2_funct_1(sK2)
% 23.66/3.49      | v1_relat_1(sK2) != iProver_top ),
% 23.66/3.49      inference(superposition,[status(thm)],[c_1164,c_1770]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_6,plain,
% 23.66/3.49      ( ~ v2_funct_1(X0)
% 23.66/3.49      | ~ v1_funct_1(X0)
% 23.66/3.49      | ~ v1_relat_1(X0)
% 23.66/3.49      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 23.66/3.49      inference(cnf_transformation,[],[f54]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_454,plain,
% 23.66/3.49      ( ~ v1_funct_1(X0)
% 23.66/3.49      | ~ v1_relat_1(X0)
% 23.66/3.49      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 23.66/3.49      | sK2 != X0 ),
% 23.66/3.49      inference(resolution_lifted,[status(thm)],[c_6,c_23]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_455,plain,
% 23.66/3.49      ( ~ v1_funct_1(sK2)
% 23.66/3.49      | ~ v1_relat_1(sK2)
% 23.66/3.49      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 23.66/3.49      inference(unflattening,[status(thm)],[c_454]) ).
% 23.66/3.49  
% 23.66/3.49  cnf(c_457,plain,
% 23.66/3.49      ( ~ v1_relat_1(sK2)
% 23.66/3.49      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 23.66/3.49      inference(global_propositional_subsumption,
% 23.66/3.50                [status(thm)],
% 23.66/3.50                [c_455,c_31]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_720,plain,
% 23.66/3.50      ( ~ v1_relat_1(sK2)
% 23.66/3.50      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 23.66/3.50      inference(subtyping,[status(esa)],[c_457]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_1170,plain,
% 23.66/3.50      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 23.66/3.50      | v1_relat_1(sK2) != iProver_top ),
% 23.66/3.50      inference(predicate_to_equality,[status(thm)],[c_720]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_1486,plain,
% 23.66/3.50      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 23.66/3.50      inference(global_propositional_subsumption,
% 23.66/3.50                [status(thm)],
% 23.66/3.50                [c_1170,c_29,c_720,c_1243]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_9,plain,
% 23.66/3.50      ( ~ v2_funct_1(X0)
% 23.66/3.50      | ~ v1_funct_1(X0)
% 23.66/3.50      | ~ v1_relat_1(X0)
% 23.66/3.50      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
% 23.66/3.50      inference(cnf_transformation,[],[f83]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_412,plain,
% 23.66/3.50      ( ~ v1_funct_1(X0)
% 23.66/3.50      | ~ v1_relat_1(X0)
% 23.66/3.50      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
% 23.66/3.50      | sK2 != X0 ),
% 23.66/3.50      inference(resolution_lifted,[status(thm)],[c_9,c_23]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_413,plain,
% 23.66/3.50      ( ~ v1_funct_1(sK2)
% 23.66/3.50      | ~ v1_relat_1(sK2)
% 23.66/3.50      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
% 23.66/3.50      inference(unflattening,[status(thm)],[c_412]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_415,plain,
% 23.66/3.50      ( ~ v1_relat_1(sK2)
% 23.66/3.50      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
% 23.66/3.50      inference(global_propositional_subsumption,
% 23.66/3.50                [status(thm)],
% 23.66/3.50                [c_413,c_31]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_723,plain,
% 23.66/3.50      ( ~ v1_relat_1(sK2)
% 23.66/3.50      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
% 23.66/3.50      inference(subtyping,[status(esa)],[c_415]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_1167,plain,
% 23.66/3.50      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
% 23.66/3.50      | v1_relat_1(sK2) != iProver_top ),
% 23.66/3.50      inference(predicate_to_equality,[status(thm)],[c_723]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_19,plain,
% 23.66/3.50      ( ~ v1_funct_2(X0,X1,X2)
% 23.66/3.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.66/3.50      | ~ v2_funct_1(X0)
% 23.66/3.50      | ~ v1_funct_1(X0)
% 23.66/3.50      | k2_relset_1(X1,X2,X0) != X2
% 23.66/3.50      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 23.66/3.50      | k1_xboole_0 = X2 ),
% 23.66/3.50      inference(cnf_transformation,[],[f66]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_358,plain,
% 23.66/3.50      ( ~ v1_funct_2(X0,X1,X2)
% 23.66/3.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.66/3.50      | ~ v1_funct_1(X0)
% 23.66/3.50      | k2_relset_1(X1,X2,X0) != X2
% 23.66/3.50      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 23.66/3.50      | sK2 != X0
% 23.66/3.50      | k1_xboole_0 = X2 ),
% 23.66/3.50      inference(resolution_lifted,[status(thm)],[c_19,c_23]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_359,plain,
% 23.66/3.50      ( ~ v1_funct_2(sK2,X0,X1)
% 23.66/3.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 23.66/3.50      | ~ v1_funct_1(sK2)
% 23.66/3.50      | k2_relset_1(X0,X1,sK2) != X1
% 23.66/3.50      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
% 23.66/3.50      | k1_xboole_0 = X1 ),
% 23.66/3.50      inference(unflattening,[status(thm)],[c_358]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_363,plain,
% 23.66/3.50      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 23.66/3.50      | ~ v1_funct_2(sK2,X0,X1)
% 23.66/3.50      | k2_relset_1(X0,X1,sK2) != X1
% 23.66/3.50      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
% 23.66/3.50      | k1_xboole_0 = X1 ),
% 23.66/3.50      inference(global_propositional_subsumption,
% 23.66/3.50                [status(thm)],
% 23.66/3.50                [c_359,c_31]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_364,plain,
% 23.66/3.50      ( ~ v1_funct_2(sK2,X0,X1)
% 23.66/3.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 23.66/3.50      | k2_relset_1(X0,X1,sK2) != X1
% 23.66/3.50      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
% 23.66/3.50      | k1_xboole_0 = X1 ),
% 23.66/3.50      inference(renaming,[status(thm)],[c_363]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_540,plain,
% 23.66/3.50      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 23.66/3.50      | k2_relset_1(X0,X1,sK2) != X1
% 23.66/3.50      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
% 23.66/3.50      | sK0 != X0
% 23.66/3.50      | sK1 != X1
% 23.66/3.50      | sK2 != sK2
% 23.66/3.50      | k1_xboole_0 = X1 ),
% 23.66/3.50      inference(resolution_lifted,[status(thm)],[c_30,c_364]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_541,plain,
% 23.66/3.50      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 23.66/3.50      | k2_relset_1(sK0,sK1,sK2) != sK1
% 23.66/3.50      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
% 23.66/3.50      | k1_xboole_0 = sK1 ),
% 23.66/3.50      inference(unflattening,[status(thm)],[c_540]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_543,plain,
% 23.66/3.50      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
% 23.66/3.50      inference(global_propositional_subsumption,
% 23.66/3.50                [status(thm)],
% 23.66/3.50                [c_541,c_29,c_25,c_21]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_716,plain,
% 23.66/3.50      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
% 23.66/3.50      inference(subtyping,[status(esa)],[c_543]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_1173,plain,
% 23.66/3.50      ( k6_partfun1(k1_relat_1(sK2)) = k6_partfun1(sK0)
% 23.66/3.50      | v1_relat_1(sK2) != iProver_top ),
% 23.66/3.50      inference(light_normalisation,[status(thm)],[c_1167,c_716]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_1190,plain,
% 23.66/3.50      ( ~ v1_relat_1(sK2)
% 23.66/3.50      | k6_partfun1(k1_relat_1(sK2)) = k6_partfun1(sK0) ),
% 23.66/3.50      inference(predicate_to_equality_rev,[status(thm)],[c_1173]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_1489,plain,
% 23.66/3.50      ( k6_partfun1(k1_relat_1(sK2)) = k6_partfun1(sK0) ),
% 23.66/3.50      inference(global_propositional_subsumption,
% 23.66/3.50                [status(thm)],
% 23.66/3.50                [c_1173,c_29,c_1190,c_1243]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_3427,plain,
% 23.66/3.50      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k2_funct_1(sK2)
% 23.66/3.50      | v1_relat_1(sK2) != iProver_top ),
% 23.66/3.50      inference(light_normalisation,[status(thm)],[c_3424,c_1486,c_1489]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_3762,plain,
% 23.66/3.50      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k2_funct_1(sK2) ),
% 23.66/3.50      inference(global_propositional_subsumption,
% 23.66/3.50                [status(thm)],
% 23.66/3.50                [c_3427,c_34,c_1244]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_4802,plain,
% 23.66/3.50      ( k5_relat_1(k6_partfun1(sK1),sK3) = k2_funct_1(sK2) ),
% 23.66/3.50      inference(light_normalisation,[status(thm)],[c_4795,c_2796,c_3762]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_83878,plain,
% 23.66/3.50      ( k7_relat_1(sK3,sK1) = k2_funct_1(sK2) ),
% 23.66/3.50      inference(superposition,[status(thm)],[c_1924,c_4802]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_11,plain,
% 23.66/3.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.66/3.50      | v4_relat_1(X0,X1) ),
% 23.66/3.50      inference(cnf_transformation,[],[f58]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_0,plain,
% 23.66/3.50      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 23.66/3.50      inference(cnf_transformation,[],[f47]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_319,plain,
% 23.66/3.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.66/3.50      | ~ v1_relat_1(X0)
% 23.66/3.50      | k7_relat_1(X0,X1) = X0 ),
% 23.66/3.50      inference(resolution,[status(thm)],[c_11,c_0]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_323,plain,
% 23.66/3.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 23.66/3.50      | k7_relat_1(X0,X1) = X0 ),
% 23.66/3.50      inference(global_propositional_subsumption,
% 23.66/3.50                [status(thm)],
% 23.66/3.50                [c_319,c_11,c_10,c_0]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_725,plain,
% 23.66/3.50      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 23.66/3.50      | k7_relat_1(X0_50,X0_51) = X0_50 ),
% 23.66/3.50      inference(subtyping,[status(esa)],[c_323]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_1165,plain,
% 23.66/3.50      ( k7_relat_1(X0_50,X0_51) = X0_50
% 23.66/3.50      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top ),
% 23.66/3.50      inference(predicate_to_equality,[status(thm)],[c_725]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_2800,plain,
% 23.66/3.50      ( k7_relat_1(sK3,sK1) = sK3 ),
% 23.66/3.50      inference(superposition,[status(thm)],[c_1161,c_1165]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_83880,plain,
% 23.66/3.50      ( k2_funct_1(sK2) = sK3 ),
% 23.66/3.50      inference(light_normalisation,[status(thm)],[c_83878,c_2800]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_20,negated_conjecture,
% 23.66/3.50      ( k2_funct_1(sK2) != sK3 ),
% 23.66/3.50      inference(cnf_transformation,[],[f79]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(c_733,negated_conjecture,
% 23.66/3.50      ( k2_funct_1(sK2) != sK3 ),
% 23.66/3.50      inference(subtyping,[status(esa)],[c_20]) ).
% 23.66/3.50  
% 23.66/3.50  cnf(contradiction,plain,
% 23.66/3.50      ( $false ),
% 23.66/3.50      inference(minisat,[status(thm)],[c_83880,c_733]) ).
% 23.66/3.50  
% 23.66/3.50  
% 23.66/3.50  % SZS output end CNFRefutation for theBenchmark.p
% 23.66/3.50  
% 23.66/3.50  ------                               Statistics
% 23.66/3.50  
% 23.66/3.50  ------ General
% 23.66/3.50  
% 23.66/3.50  abstr_ref_over_cycles:                  0
% 23.66/3.50  abstr_ref_under_cycles:                 0
% 23.66/3.50  gc_basic_clause_elim:                   0
% 23.66/3.50  forced_gc_time:                         0
% 23.66/3.50  parsing_time:                           0.009
% 23.66/3.50  unif_index_cands_time:                  0.
% 23.66/3.50  unif_index_add_time:                    0.
% 23.66/3.50  orderings_time:                         0.
% 23.66/3.50  out_proof_time:                         0.016
% 23.66/3.50  total_time:                             2.651
% 23.66/3.50  num_of_symbols:                         57
% 23.66/3.50  num_of_terms:                           68266
% 23.66/3.50  
% 23.66/3.50  ------ Preprocessing
% 23.66/3.50  
% 23.66/3.50  num_of_splits:                          0
% 23.66/3.50  num_of_split_atoms:                     0
% 23.66/3.50  num_of_reused_defs:                     0
% 23.66/3.50  num_eq_ax_congr_red:                    8
% 23.66/3.50  num_of_sem_filtered_clauses:            1
% 23.66/3.50  num_of_subtypes:                        4
% 23.66/3.50  monotx_restored_types:                  1
% 23.66/3.50  sat_num_of_epr_types:                   0
% 23.66/3.50  sat_num_of_non_cyclic_types:            0
% 23.66/3.50  sat_guarded_non_collapsed_types:        1
% 23.66/3.50  num_pure_diseq_elim:                    0
% 23.66/3.50  simp_replaced_by:                       0
% 23.66/3.50  res_preprocessed:                       153
% 23.66/3.50  prep_upred:                             0
% 23.66/3.50  prep_unflattend:                        22
% 23.66/3.50  smt_new_axioms:                         0
% 23.66/3.50  pred_elim_cands:                        3
% 23.66/3.50  pred_elim:                              4
% 23.66/3.50  pred_elim_cl:                           4
% 23.66/3.50  pred_elim_cycles:                       6
% 23.66/3.50  merged_defs:                            0
% 23.66/3.50  merged_defs_ncl:                        0
% 23.66/3.50  bin_hyper_res:                          0
% 23.66/3.50  prep_cycles:                            4
% 23.66/3.50  pred_elim_time:                         0.006
% 23.66/3.50  splitting_time:                         0.
% 23.66/3.50  sem_filter_time:                        0.
% 23.66/3.50  monotx_time:                            0.001
% 23.66/3.50  subtype_inf_time:                       0.001
% 23.66/3.50  
% 23.66/3.50  ------ Problem properties
% 23.66/3.50  
% 23.66/3.50  clauses:                                28
% 23.66/3.50  conjectures:                            8
% 23.66/3.50  epr:                                    4
% 23.66/3.50  horn:                                   28
% 23.66/3.50  ground:                                 17
% 23.66/3.50  unary:                                  11
% 23.66/3.50  binary:                                 9
% 23.66/3.50  lits:                                   62
% 23.66/3.50  lits_eq:                                22
% 23.66/3.50  fd_pure:                                0
% 23.66/3.50  fd_pseudo:                              0
% 23.66/3.50  fd_cond:                                0
% 23.66/3.50  fd_pseudo_cond:                         0
% 23.66/3.50  ac_symbols:                             0
% 23.66/3.50  
% 23.66/3.50  ------ Propositional Solver
% 23.66/3.50  
% 23.66/3.50  prop_solver_calls:                      48
% 23.66/3.50  prop_fast_solver_calls:                 3824
% 23.66/3.50  smt_solver_calls:                       0
% 23.66/3.50  smt_fast_solver_calls:                  0
% 23.66/3.50  prop_num_of_clauses:                    31963
% 23.66/3.50  prop_preprocess_simplified:             58811
% 23.66/3.50  prop_fo_subsumed:                       585
% 23.66/3.50  prop_solver_time:                       0.
% 23.66/3.50  smt_solver_time:                        0.
% 23.66/3.50  smt_fast_solver_time:                   0.
% 23.66/3.50  prop_fast_solver_time:                  0.
% 23.66/3.50  prop_unsat_core_time:                   0.004
% 23.66/3.50  
% 23.66/3.50  ------ QBF
% 23.66/3.50  
% 23.66/3.50  qbf_q_res:                              0
% 23.66/3.50  qbf_num_tautologies:                    0
% 23.66/3.50  qbf_prep_cycles:                        0
% 23.66/3.50  
% 23.66/3.50  ------ BMC1
% 23.66/3.50  
% 23.66/3.50  bmc1_current_bound:                     -1
% 23.66/3.50  bmc1_last_solved_bound:                 -1
% 23.66/3.50  bmc1_unsat_core_size:                   -1
% 23.66/3.50  bmc1_unsat_core_parents_size:           -1
% 23.66/3.50  bmc1_merge_next_fun:                    0
% 23.66/3.50  bmc1_unsat_core_clauses_time:           0.
% 23.66/3.50  
% 23.66/3.50  ------ Instantiation
% 23.66/3.50  
% 23.66/3.50  inst_num_of_clauses:                    5306
% 23.66/3.50  inst_num_in_passive:                    644
% 23.66/3.50  inst_num_in_active:                     4823
% 23.66/3.50  inst_num_in_unprocessed:                2608
% 23.66/3.50  inst_num_of_loops:                      5099
% 23.66/3.50  inst_num_of_learning_restarts:          1
% 23.66/3.50  inst_num_moves_active_passive:          261
% 23.66/3.50  inst_lit_activity:                      0
% 23.66/3.50  inst_lit_activity_moves:                1
% 23.66/3.50  inst_num_tautologies:                   0
% 23.66/3.50  inst_num_prop_implied:                  0
% 23.66/3.50  inst_num_existing_simplified:           0
% 23.66/3.50  inst_num_eq_res_simplified:             0
% 23.66/3.50  inst_num_child_elim:                    0
% 23.66/3.50  inst_num_of_dismatching_blockings:      12203
% 23.66/3.50  inst_num_of_non_proper_insts:           17821
% 23.66/3.50  inst_num_of_duplicates:                 0
% 23.66/3.50  inst_inst_num_from_inst_to_res:         0
% 23.66/3.50  inst_dismatching_checking_time:         0.
% 23.66/3.50  
% 23.66/3.50  ------ Resolution
% 23.66/3.50  
% 23.66/3.50  res_num_of_clauses:                     46
% 23.66/3.50  res_num_in_passive:                     46
% 23.66/3.50  res_num_in_active:                      0
% 23.66/3.50  res_num_of_loops:                       157
% 23.66/3.50  res_forward_subset_subsumed:            593
% 23.66/3.50  res_backward_subset_subsumed:           4
% 23.66/3.50  res_forward_subsumed:                   0
% 23.66/3.50  res_backward_subsumed:                  0
% 23.66/3.50  res_forward_subsumption_resolution:     0
% 23.66/3.50  res_backward_subsumption_resolution:    0
% 23.66/3.50  res_clause_to_clause_subsumption:       9334
% 23.66/3.50  res_orphan_elimination:                 0
% 23.66/3.50  res_tautology_del:                      1619
% 23.66/3.50  res_num_eq_res_simplified:              0
% 23.66/3.50  res_num_sel_changes:                    0
% 23.66/3.50  res_moves_from_active_to_pass:          0
% 23.66/3.50  
% 23.66/3.50  ------ Superposition
% 23.66/3.50  
% 23.66/3.50  sup_time_total:                         0.
% 23.66/3.50  sup_time_generating:                    0.
% 23.66/3.50  sup_time_sim_full:                      0.
% 23.66/3.50  sup_time_sim_immed:                     0.
% 23.66/3.50  
% 23.66/3.50  sup_num_of_clauses:                     3555
% 23.66/3.50  sup_num_in_active:                      975
% 23.66/3.50  sup_num_in_passive:                     2580
% 23.66/3.50  sup_num_of_loops:                       1019
% 23.66/3.50  sup_fw_superposition:                   3336
% 23.66/3.50  sup_bw_superposition:                   588
% 23.66/3.50  sup_immediate_simplified:               1400
% 23.66/3.50  sup_given_eliminated:                   2
% 23.66/3.50  comparisons_done:                       0
% 23.66/3.50  comparisons_avoided:                    0
% 23.66/3.50  
% 23.66/3.50  ------ Simplifications
% 23.66/3.50  
% 23.66/3.50  
% 23.66/3.50  sim_fw_subset_subsumed:                 16
% 23.66/3.50  sim_bw_subset_subsumed:                 36
% 23.66/3.50  sim_fw_subsumed:                        30
% 23.66/3.50  sim_bw_subsumed:                        5
% 23.66/3.50  sim_fw_subsumption_res:                 0
% 23.66/3.50  sim_bw_subsumption_res:                 0
% 23.66/3.50  sim_tautology_del:                      3
% 23.66/3.50  sim_eq_tautology_del:                   237
% 23.66/3.50  sim_eq_res_simp:                        0
% 23.66/3.50  sim_fw_demodulated:                     402
% 23.66/3.50  sim_bw_demodulated:                     41
% 23.66/3.50  sim_light_normalised:                   1102
% 23.66/3.50  sim_joinable_taut:                      0
% 23.66/3.50  sim_joinable_simp:                      0
% 23.66/3.50  sim_ac_normalised:                      0
% 23.66/3.50  sim_smt_subsumption:                    0
% 23.66/3.50  
%------------------------------------------------------------------------------
