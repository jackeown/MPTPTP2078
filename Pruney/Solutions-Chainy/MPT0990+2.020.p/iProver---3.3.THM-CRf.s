%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:00 EST 2020

% Result     : Theorem 31.51s
% Output     : CNFRefutation 31.51s
% Verified   : 
% Statistics : Number of formulae       :  349 (16789 expanded)
%              Number of clauses        :  256 (5101 expanded)
%              Number of leaves         :   27 (4253 expanded)
%              Depth                    :   29
%              Number of atoms          : 1437 (146763 expanded)
%              Number of equality atoms :  738 (52087 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   24 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
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
    inference(ennf_transformation,[],[f15])).

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
    inference(flattening,[],[f44])).

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
    inference(cnf_transformation,[],[f45])).

fof(f20,conjecture,(
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

fof(f21,negated_conjecture,(
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
    inference(negated_conjecture,[],[f20])).

fof(f54,plain,(
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
    inference(ennf_transformation,[],[f21])).

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
    inference(flattening,[],[f54])).

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

fof(f60,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f55,f59,f58])).

fof(f103,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f60])).

fof(f96,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f60])).

fof(f97,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f60])).

fof(f98,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f60])).

fof(f99,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f60])).

fof(f100,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f60])).

fof(f101,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f60])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
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

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f50])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f105,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f60])).

fof(f2,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f14,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f82,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f108,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f64,f82])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f42])).

fof(f81,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f36])).

fof(f56,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f104,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f60])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f62,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f102,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f60])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f17,axiom,(
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

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f48])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f40])).

fof(f80,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f30,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f69,plain,(
    ! [X0] :
      ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f111,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f69,f82])).

fof(f106,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f60])).

fof(f16,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f47,plain,(
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
    inference(flattening,[],[f46])).

fof(f86,plain,(
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
    inference(cnf_transformation,[],[f47])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f19,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f53,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f52])).

fof(f95,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f94,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_funct_1(X2))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f113,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f76])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f28,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f68,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f61,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
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

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f112,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f71,f82])).

fof(f67,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f3,axiom,(
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

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X1)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f107,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_867,plain,
    ( X0_50 != X1_50
    | k2_funct_1(X0_50) = k2_funct_1(X1_50) ),
    theory(equality)).

cnf(c_82192,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = k2_funct_1(sK2)
    | k2_funct_1(sK3) != sK2 ),
    inference(instantiation,[status(thm)],[c_867])).

cnf(c_865,plain,
    ( X0_50 != X1_50
    | X2_50 != X1_50
    | X2_50 = X0_50 ),
    theory(equality)).

cnf(c_64456,plain,
    ( X0_50 != X1_50
    | X0_50 = k2_funct_1(X2_50)
    | k2_funct_1(X2_50) != X1_50 ),
    inference(instantiation,[status(thm)],[c_865])).

cnf(c_66274,plain,
    ( X0_50 != k2_funct_1(X1_50)
    | X0_50 = k2_funct_1(X2_50)
    | k2_funct_1(X2_50) != k2_funct_1(X1_50) ),
    inference(instantiation,[status(thm)],[c_64456])).

cnf(c_67000,plain,
    ( k2_funct_1(X0_50) != k2_funct_1(X0_50)
    | k2_funct_1(X1_50) != k2_funct_1(X0_50)
    | k2_funct_1(X0_50) = k2_funct_1(X1_50) ),
    inference(instantiation,[status(thm)],[c_66274])).

cnf(c_72469,plain,
    ( k2_funct_1(k2_funct_1(sK3)) != k2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_funct_1(k2_funct_1(sK3))
    | k2_funct_1(sK2) != k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_67000])).

cnf(c_63481,plain,
    ( k2_funct_1(sK2) != X0_50
    | k2_funct_1(sK2) = sK3
    | sK3 != X0_50 ),
    inference(instantiation,[status(thm)],[c_865])).

cnf(c_69903,plain,
    ( k2_funct_1(sK2) != k2_funct_1(k2_funct_1(sK3))
    | k2_funct_1(sK2) = sK3
    | sK3 != k2_funct_1(k2_funct_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_63481])).

cnf(c_21,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_38,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_519,plain,
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
    inference(resolution_lifted,[status(thm)],[c_21,c_38])).

cnf(c_520,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0
    | k6_partfun1(sK0) != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_519])).

cnf(c_612,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_520])).

cnf(c_819,plain,
    ( ~ v1_funct_2(X0_50,X0_51,sK0)
    | ~ v1_funct_2(X1_50,sK0,X0_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK0)))
    | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_51)))
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(X1_50)
    | k2_relset_1(X0_51,sK0,X0_50) = sK0
    | k1_partfun1(sK0,X0_51,X0_51,sK0,X1_50,X0_50) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_612])).

cnf(c_1528,plain,
    ( k2_relset_1(X0_51,sK0,X0_50) = sK0
    | k1_partfun1(sK0,X0_51,X0_51,sK0,X1_50,X0_50) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | v1_funct_2(X0_50,X0_51,sK0) != iProver_top
    | v1_funct_2(X1_50,sK0,X0_51) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK0))) != iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_funct_1(X1_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_819])).

cnf(c_2003,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1528])).

cnf(c_45,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_44,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_43,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_42,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_41,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_40,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1609,plain,
    ( ~ v1_funct_2(X0_50,sK0,sK1)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(sK3)
    | k2_relset_1(sK1,sK0,sK3) = sK0
    | k1_partfun1(sK0,sK1,sK1,sK0,X0_50,sK3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_819])).

cnf(c_1611,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(sK1,sK0,sK3) = sK0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1609])).

cnf(c_861,plain,
    ( X0_50 = X0_50 ),
    theory(equality)).

cnf(c_1776,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_861])).

cnf(c_2060,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2003,c_45,c_44,c_43,c_42,c_41,c_40,c_1611,c_1776])).

cnf(c_30,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_836,plain,
    ( ~ v1_funct_2(X0_50,X0_51,X1_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ v2_funct_1(X0_50)
    | ~ v1_funct_1(X0_50)
    | k2_relset_1(X0_51,X1_51,X0_50) != X1_51
    | k1_xboole_0 = X1_51
    | k5_relat_1(X0_50,k2_funct_1(X0_50)) = k6_partfun1(X0_51) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_1515,plain,
    ( k2_relset_1(X0_51,X1_51,X0_50) != X1_51
    | k1_xboole_0 = X1_51
    | k5_relat_1(X0_50,k2_funct_1(X0_50)) = k6_partfun1(X0_51)
    | v1_funct_2(X0_50,X0_51,X1_51) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v2_funct_1(X0_50) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_836])).

cnf(c_5224,plain,
    ( sK0 = k1_xboole_0
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2060,c_1515])).

cnf(c_49,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_50,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_51,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_862,plain,
    ( X0_51 = X0_51 ),
    theory(equality)).

cnf(c_897,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_862])).

cnf(c_36,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f105])).

cnf(c_831,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(subtyping,[status(esa)],[c_36])).

cnf(c_866,plain,
    ( X0_51 != X1_51
    | X2_51 != X1_51
    | X2_51 = X0_51 ),
    theory(equality)).

cnf(c_1585,plain,
    ( sK0 != X0_51
    | k1_xboole_0 != X0_51
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_866])).

cnf(c_1586,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1585])).

cnf(c_2,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_857,plain,
    ( v2_funct_1(k6_partfun1(X0_51)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_5082,plain,
    ( v2_funct_1(k6_partfun1(sK0)) ),
    inference(instantiation,[status(thm)],[c_857])).

cnf(c_5083,plain,
    ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5082])).

cnf(c_825,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_43])).

cnf(c_1522,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_825])).

cnf(c_828,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subtyping,[status(esa)],[c_40])).

cnf(c_1519,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_828])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_844,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51)))
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(X1_50)
    | k1_partfun1(X2_51,X3_51,X0_51,X1_51,X1_50,X0_50) = k5_relat_1(X1_50,X0_50) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1507,plain,
    ( k1_partfun1(X0_51,X1_51,X2_51,X3_51,X0_50,X1_50) = k5_relat_1(X0_50,X1_50)
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51))) != iProver_top
    | v1_funct_1(X1_50) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_844])).

cnf(c_3887,plain,
    ( k1_partfun1(X0_51,X1_51,sK1,sK0,X0_50,sK3) = k5_relat_1(X0_50,sK3)
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1519,c_1507])).

cnf(c_4013,plain,
    ( v1_funct_1(X0_50) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | k1_partfun1(X0_51,X1_51,sK1,sK0,X0_50,sK3) = k5_relat_1(X0_50,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3887,c_49])).

cnf(c_4014,plain,
    ( k1_partfun1(X0_51,X1_51,sK1,sK0,X0_50,sK3) = k5_relat_1(X0_50,sK3)
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(renaming,[status(thm)],[c_4013])).

cnf(c_4020,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1522,c_4014])).

cnf(c_2434,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_844])).

cnf(c_4311,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4020,c_45,c_43,c_42,c_40,c_2434])).

cnf(c_15,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_506,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_38])).

cnf(c_507,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_506])).

cnf(c_820,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_507])).

cnf(c_1527,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_820])).

cnf(c_4314,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4311,c_1527])).

cnf(c_46,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_47,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_48,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_37,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_53,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_859,plain,
    ( ~ v1_relat_1(X0_50)
    | ~ v1_funct_1(X0_50)
    | v1_funct_1(k2_funct_1(X0_50)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_900,plain,
    ( v1_relat_1(X0_50) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_funct_1(k2_funct_1(X0_50)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_859])).

cnf(c_902,plain,
    ( v1_relat_1(sK2) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_900])).

cnf(c_39,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_829,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(subtyping,[status(esa)],[c_39])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_848,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | v1_relat_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1624,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_848])).

cnf(c_1685,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1624])).

cnf(c_1686,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1685])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_839,plain,
    ( ~ v1_funct_2(X0_50,X0_51,X1_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | m1_subset_1(k2_funct_1(X0_50),k1_zfmisc_1(k2_zfmisc_1(X1_51,X0_51)))
    | ~ v2_funct_1(X0_50)
    | ~ v1_funct_1(X0_50)
    | k2_relset_1(X0_51,X1_51,X0_50) != X1_51 ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_2249,plain,
    ( ~ v1_funct_2(X0_50,sK0,sK1)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | m1_subset_1(k2_funct_1(X0_50),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v2_funct_1(X0_50)
    | ~ v1_funct_1(X0_50)
    | k2_relset_1(sK0,sK1,X0_50) != sK1 ),
    inference(instantiation,[status(thm)],[c_839])).

cnf(c_2250,plain,
    ( k2_relset_1(sK0,sK1,X0_50) != sK1
    | v1_funct_2(X0_50,sK0,sK1) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(k2_funct_1(X0_50),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
    | v2_funct_1(X0_50) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2249])).

cnf(c_2252,plain,
    ( k2_relset_1(sK0,sK1,sK2) != sK1
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2250])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_846,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51)))
    | m1_subset_1(k1_partfun1(X2_51,X3_51,X0_51,X1_51,X1_50,X0_50),k1_zfmisc_1(k2_zfmisc_1(X2_51,X1_51)))
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(X1_50) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1505,plain,
    ( m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51))) != iProver_top
    | m1_subset_1(k1_partfun1(X0_51,X1_51,X2_51,X3_51,X0_50,X1_50),k1_zfmisc_1(k2_zfmisc_1(X0_51,X3_51))) = iProver_top
    | v1_funct_1(X1_50) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_846])).

cnf(c_4898,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4311,c_1505])).

cnf(c_1512,plain,
    ( k2_relset_1(X0_51,X1_51,X0_50) != X1_51
    | v1_funct_2(X0_50,X0_51,X1_51) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | m1_subset_1(k2_funct_1(X0_50),k1_zfmisc_1(k2_zfmisc_1(X1_51,X0_51))) = iProver_top
    | v2_funct_1(X0_50) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_839])).

cnf(c_5089,plain,
    ( v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_829,c_1512])).

cnf(c_5099,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5089,c_46,c_47,c_48,c_53,c_829,c_2252])).

cnf(c_5108,plain,
    ( k1_partfun1(X0_51,X1_51,sK1,sK0,X0_50,k2_funct_1(sK2)) = k5_relat_1(X0_50,k2_funct_1(sK2))
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5099,c_1507])).

cnf(c_5297,plain,
    ( v1_funct_1(X0_50) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | k1_partfun1(X0_51,X1_51,sK1,sK0,X0_50,k2_funct_1(sK2)) = k5_relat_1(X0_50,k2_funct_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5108,c_46,c_48,c_902,c_1686])).

cnf(c_5298,plain,
    ( k1_partfun1(X0_51,X1_51,sK1,sK0,X0_50,k2_funct_1(sK2)) = k5_relat_1(X0_50,k2_funct_1(sK2))
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(renaming,[status(thm)],[c_5297])).

cnf(c_5304,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2))
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1522,c_5298])).

cnf(c_830,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_37])).

cnf(c_1518,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_830])).

cnf(c_9,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_850,plain,
    ( ~ v2_funct_1(X0_50)
    | ~ v1_relat_1(X0_50)
    | ~ v1_funct_1(X0_50)
    | k5_relat_1(X0_50,k2_funct_1(X0_50)) = k6_partfun1(k1_relat_1(X0_50)) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1501,plain,
    ( k5_relat_1(X0_50,k2_funct_1(X0_50)) = k6_partfun1(k1_relat_1(X0_50))
    | v2_funct_1(X0_50) != iProver_top
    | v1_relat_1(X0_50) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_850])).

cnf(c_3274,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1518,c_1501])).

cnf(c_920,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_850])).

cnf(c_3552,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3274,c_45,c_43,c_37,c_920,c_1685])).

cnf(c_5312,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5304,c_3552])).

cnf(c_5856,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5312,c_46])).

cnf(c_5223,plain,
    ( sK1 = k1_xboole_0
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_829,c_1515])).

cnf(c_5228,plain,
    ( sK1 = k1_xboole_0
    | k6_partfun1(k1_relat_1(sK2)) = k6_partfun1(sK0)
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5223,c_3552])).

cnf(c_35,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f106])).

cnf(c_832,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(subtyping,[status(esa)],[c_35])).

cnf(c_1597,plain,
    ( sK1 != X0_51
    | k1_xboole_0 != X0_51
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_866])).

cnf(c_1598,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1597])).

cnf(c_5418,plain,
    ( k6_partfun1(k1_relat_1(sK2)) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5228,c_46,c_47,c_48,c_53,c_897,c_832,c_1598])).

cnf(c_5858,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
    inference(light_normalisation,[status(thm)],[c_5856,c_5418])).

cnf(c_5859,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5858,c_1505])).

cnf(c_8888,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4314,c_46,c_47,c_48,c_49,c_51,c_53,c_902,c_829,c_1686,c_2252,c_4898,c_5859])).

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
    inference(cnf_transformation,[],[f86])).

cnf(c_842,plain,
    ( ~ v1_funct_2(X0_50,X0_51,X1_51)
    | ~ v1_funct_2(X1_50,X2_51,X0_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X0_51)))
    | v2_funct_1(X0_50)
    | ~ v2_funct_1(k1_partfun1(X2_51,X0_51,X0_51,X1_51,X1_50,X0_50))
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(X1_50)
    | k2_relset_1(X2_51,X0_51,X1_50) != X0_51
    | k1_xboole_0 = X1_51 ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1509,plain,
    ( k2_relset_1(X0_51,X1_51,X0_50) != X1_51
    | k1_xboole_0 = X2_51
    | v1_funct_2(X1_50,X1_51,X2_51) != iProver_top
    | v1_funct_2(X0_50,X0_51,X1_51) != iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51))) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v2_funct_1(X1_50) = iProver_top
    | v2_funct_1(k1_partfun1(X0_51,X1_51,X1_51,X2_51,X0_50,X1_50)) != iProver_top
    | v1_funct_1(X1_50) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_842])).

cnf(c_5569,plain,
    ( k1_xboole_0 = X0_51
    | v1_funct_2(X0_50,sK1,X0_51) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK1,X0_51))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v2_funct_1(X0_50) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0_51,sK2,X0_50)) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_829,c_1509])).

cnf(c_5582,plain,
    ( v1_funct_1(X0_50) != iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0_51,sK2,X0_50)) != iProver_top
    | v2_funct_1(X0_50) = iProver_top
    | v1_funct_2(X0_50,sK1,X0_51) != iProver_top
    | k1_xboole_0 = X0_51
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK1,X0_51))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5569,c_46,c_47,c_48])).

cnf(c_5583,plain,
    ( k1_xboole_0 = X0_51
    | v1_funct_2(X0_50,sK1,X0_51) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK1,X0_51))) != iProver_top
    | v2_funct_1(X0_50) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0_51,sK2,X0_50)) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(renaming,[status(thm)],[c_5582])).

cnf(c_5586,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4311,c_5583])).

cnf(c_5696,plain,
    ( v2_funct_1(sK3) = iProver_top
    | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5586,c_49,c_50,c_51,c_897,c_831,c_1586])).

cnf(c_5697,plain,
    ( v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_5696])).

cnf(c_8890,plain,
    ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8888,c_5697])).

cnf(c_33931,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5224,c_49,c_50,c_51,c_897,c_831,c_1586,c_5083,c_8890])).

cnf(c_8989,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8890,c_5083])).

cnf(c_8993,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_8989,c_1501])).

cnf(c_1885,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_848])).

cnf(c_1994,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1885])).

cnf(c_1995,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1994])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_847,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | k2_relset_1(X0_51,X1_51,X0_50) = k2_relat_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1504,plain,
    ( k2_relset_1(X0_51,X1_51,X0_50) = k2_relat_1(X0_50)
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_847])).

cnf(c_2358,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1519,c_1504])).

cnf(c_2361,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_2358,c_2060])).

cnf(c_31,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_835,plain,
    ( m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_50),k2_relat_1(X0_50))))
    | ~ v1_relat_1(X0_50)
    | ~ v1_funct_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_1516,plain,
    ( m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_50),k2_relat_1(X0_50)))) = iProver_top
    | v1_relat_1(X0_50) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_835])).

cnf(c_2587,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK0))) = iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2361,c_1516])).

cnf(c_32,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_834,plain,
    ( v1_funct_2(X0_50,k1_relat_1(X0_50),k2_relat_1(X0_50))
    | ~ v1_relat_1(X0_50)
    | ~ v1_funct_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_32])).

cnf(c_1517,plain,
    ( v1_funct_2(X0_50,k1_relat_1(X0_50),k2_relat_1(X0_50)) = iProver_top
    | v1_relat_1(X0_50) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_834])).

cnf(c_2588,plain,
    ( v1_funct_2(sK3,k1_relat_1(sK3),sK0) = iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2361,c_1517])).

cnf(c_2713,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2587,c_49,c_51,c_1995])).

cnf(c_2717,plain,
    ( k2_relset_1(k1_relat_1(sK3),sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2713,c_1504])).

cnf(c_2719,plain,
    ( k2_relset_1(k1_relat_1(sK3),sK0,sK3) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_2717,c_2361])).

cnf(c_5226,plain,
    ( sK0 = k1_xboole_0
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
    | v1_funct_2(sK3,k1_relat_1(sK3),sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK0))) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2719,c_1515])).

cnf(c_9174,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8993,c_49,c_51,c_897,c_831,c_1586,c_1995,c_2587,c_2588,c_5083,c_5226,c_8890])).

cnf(c_33933,plain,
    ( k6_partfun1(k1_relat_1(sK3)) = k6_partfun1(sK1) ),
    inference(demodulation,[status(thm)],[c_33931,c_9174])).

cnf(c_5090,plain,
    ( v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2060,c_1512])).

cnf(c_26223,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5090,c_49,c_50,c_51,c_5083,c_8890])).

cnf(c_26242,plain,
    ( k1_partfun1(X0_51,X1_51,sK0,sK1,X0_50,k2_funct_1(sK3)) = k5_relat_1(X0_50,k2_funct_1(sK3))
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_26223,c_1507])).

cnf(c_28,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_245,plain,
    ( v1_funct_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_28,c_11,c_0])).

cnf(c_246,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0)) ),
    inference(renaming,[status(thm)],[c_245])).

cnf(c_822,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ v1_funct_1(X0_50)
    | v1_funct_1(k2_funct_1(X0_50)) ),
    inference(subtyping,[status(esa)],[c_246])).

cnf(c_1525,plain,
    ( m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_funct_1(k2_funct_1(X0_50)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_822])).

cnf(c_2820,plain,
    ( v1_funct_1(k2_funct_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2713,c_1525])).

cnf(c_26405,plain,
    ( v1_funct_1(X0_50) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | k1_partfun1(X0_51,X1_51,sK0,sK1,X0_50,k2_funct_1(sK3)) = k5_relat_1(X0_50,k2_funct_1(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_26242,c_49,c_2820])).

cnf(c_26406,plain,
    ( k1_partfun1(X0_51,X1_51,sK0,sK1,X0_50,k2_funct_1(sK3)) = k5_relat_1(X0_50,k2_funct_1(sK3))
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(renaming,[status(thm)],[c_26405])).

cnf(c_26411,plain,
    ( k1_partfun1(sK1,sK0,sK0,sK1,sK3,k2_funct_1(sK3)) = k5_relat_1(sK3,k2_funct_1(sK3))
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1519,c_26406])).

cnf(c_26435,plain,
    ( k1_partfun1(sK1,sK0,sK0,sK1,sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
    | v1_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_26411,c_9174])).

cnf(c_26687,plain,
    ( k1_partfun1(sK1,sK0,sK0,sK1,sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_26435,c_49])).

cnf(c_14,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_471,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | X1 != X6
    | X1 != X5
    | k1_partfun1(X1,X2,X2,X1,X0,X3) != X4
    | k2_relset_1(X2,X1,X3) = X1
    | k6_partfun1(X1) != X4 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_21])).

cnf(c_472,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ m1_subset_1(k1_partfun1(X1,X2,X2,X1,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X2,X1,X3) = X1
    | k6_partfun1(X1) != k1_partfun1(X1,X2,X2,X1,X0,X3) ),
    inference(unflattening,[status(thm)],[c_471])).

cnf(c_494,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X2,X1,X3) = X1
    | k6_partfun1(X1) != k1_partfun1(X1,X2,X2,X1,X0,X3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_472,c_18])).

cnf(c_821,plain,
    ( ~ v1_funct_2(X0_50,X0_51,X1_51)
    | ~ v1_funct_2(X1_50,X1_51,X0_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X1_51,X0_51)))
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(X1_50)
    | k2_relset_1(X1_51,X0_51,X1_50) = X0_51
    | k6_partfun1(X0_51) != k1_partfun1(X0_51,X1_51,X1_51,X0_51,X0_50,X1_50) ),
    inference(subtyping,[status(esa)],[c_494])).

cnf(c_1526,plain,
    ( k2_relset_1(X0_51,X1_51,X0_50) = X1_51
    | k6_partfun1(X1_51) != k1_partfun1(X1_51,X0_51,X0_51,X1_51,X1_50,X0_50)
    | v1_funct_2(X1_50,X1_51,X0_51) != iProver_top
    | v1_funct_2(X0_50,X0_51,X1_51) != iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X1_51,X0_51))) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X1_50) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_821])).

cnf(c_26693,plain,
    ( k2_relset_1(sK0,sK1,k2_funct_1(sK3)) = sK1
    | k6_partfun1(k1_relat_1(sK3)) != k6_partfun1(sK1)
    | v1_funct_2(k2_funct_1(sK3),sK0,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_26687,c_1526])).

cnf(c_26240,plain,
    ( k2_relset_1(sK0,sK1,k2_funct_1(sK3)) = k2_relat_1(k2_funct_1(sK3)) ),
    inference(superposition,[status(thm)],[c_26223,c_1504])).

cnf(c_6,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_853,plain,
    ( ~ v2_funct_1(X0_50)
    | ~ v1_relat_1(X0_50)
    | ~ v1_funct_1(X0_50)
    | k2_relat_1(k2_funct_1(X0_50)) = k1_relat_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1498,plain,
    ( k2_relat_1(k2_funct_1(X0_50)) = k1_relat_1(X0_50)
    | v2_funct_1(X0_50) != iProver_top
    | v1_relat_1(X0_50) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_853])).

cnf(c_8996,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_8989,c_1498])).

cnf(c_9009,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8996,c_49,c_51,c_1995])).

cnf(c_26245,plain,
    ( k2_relset_1(sK0,sK1,k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(light_normalisation,[status(thm)],[c_26240,c_9009])).

cnf(c_26694,plain,
    ( k1_relat_1(sK3) = sK1
    | k6_partfun1(k1_relat_1(sK3)) != k6_partfun1(sK1)
    | v1_funct_2(k2_funct_1(sK3),sK0,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_26693,c_26245])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_858,plain,
    ( ~ v1_relat_1(X0_50)
    | v1_relat_1(k2_funct_1(X0_50))
    | ~ v1_funct_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_22705,plain,
    ( v1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_858])).

cnf(c_2616,plain,
    ( X0_50 != X1_50
    | X0_50 = k2_funct_1(X2_50)
    | k2_funct_1(X2_50) != X1_50 ),
    inference(instantiation,[status(thm)],[c_865])).

cnf(c_7967,plain,
    ( X0_50 != X1_50
    | X0_50 = k2_funct_1(k2_funct_1(X1_50))
    | k2_funct_1(k2_funct_1(X1_50)) != X1_50 ),
    inference(instantiation,[status(thm)],[c_2616])).

cnf(c_22163,plain,
    ( k2_funct_1(k2_funct_1(X0_50)) != X0_50
    | k2_funct_1(sK3) != X0_50
    | k2_funct_1(sK3) = k2_funct_1(k2_funct_1(X0_50)) ),
    inference(instantiation,[status(thm)],[c_7967])).

cnf(c_22168,plain,
    ( k2_funct_1(k2_funct_1(sK2)) != sK2
    | k2_funct_1(sK3) = k2_funct_1(k2_funct_1(sK2))
    | k2_funct_1(sK3) != sK2 ),
    inference(instantiation,[status(thm)],[c_22163])).

cnf(c_871,plain,
    ( ~ v2_funct_1(X0_50)
    | v2_funct_1(X1_50)
    | X1_50 != X0_50 ),
    theory(equality)).

cnf(c_1814,plain,
    ( ~ v2_funct_1(X0_50)
    | v2_funct_1(k2_funct_1(X1_50))
    | k2_funct_1(X1_50) != X0_50 ),
    inference(instantiation,[status(thm)],[c_871])).

cnf(c_2071,plain,
    ( ~ v2_funct_1(k2_funct_1(X0_50))
    | v2_funct_1(k2_funct_1(X1_50))
    | k2_funct_1(X1_50) != k2_funct_1(X0_50) ),
    inference(instantiation,[status(thm)],[c_1814])).

cnf(c_9235,plain,
    ( ~ v2_funct_1(k2_funct_1(X0_50))
    | v2_funct_1(k2_funct_1(sK3))
    | k2_funct_1(sK3) != k2_funct_1(X0_50) ),
    inference(instantiation,[status(thm)],[c_2071])).

cnf(c_22162,plain,
    ( ~ v2_funct_1(k2_funct_1(k2_funct_1(X0_50)))
    | v2_funct_1(k2_funct_1(sK3))
    | k2_funct_1(sK3) != k2_funct_1(k2_funct_1(X0_50)) ),
    inference(instantiation,[status(thm)],[c_9235])).

cnf(c_22165,plain,
    ( ~ v2_funct_1(k2_funct_1(k2_funct_1(sK2)))
    | v2_funct_1(k2_funct_1(sK3))
    | k2_funct_1(sK3) != k2_funct_1(k2_funct_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_22162])).

cnf(c_10,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
    | k1_relat_1(X0) != k2_relat_1(X1)
    | k2_funct_1(X0) = X1 ),
    inference(cnf_transformation,[],[f112])).

cnf(c_849,plain,
    ( ~ v2_funct_1(X0_50)
    | ~ v1_relat_1(X0_50)
    | ~ v1_relat_1(X1_50)
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(X1_50)
    | k1_relat_1(X0_50) != k2_relat_1(X1_50)
    | k5_relat_1(X1_50,X0_50) != k6_partfun1(k2_relat_1(X0_50))
    | k2_funct_1(X0_50) = X1_50 ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1502,plain,
    ( k1_relat_1(X0_50) != k2_relat_1(X1_50)
    | k5_relat_1(X1_50,X0_50) != k6_partfun1(k2_relat_1(X0_50))
    | k2_funct_1(X0_50) = X1_50
    | v2_funct_1(X0_50) != iProver_top
    | v1_relat_1(X0_50) != iProver_top
    | v1_relat_1(X1_50) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_funct_1(X1_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_849])).

cnf(c_8894,plain,
    ( k1_relat_1(sK3) != k2_relat_1(sK2)
    | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
    | k2_funct_1(sK3) = sK2
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_8888,c_1502])).

cnf(c_2359,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1522,c_1504])).

cnf(c_2360,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2359,c_829])).

cnf(c_8895,plain,
    ( k1_relat_1(sK3) != sK1
    | k6_partfun1(sK0) != k6_partfun1(sK0)
    | k2_funct_1(sK3) = sK2
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8894,c_2360,c_2361])).

cnf(c_8896,plain,
    ( k1_relat_1(sK3) != sK1
    | k2_funct_1(sK3) = sK2
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_8895])).

cnf(c_10318,plain,
    ( k2_funct_1(sK3) = sK2
    | k1_relat_1(sK3) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8896,c_46,c_48,c_49,c_51,c_1686,c_1995,c_5083,c_8890])).

cnf(c_10319,plain,
    ( k1_relat_1(sK3) != sK1
    | k2_funct_1(sK3) = sK2 ),
    inference(renaming,[status(thm)],[c_10318])).

cnf(c_9176,plain,
    ( k1_relat_1(k2_funct_1(sK3)) != k2_relat_1(sK3)
    | k6_partfun1(k2_relat_1(k2_funct_1(sK3))) != k6_partfun1(k1_relat_1(sK3))
    | k2_funct_1(k2_funct_1(sK3)) = sK3
    | v2_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_9174,c_1502])).

cnf(c_9177,plain,
    ( k1_relat_1(k2_funct_1(sK3)) != sK0
    | k6_partfun1(k1_relat_1(sK3)) != k6_partfun1(k1_relat_1(sK3))
    | k2_funct_1(k2_funct_1(sK3)) = sK3
    | v2_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9176,c_2361,c_9009])).

cnf(c_9178,plain,
    ( k1_relat_1(k2_funct_1(sK3)) != sK0
    | k2_funct_1(k2_funct_1(sK3)) = sK3
    | v2_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_9177])).

cnf(c_9179,plain,
    ( ~ v2_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | k1_relat_1(k2_funct_1(sK3)) != sK0
    | k2_funct_1(k2_funct_1(sK3)) = sK3 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_9178])).

cnf(c_7,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_852,plain,
    ( ~ v2_funct_1(X0_50)
    | ~ v1_relat_1(X0_50)
    | ~ v1_funct_1(X0_50)
    | k1_relat_1(k2_funct_1(X0_50)) = k2_relat_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1499,plain,
    ( k1_relat_1(k2_funct_1(X0_50)) = k2_relat_1(X0_50)
    | v2_funct_1(X0_50) != iProver_top
    | v1_relat_1(X0_50) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_852])).

cnf(c_8995,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_8989,c_1499])).

cnf(c_8997,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = sK0
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8995,c_2361])).

cnf(c_1637,plain,
    ( X0_50 != X1_50
    | sK3 != X1_50
    | sK3 = X0_50 ),
    inference(instantiation,[status(thm)],[c_865])).

cnf(c_1787,plain,
    ( X0_50 != sK3
    | sK3 = X0_50
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1637])).

cnf(c_7920,plain,
    ( k2_funct_1(k2_funct_1(sK3)) != sK3
    | sK3 = k2_funct_1(k2_funct_1(sK3))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1787])).

cnf(c_7911,plain,
    ( ~ v2_funct_1(X0_50)
    | v2_funct_1(k2_funct_1(k2_funct_1(X0_50)))
    | k2_funct_1(k2_funct_1(X0_50)) != X0_50 ),
    inference(instantiation,[status(thm)],[c_1814])).

cnf(c_7913,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1(sK2)))
    | ~ v2_funct_1(sK2)
    | k2_funct_1(k2_funct_1(sK2)) != sK2 ),
    inference(instantiation,[status(thm)],[c_7911])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_838,plain,
    ( ~ v1_funct_2(X0_50,X0_51,X1_51)
    | v1_funct_2(k2_funct_1(X0_50),X1_51,X0_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ v2_funct_1(X0_50)
    | ~ v1_funct_1(X0_50)
    | k2_relset_1(X0_51,X1_51,X0_50) != X1_51 ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_1513,plain,
    ( k2_relset_1(X0_51,X1_51,X0_50) != X1_51
    | v1_funct_2(X0_50,X0_51,X1_51) != iProver_top
    | v1_funct_2(k2_funct_1(X0_50),X1_51,X0_51) = iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v2_funct_1(X0_50) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_838])).

cnf(c_3913,plain,
    ( v1_funct_2(k2_funct_1(sK3),sK0,sK1) = iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2060,c_1513])).

cnf(c_3742,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2)
    | k6_partfun1(k2_relat_1(k2_funct_1(sK2))) != k6_partfun1(k1_relat_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = sK2
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3552,c_1502])).

cnf(c_3211,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1518,c_1499])).

cnf(c_3213,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK1
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3211,c_2360])).

cnf(c_3281,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3213,c_46,c_48,c_1686])).

cnf(c_3022,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1518,c_1498])).

cnf(c_911,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_853])).

cnf(c_3372,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3022,c_45,c_43,c_37,c_911,c_1685])).

cnf(c_3743,plain,
    ( sK1 != sK1
    | k6_partfun1(k1_relat_1(sK2)) != k6_partfun1(k1_relat_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = sK2
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3742,c_2360,c_3281,c_3372])).

cnf(c_3744,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3743])).

cnf(c_5,plain,
    ( v2_funct_1(X0)
    | ~ v2_funct_1(k5_relat_1(X0,X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | k1_relat_1(X1) != k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_854,plain,
    ( v2_funct_1(X0_50)
    | ~ v2_funct_1(k5_relat_1(X0_50,X1_50))
    | ~ v1_relat_1(X0_50)
    | ~ v1_relat_1(X1_50)
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(X1_50)
    | k1_relat_1(X1_50) != k2_relat_1(X0_50) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1497,plain,
    ( k1_relat_1(X0_50) != k2_relat_1(X1_50)
    | v2_funct_1(X1_50) = iProver_top
    | v2_funct_1(k5_relat_1(X1_50,X0_50)) != iProver_top
    | v1_relat_1(X1_50) != iProver_top
    | v1_relat_1(X0_50) != iProver_top
    | v1_funct_1(X1_50) != iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_854])).

cnf(c_3376,plain,
    ( k1_relat_1(X0_50) != k1_relat_1(sK2)
    | v2_funct_1(k5_relat_1(k2_funct_1(sK2),X0_50)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(X0_50) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3372,c_1497])).

cnf(c_3381,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | v2_funct_1(k5_relat_1(k2_funct_1(sK2),sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3376])).

cnf(c_2975,plain,
    ( v2_funct_1(k6_partfun1(sK1)) ),
    inference(instantiation,[status(thm)],[c_857])).

cnf(c_2976,plain,
    ( v2_funct_1(k6_partfun1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2975])).

cnf(c_2821,plain,
    ( v1_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2820])).

cnf(c_2104,plain,
    ( ~ v2_funct_1(X0_50)
    | v2_funct_1(k5_relat_1(k2_funct_1(X1_50),X2_50))
    | k5_relat_1(k2_funct_1(X1_50),X2_50) != X0_50 ),
    inference(instantiation,[status(thm)],[c_871])).

cnf(c_2481,plain,
    ( v2_funct_1(k5_relat_1(k2_funct_1(sK2),sK2))
    | ~ v2_funct_1(k6_partfun1(sK1))
    | k5_relat_1(k2_funct_1(sK2),sK2) != k6_partfun1(sK1) ),
    inference(instantiation,[status(thm)],[c_2104])).

cnf(c_2482,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) != k6_partfun1(sK1)
    | v2_funct_1(k5_relat_1(k2_funct_1(sK2),sK2)) = iProver_top
    | v2_funct_1(k6_partfun1(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2481])).

cnf(c_2045,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_861])).

cnf(c_29,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_837,plain,
    ( ~ v1_funct_2(X0_50,X0_51,X1_51)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ v2_funct_1(X0_50)
    | ~ v1_funct_1(X0_50)
    | k2_relset_1(X0_51,X1_51,X0_50) != X1_51
    | k1_xboole_0 = X1_51
    | k5_relat_1(k2_funct_1(X0_50),X0_50) = k6_partfun1(X1_51) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_1588,plain,
    ( ~ v1_funct_2(X0_50,X0_51,sK1)
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1)))
    | ~ v2_funct_1(X0_50)
    | ~ v1_funct_1(X0_50)
    | k2_relset_1(X0_51,sK1,X0_50) != sK1
    | k1_xboole_0 = sK1
    | k5_relat_1(k2_funct_1(X0_50),X0_50) = k6_partfun1(sK1) ),
    inference(instantiation,[status(thm)],[c_837])).

cnf(c_1654,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(sK0,sK1,sK2) != sK1
    | k1_xboole_0 = sK1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(instantiation,[status(thm)],[c_1588])).

cnf(c_34,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f107])).

cnf(c_833,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(subtyping,[status(esa)],[c_34])).

cnf(c_903,plain,
    ( v1_relat_1(X0_50) != iProver_top
    | v1_relat_1(k2_funct_1(X0_50)) = iProver_top
    | v1_funct_1(X0_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_858])).

cnf(c_905,plain,
    ( v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_903])).

cnf(c_896,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_861])).

cnf(c_873,plain,
    ( k1_relat_1(X0_50) = k1_relat_1(X1_50)
    | X0_50 != X1_50 ),
    theory(equality)).

cnf(c_887,plain,
    ( k1_relat_1(sK2) = k1_relat_1(sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_873])).

cnf(c_881,plain,
    ( k2_funct_1(sK2) = k2_funct_1(sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_867])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_82192,c_72469,c_69903,c_33933,c_26694,c_22705,c_22168,c_22165,c_10319,c_9179,c_8997,c_8890,c_7920,c_7913,c_5090,c_5083,c_3913,c_3744,c_3381,c_2976,c_2821,c_2820,c_2482,c_2045,c_1995,c_1994,c_1686,c_1654,c_829,c_832,c_833,c_905,c_902,c_896,c_887,c_881,c_37,c_51,c_40,c_50,c_49,c_42,c_48,c_43,c_44,c_46,c_45])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:23:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 31.51/4.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 31.51/4.49  
% 31.51/4.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 31.51/4.49  
% 31.51/4.49  ------  iProver source info
% 31.51/4.49  
% 31.51/4.49  git: date: 2020-06-30 10:37:57 +0100
% 31.51/4.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 31.51/4.49  git: non_committed_changes: false
% 31.51/4.49  git: last_make_outside_of_git: false
% 31.51/4.49  
% 31.51/4.49  ------ 
% 31.51/4.49  
% 31.51/4.49  ------ Input Options
% 31.51/4.49  
% 31.51/4.49  --out_options                           all
% 31.51/4.49  --tptp_safe_out                         true
% 31.51/4.49  --problem_path                          ""
% 31.51/4.49  --include_path                          ""
% 31.51/4.49  --clausifier                            res/vclausify_rel
% 31.51/4.49  --clausifier_options                    ""
% 31.51/4.49  --stdin                                 false
% 31.51/4.49  --stats_out                             all
% 31.51/4.49  
% 31.51/4.49  ------ General Options
% 31.51/4.49  
% 31.51/4.49  --fof                                   false
% 31.51/4.49  --time_out_real                         305.
% 31.51/4.49  --time_out_virtual                      -1.
% 31.51/4.49  --symbol_type_check                     false
% 31.51/4.49  --clausify_out                          false
% 31.51/4.49  --sig_cnt_out                           false
% 31.51/4.49  --trig_cnt_out                          false
% 31.51/4.49  --trig_cnt_out_tolerance                1.
% 31.51/4.49  --trig_cnt_out_sk_spl                   false
% 31.51/4.49  --abstr_cl_out                          false
% 31.51/4.49  
% 31.51/4.49  ------ Global Options
% 31.51/4.49  
% 31.51/4.49  --schedule                              default
% 31.51/4.49  --add_important_lit                     false
% 31.51/4.49  --prop_solver_per_cl                    1000
% 31.51/4.49  --min_unsat_core                        false
% 31.51/4.49  --soft_assumptions                      false
% 31.51/4.49  --soft_lemma_size                       3
% 31.51/4.49  --prop_impl_unit_size                   0
% 31.51/4.49  --prop_impl_unit                        []
% 31.51/4.49  --share_sel_clauses                     true
% 31.51/4.49  --reset_solvers                         false
% 31.51/4.49  --bc_imp_inh                            [conj_cone]
% 31.51/4.49  --conj_cone_tolerance                   3.
% 31.51/4.49  --extra_neg_conj                        none
% 31.51/4.49  --large_theory_mode                     true
% 31.51/4.49  --prolific_symb_bound                   200
% 31.51/4.49  --lt_threshold                          2000
% 31.51/4.49  --clause_weak_htbl                      true
% 31.51/4.49  --gc_record_bc_elim                     false
% 31.51/4.49  
% 31.51/4.49  ------ Preprocessing Options
% 31.51/4.49  
% 31.51/4.49  --preprocessing_flag                    true
% 31.51/4.49  --time_out_prep_mult                    0.1
% 31.51/4.49  --splitting_mode                        input
% 31.51/4.49  --splitting_grd                         true
% 31.51/4.49  --splitting_cvd                         false
% 31.51/4.49  --splitting_cvd_svl                     false
% 31.51/4.49  --splitting_nvd                         32
% 31.51/4.49  --sub_typing                            true
% 31.51/4.49  --prep_gs_sim                           true
% 31.51/4.49  --prep_unflatten                        true
% 31.51/4.49  --prep_res_sim                          true
% 31.51/4.49  --prep_upred                            true
% 31.51/4.49  --prep_sem_filter                       exhaustive
% 31.51/4.49  --prep_sem_filter_out                   false
% 31.51/4.49  --pred_elim                             true
% 31.51/4.49  --res_sim_input                         true
% 31.51/4.49  --eq_ax_congr_red                       true
% 31.51/4.49  --pure_diseq_elim                       true
% 31.51/4.49  --brand_transform                       false
% 31.51/4.49  --non_eq_to_eq                          false
% 31.51/4.49  --prep_def_merge                        true
% 31.51/4.49  --prep_def_merge_prop_impl              false
% 31.51/4.49  --prep_def_merge_mbd                    true
% 31.51/4.49  --prep_def_merge_tr_red                 false
% 31.51/4.49  --prep_def_merge_tr_cl                  false
% 31.51/4.49  --smt_preprocessing                     true
% 31.51/4.49  --smt_ac_axioms                         fast
% 31.51/4.49  --preprocessed_out                      false
% 31.51/4.49  --preprocessed_stats                    false
% 31.51/4.49  
% 31.51/4.49  ------ Abstraction refinement Options
% 31.51/4.49  
% 31.51/4.49  --abstr_ref                             []
% 31.51/4.49  --abstr_ref_prep                        false
% 31.51/4.49  --abstr_ref_until_sat                   false
% 31.51/4.49  --abstr_ref_sig_restrict                funpre
% 31.51/4.49  --abstr_ref_af_restrict_to_split_sk     false
% 31.51/4.49  --abstr_ref_under                       []
% 31.51/4.49  
% 31.51/4.49  ------ SAT Options
% 31.51/4.49  
% 31.51/4.49  --sat_mode                              false
% 31.51/4.49  --sat_fm_restart_options                ""
% 31.51/4.49  --sat_gr_def                            false
% 31.51/4.49  --sat_epr_types                         true
% 31.51/4.49  --sat_non_cyclic_types                  false
% 31.51/4.49  --sat_finite_models                     false
% 31.51/4.49  --sat_fm_lemmas                         false
% 31.51/4.49  --sat_fm_prep                           false
% 31.51/4.49  --sat_fm_uc_incr                        true
% 31.51/4.49  --sat_out_model                         small
% 31.51/4.49  --sat_out_clauses                       false
% 31.51/4.49  
% 31.51/4.49  ------ QBF Options
% 31.51/4.49  
% 31.51/4.49  --qbf_mode                              false
% 31.51/4.49  --qbf_elim_univ                         false
% 31.51/4.49  --qbf_dom_inst                          none
% 31.51/4.49  --qbf_dom_pre_inst                      false
% 31.51/4.49  --qbf_sk_in                             false
% 31.51/4.49  --qbf_pred_elim                         true
% 31.51/4.49  --qbf_split                             512
% 31.51/4.49  
% 31.51/4.49  ------ BMC1 Options
% 31.51/4.49  
% 31.51/4.49  --bmc1_incremental                      false
% 31.51/4.49  --bmc1_axioms                           reachable_all
% 31.51/4.49  --bmc1_min_bound                        0
% 31.51/4.49  --bmc1_max_bound                        -1
% 31.51/4.49  --bmc1_max_bound_default                -1
% 31.51/4.49  --bmc1_symbol_reachability              true
% 31.51/4.49  --bmc1_property_lemmas                  false
% 31.51/4.49  --bmc1_k_induction                      false
% 31.51/4.49  --bmc1_non_equiv_states                 false
% 31.51/4.49  --bmc1_deadlock                         false
% 31.51/4.49  --bmc1_ucm                              false
% 31.51/4.49  --bmc1_add_unsat_core                   none
% 31.51/4.49  --bmc1_unsat_core_children              false
% 31.51/4.49  --bmc1_unsat_core_extrapolate_axioms    false
% 31.51/4.49  --bmc1_out_stat                         full
% 31.51/4.49  --bmc1_ground_init                      false
% 31.51/4.49  --bmc1_pre_inst_next_state              false
% 31.51/4.49  --bmc1_pre_inst_state                   false
% 31.51/4.49  --bmc1_pre_inst_reach_state             false
% 31.51/4.49  --bmc1_out_unsat_core                   false
% 31.51/4.49  --bmc1_aig_witness_out                  false
% 31.51/4.49  --bmc1_verbose                          false
% 31.51/4.49  --bmc1_dump_clauses_tptp                false
% 31.51/4.49  --bmc1_dump_unsat_core_tptp             false
% 31.51/4.49  --bmc1_dump_file                        -
% 31.51/4.49  --bmc1_ucm_expand_uc_limit              128
% 31.51/4.49  --bmc1_ucm_n_expand_iterations          6
% 31.51/4.49  --bmc1_ucm_extend_mode                  1
% 31.51/4.49  --bmc1_ucm_init_mode                    2
% 31.51/4.49  --bmc1_ucm_cone_mode                    none
% 31.51/4.49  --bmc1_ucm_reduced_relation_type        0
% 31.51/4.49  --bmc1_ucm_relax_model                  4
% 31.51/4.49  --bmc1_ucm_full_tr_after_sat            true
% 31.51/4.49  --bmc1_ucm_expand_neg_assumptions       false
% 31.51/4.49  --bmc1_ucm_layered_model                none
% 31.51/4.49  --bmc1_ucm_max_lemma_size               10
% 31.51/4.49  
% 31.51/4.49  ------ AIG Options
% 31.51/4.49  
% 31.51/4.49  --aig_mode                              false
% 31.51/4.49  
% 31.51/4.49  ------ Instantiation Options
% 31.51/4.49  
% 31.51/4.49  --instantiation_flag                    true
% 31.51/4.49  --inst_sos_flag                         true
% 31.51/4.49  --inst_sos_phase                        true
% 31.51/4.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 31.51/4.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 31.51/4.49  --inst_lit_sel_side                     num_symb
% 31.51/4.49  --inst_solver_per_active                1400
% 31.51/4.49  --inst_solver_calls_frac                1.
% 31.51/4.49  --inst_passive_queue_type               priority_queues
% 31.51/4.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 31.51/4.49  --inst_passive_queues_freq              [25;2]
% 31.51/4.49  --inst_dismatching                      true
% 31.51/4.49  --inst_eager_unprocessed_to_passive     true
% 31.51/4.49  --inst_prop_sim_given                   true
% 31.51/4.49  --inst_prop_sim_new                     false
% 31.51/4.49  --inst_subs_new                         false
% 31.51/4.49  --inst_eq_res_simp                      false
% 31.51/4.49  --inst_subs_given                       false
% 31.51/4.49  --inst_orphan_elimination               true
% 31.51/4.49  --inst_learning_loop_flag               true
% 31.51/4.49  --inst_learning_start                   3000
% 31.51/4.49  --inst_learning_factor                  2
% 31.51/4.49  --inst_start_prop_sim_after_learn       3
% 31.51/4.49  --inst_sel_renew                        solver
% 31.51/4.49  --inst_lit_activity_flag                true
% 31.51/4.49  --inst_restr_to_given                   false
% 31.51/4.49  --inst_activity_threshold               500
% 31.51/4.49  --inst_out_proof                        true
% 31.51/4.49  
% 31.51/4.49  ------ Resolution Options
% 31.51/4.49  
% 31.51/4.49  --resolution_flag                       true
% 31.51/4.49  --res_lit_sel                           adaptive
% 31.51/4.49  --res_lit_sel_side                      none
% 31.51/4.49  --res_ordering                          kbo
% 31.51/4.49  --res_to_prop_solver                    active
% 31.51/4.49  --res_prop_simpl_new                    false
% 31.51/4.49  --res_prop_simpl_given                  true
% 31.51/4.49  --res_passive_queue_type                priority_queues
% 31.51/4.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 31.51/4.49  --res_passive_queues_freq               [15;5]
% 31.51/4.49  --res_forward_subs                      full
% 31.51/4.49  --res_backward_subs                     full
% 31.51/4.49  --res_forward_subs_resolution           true
% 31.51/4.49  --res_backward_subs_resolution          true
% 31.51/4.49  --res_orphan_elimination                true
% 31.51/4.49  --res_time_limit                        2.
% 31.51/4.49  --res_out_proof                         true
% 31.51/4.49  
% 31.51/4.49  ------ Superposition Options
% 31.51/4.49  
% 31.51/4.49  --superposition_flag                    true
% 31.51/4.49  --sup_passive_queue_type                priority_queues
% 31.51/4.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 31.51/4.49  --sup_passive_queues_freq               [8;1;4]
% 31.51/4.49  --demod_completeness_check              fast
% 31.51/4.49  --demod_use_ground                      true
% 31.51/4.49  --sup_to_prop_solver                    passive
% 31.51/4.49  --sup_prop_simpl_new                    true
% 31.51/4.49  --sup_prop_simpl_given                  true
% 31.51/4.49  --sup_fun_splitting                     true
% 31.51/4.49  --sup_smt_interval                      50000
% 31.51/4.49  
% 31.51/4.49  ------ Superposition Simplification Setup
% 31.51/4.49  
% 31.51/4.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 31.51/4.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 31.51/4.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 31.51/4.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 31.51/4.49  --sup_full_triv                         [TrivRules;PropSubs]
% 31.51/4.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 31.51/4.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 31.51/4.49  --sup_immed_triv                        [TrivRules]
% 31.51/4.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 31.51/4.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.51/4.49  --sup_immed_bw_main                     []
% 31.51/4.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 31.51/4.49  --sup_input_triv                        [Unflattening;TrivRules]
% 31.51/4.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.51/4.49  --sup_input_bw                          []
% 31.51/4.49  
% 31.51/4.49  ------ Combination Options
% 31.51/4.49  
% 31.51/4.49  --comb_res_mult                         3
% 31.51/4.49  --comb_sup_mult                         2
% 31.51/4.49  --comb_inst_mult                        10
% 31.51/4.49  
% 31.51/4.49  ------ Debug Options
% 31.51/4.49  
% 31.51/4.49  --dbg_backtrace                         false
% 31.51/4.49  --dbg_dump_prop_clauses                 false
% 31.51/4.49  --dbg_dump_prop_clauses_file            -
% 31.51/4.49  --dbg_out_stat                          false
% 31.51/4.49  ------ Parsing...
% 31.51/4.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 31.51/4.49  
% 31.51/4.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 31.51/4.49  
% 31.51/4.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 31.51/4.49  
% 31.51/4.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.51/4.49  ------ Proving...
% 31.51/4.49  ------ Problem Properties 
% 31.51/4.49  
% 31.51/4.49  
% 31.51/4.49  clauses                                 41
% 31.51/4.49  conjectures                             11
% 31.51/4.49  EPR                                     7
% 31.51/4.49  Horn                                    37
% 31.51/4.49  unary                                   13
% 31.51/4.49  binary                                  2
% 31.51/4.49  lits                                    168
% 31.51/4.49  lits eq                                 34
% 31.51/4.49  fd_pure                                 0
% 31.51/4.49  fd_pseudo                               0
% 31.51/4.49  fd_cond                                 4
% 31.51/4.49  fd_pseudo_cond                          1
% 31.51/4.49  AC symbols                              0
% 31.51/4.49  
% 31.51/4.49  ------ Schedule dynamic 5 is on 
% 31.51/4.49  
% 31.51/4.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 31.51/4.49  
% 31.51/4.49  
% 31.51/4.49  ------ 
% 31.51/4.49  Current options:
% 31.51/4.49  ------ 
% 31.51/4.49  
% 31.51/4.49  ------ Input Options
% 31.51/4.49  
% 31.51/4.49  --out_options                           all
% 31.51/4.49  --tptp_safe_out                         true
% 31.51/4.49  --problem_path                          ""
% 31.51/4.49  --include_path                          ""
% 31.51/4.49  --clausifier                            res/vclausify_rel
% 31.51/4.49  --clausifier_options                    ""
% 31.51/4.49  --stdin                                 false
% 31.51/4.49  --stats_out                             all
% 31.51/4.49  
% 31.51/4.49  ------ General Options
% 31.51/4.49  
% 31.51/4.49  --fof                                   false
% 31.51/4.49  --time_out_real                         305.
% 31.51/4.49  --time_out_virtual                      -1.
% 31.51/4.49  --symbol_type_check                     false
% 31.51/4.49  --clausify_out                          false
% 31.51/4.49  --sig_cnt_out                           false
% 31.51/4.49  --trig_cnt_out                          false
% 31.51/4.49  --trig_cnt_out_tolerance                1.
% 31.51/4.49  --trig_cnt_out_sk_spl                   false
% 31.51/4.49  --abstr_cl_out                          false
% 31.51/4.49  
% 31.51/4.49  ------ Global Options
% 31.51/4.49  
% 31.51/4.49  --schedule                              default
% 31.51/4.49  --add_important_lit                     false
% 31.51/4.49  --prop_solver_per_cl                    1000
% 31.51/4.49  --min_unsat_core                        false
% 31.51/4.49  --soft_assumptions                      false
% 31.51/4.49  --soft_lemma_size                       3
% 31.51/4.49  --prop_impl_unit_size                   0
% 31.51/4.49  --prop_impl_unit                        []
% 31.51/4.49  --share_sel_clauses                     true
% 31.51/4.49  --reset_solvers                         false
% 31.51/4.49  --bc_imp_inh                            [conj_cone]
% 31.51/4.49  --conj_cone_tolerance                   3.
% 31.51/4.49  --extra_neg_conj                        none
% 31.51/4.49  --large_theory_mode                     true
% 31.51/4.49  --prolific_symb_bound                   200
% 31.51/4.49  --lt_threshold                          2000
% 31.51/4.49  --clause_weak_htbl                      true
% 31.51/4.49  --gc_record_bc_elim                     false
% 31.51/4.49  
% 31.51/4.49  ------ Preprocessing Options
% 31.51/4.49  
% 31.51/4.49  --preprocessing_flag                    true
% 31.51/4.49  --time_out_prep_mult                    0.1
% 31.51/4.49  --splitting_mode                        input
% 31.51/4.49  --splitting_grd                         true
% 31.51/4.49  --splitting_cvd                         false
% 31.51/4.49  --splitting_cvd_svl                     false
% 31.51/4.49  --splitting_nvd                         32
% 31.51/4.49  --sub_typing                            true
% 31.51/4.49  --prep_gs_sim                           true
% 31.51/4.49  --prep_unflatten                        true
% 31.51/4.49  --prep_res_sim                          true
% 31.51/4.49  --prep_upred                            true
% 31.51/4.49  --prep_sem_filter                       exhaustive
% 31.51/4.49  --prep_sem_filter_out                   false
% 31.51/4.49  --pred_elim                             true
% 31.51/4.49  --res_sim_input                         true
% 31.51/4.49  --eq_ax_congr_red                       true
% 31.51/4.49  --pure_diseq_elim                       true
% 31.51/4.49  --brand_transform                       false
% 31.51/4.49  --non_eq_to_eq                          false
% 31.51/4.49  --prep_def_merge                        true
% 31.51/4.49  --prep_def_merge_prop_impl              false
% 31.51/4.49  --prep_def_merge_mbd                    true
% 31.51/4.49  --prep_def_merge_tr_red                 false
% 31.51/4.49  --prep_def_merge_tr_cl                  false
% 31.51/4.49  --smt_preprocessing                     true
% 31.51/4.49  --smt_ac_axioms                         fast
% 31.51/4.49  --preprocessed_out                      false
% 31.51/4.49  --preprocessed_stats                    false
% 31.51/4.49  
% 31.51/4.49  ------ Abstraction refinement Options
% 31.51/4.49  
% 31.51/4.49  --abstr_ref                             []
% 31.51/4.49  --abstr_ref_prep                        false
% 31.51/4.49  --abstr_ref_until_sat                   false
% 31.51/4.49  --abstr_ref_sig_restrict                funpre
% 31.51/4.49  --abstr_ref_af_restrict_to_split_sk     false
% 31.51/4.49  --abstr_ref_under                       []
% 31.51/4.49  
% 31.51/4.49  ------ SAT Options
% 31.51/4.49  
% 31.51/4.49  --sat_mode                              false
% 31.51/4.49  --sat_fm_restart_options                ""
% 31.51/4.49  --sat_gr_def                            false
% 31.51/4.49  --sat_epr_types                         true
% 31.51/4.49  --sat_non_cyclic_types                  false
% 31.51/4.49  --sat_finite_models                     false
% 31.51/4.49  --sat_fm_lemmas                         false
% 31.51/4.49  --sat_fm_prep                           false
% 31.51/4.49  --sat_fm_uc_incr                        true
% 31.51/4.49  --sat_out_model                         small
% 31.51/4.49  --sat_out_clauses                       false
% 31.51/4.49  
% 31.51/4.49  ------ QBF Options
% 31.51/4.49  
% 31.51/4.49  --qbf_mode                              false
% 31.51/4.49  --qbf_elim_univ                         false
% 31.51/4.49  --qbf_dom_inst                          none
% 31.51/4.49  --qbf_dom_pre_inst                      false
% 31.51/4.49  --qbf_sk_in                             false
% 31.51/4.49  --qbf_pred_elim                         true
% 31.51/4.49  --qbf_split                             512
% 31.51/4.49  
% 31.51/4.49  ------ BMC1 Options
% 31.51/4.49  
% 31.51/4.49  --bmc1_incremental                      false
% 31.51/4.49  --bmc1_axioms                           reachable_all
% 31.51/4.49  --bmc1_min_bound                        0
% 31.51/4.49  --bmc1_max_bound                        -1
% 31.51/4.49  --bmc1_max_bound_default                -1
% 31.51/4.49  --bmc1_symbol_reachability              true
% 31.51/4.49  --bmc1_property_lemmas                  false
% 31.51/4.49  --bmc1_k_induction                      false
% 31.51/4.49  --bmc1_non_equiv_states                 false
% 31.51/4.49  --bmc1_deadlock                         false
% 31.51/4.49  --bmc1_ucm                              false
% 31.51/4.49  --bmc1_add_unsat_core                   none
% 31.51/4.49  --bmc1_unsat_core_children              false
% 31.51/4.49  --bmc1_unsat_core_extrapolate_axioms    false
% 31.51/4.49  --bmc1_out_stat                         full
% 31.51/4.49  --bmc1_ground_init                      false
% 31.51/4.49  --bmc1_pre_inst_next_state              false
% 31.51/4.49  --bmc1_pre_inst_state                   false
% 31.51/4.49  --bmc1_pre_inst_reach_state             false
% 31.51/4.49  --bmc1_out_unsat_core                   false
% 31.51/4.49  --bmc1_aig_witness_out                  false
% 31.51/4.49  --bmc1_verbose                          false
% 31.51/4.49  --bmc1_dump_clauses_tptp                false
% 31.51/4.49  --bmc1_dump_unsat_core_tptp             false
% 31.51/4.49  --bmc1_dump_file                        -
% 31.51/4.49  --bmc1_ucm_expand_uc_limit              128
% 31.51/4.49  --bmc1_ucm_n_expand_iterations          6
% 31.51/4.49  --bmc1_ucm_extend_mode                  1
% 31.51/4.49  --bmc1_ucm_init_mode                    2
% 31.51/4.49  --bmc1_ucm_cone_mode                    none
% 31.51/4.49  --bmc1_ucm_reduced_relation_type        0
% 31.51/4.49  --bmc1_ucm_relax_model                  4
% 31.51/4.49  --bmc1_ucm_full_tr_after_sat            true
% 31.51/4.49  --bmc1_ucm_expand_neg_assumptions       false
% 31.51/4.49  --bmc1_ucm_layered_model                none
% 31.51/4.49  --bmc1_ucm_max_lemma_size               10
% 31.51/4.49  
% 31.51/4.49  ------ AIG Options
% 31.51/4.49  
% 31.51/4.49  --aig_mode                              false
% 31.51/4.49  
% 31.51/4.49  ------ Instantiation Options
% 31.51/4.49  
% 31.51/4.49  --instantiation_flag                    true
% 31.51/4.49  --inst_sos_flag                         true
% 31.51/4.49  --inst_sos_phase                        true
% 31.51/4.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 31.51/4.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 31.51/4.49  --inst_lit_sel_side                     none
% 31.51/4.49  --inst_solver_per_active                1400
% 31.51/4.49  --inst_solver_calls_frac                1.
% 31.51/4.49  --inst_passive_queue_type               priority_queues
% 31.51/4.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 31.51/4.49  --inst_passive_queues_freq              [25;2]
% 31.51/4.49  --inst_dismatching                      true
% 31.51/4.49  --inst_eager_unprocessed_to_passive     true
% 31.51/4.49  --inst_prop_sim_given                   true
% 31.51/4.49  --inst_prop_sim_new                     false
% 31.51/4.49  --inst_subs_new                         false
% 31.51/4.49  --inst_eq_res_simp                      false
% 31.51/4.49  --inst_subs_given                       false
% 31.51/4.49  --inst_orphan_elimination               true
% 31.51/4.49  --inst_learning_loop_flag               true
% 31.51/4.49  --inst_learning_start                   3000
% 31.51/4.49  --inst_learning_factor                  2
% 31.51/4.49  --inst_start_prop_sim_after_learn       3
% 31.51/4.49  --inst_sel_renew                        solver
% 31.51/4.49  --inst_lit_activity_flag                true
% 31.51/4.49  --inst_restr_to_given                   false
% 31.51/4.49  --inst_activity_threshold               500
% 31.51/4.49  --inst_out_proof                        true
% 31.51/4.49  
% 31.51/4.49  ------ Resolution Options
% 31.51/4.49  
% 31.51/4.49  --resolution_flag                       false
% 31.51/4.49  --res_lit_sel                           adaptive
% 31.51/4.49  --res_lit_sel_side                      none
% 31.51/4.49  --res_ordering                          kbo
% 31.51/4.49  --res_to_prop_solver                    active
% 31.51/4.49  --res_prop_simpl_new                    false
% 31.51/4.49  --res_prop_simpl_given                  true
% 31.51/4.49  --res_passive_queue_type                priority_queues
% 31.51/4.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 31.51/4.49  --res_passive_queues_freq               [15;5]
% 31.51/4.49  --res_forward_subs                      full
% 31.51/4.49  --res_backward_subs                     full
% 31.51/4.49  --res_forward_subs_resolution           true
% 31.51/4.49  --res_backward_subs_resolution          true
% 31.51/4.49  --res_orphan_elimination                true
% 31.51/4.49  --res_time_limit                        2.
% 31.51/4.49  --res_out_proof                         true
% 31.51/4.49  
% 31.51/4.49  ------ Superposition Options
% 31.51/4.49  
% 31.51/4.49  --superposition_flag                    true
% 31.51/4.49  --sup_passive_queue_type                priority_queues
% 31.51/4.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 31.51/4.49  --sup_passive_queues_freq               [8;1;4]
% 31.51/4.49  --demod_completeness_check              fast
% 31.51/4.49  --demod_use_ground                      true
% 31.51/4.49  --sup_to_prop_solver                    passive
% 31.51/4.49  --sup_prop_simpl_new                    true
% 31.51/4.49  --sup_prop_simpl_given                  true
% 31.51/4.49  --sup_fun_splitting                     true
% 31.51/4.49  --sup_smt_interval                      50000
% 31.51/4.49  
% 31.51/4.49  ------ Superposition Simplification Setup
% 31.51/4.49  
% 31.51/4.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 31.51/4.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 31.51/4.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 31.51/4.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 31.51/4.49  --sup_full_triv                         [TrivRules;PropSubs]
% 31.51/4.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 31.51/4.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 31.51/4.49  --sup_immed_triv                        [TrivRules]
% 31.51/4.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 31.51/4.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.51/4.49  --sup_immed_bw_main                     []
% 31.51/4.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 31.51/4.49  --sup_input_triv                        [Unflattening;TrivRules]
% 31.51/4.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.51/4.49  --sup_input_bw                          []
% 31.51/4.49  
% 31.51/4.49  ------ Combination Options
% 31.51/4.49  
% 31.51/4.49  --comb_res_mult                         3
% 31.51/4.49  --comb_sup_mult                         2
% 31.51/4.49  --comb_inst_mult                        10
% 31.51/4.49  
% 31.51/4.49  ------ Debug Options
% 31.51/4.49  
% 31.51/4.49  --dbg_backtrace                         false
% 31.51/4.49  --dbg_dump_prop_clauses                 false
% 31.51/4.49  --dbg_dump_prop_clauses_file            -
% 31.51/4.49  --dbg_out_stat                          false
% 31.51/4.49  
% 31.51/4.49  
% 31.51/4.49  
% 31.51/4.49  
% 31.51/4.49  ------ Proving...
% 31.51/4.49  
% 31.51/4.49  
% 31.51/4.49  % SZS status Theorem for theBenchmark.p
% 31.51/4.49  
% 31.51/4.49  % SZS output start CNFRefutation for theBenchmark.p
% 31.51/4.49  
% 31.51/4.49  fof(f15,axiom,(
% 31.51/4.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 31.51/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.51/4.49  
% 31.51/4.49  fof(f44,plain,(
% 31.51/4.49    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 31.51/4.49    inference(ennf_transformation,[],[f15])).
% 31.51/4.49  
% 31.51/4.49  fof(f45,plain,(
% 31.51/4.49    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 31.51/4.49    inference(flattening,[],[f44])).
% 31.51/4.49  
% 31.51/4.49  fof(f83,plain,(
% 31.51/4.49    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 31.51/4.49    inference(cnf_transformation,[],[f45])).
% 31.51/4.49  
% 31.51/4.49  fof(f20,conjecture,(
% 31.51/4.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 31.51/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.51/4.49  
% 31.51/4.49  fof(f21,negated_conjecture,(
% 31.51/4.49    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 31.51/4.49    inference(negated_conjecture,[],[f20])).
% 31.51/4.49  
% 31.51/4.49  fof(f54,plain,(
% 31.51/4.49    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 31.51/4.49    inference(ennf_transformation,[],[f21])).
% 31.51/4.49  
% 31.51/4.49  fof(f55,plain,(
% 31.51/4.49    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 31.51/4.49    inference(flattening,[],[f54])).
% 31.51/4.49  
% 31.51/4.49  fof(f59,plain,(
% 31.51/4.49    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 31.51/4.49    introduced(choice_axiom,[])).
% 31.51/4.49  
% 31.51/4.49  fof(f58,plain,(
% 31.51/4.49    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 31.51/4.49    introduced(choice_axiom,[])).
% 31.51/4.49  
% 31.51/4.49  fof(f60,plain,(
% 31.51/4.49    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 31.51/4.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f55,f59,f58])).
% 31.51/4.49  
% 31.51/4.49  fof(f103,plain,(
% 31.51/4.49    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 31.51/4.49    inference(cnf_transformation,[],[f60])).
% 31.51/4.49  
% 31.51/4.49  fof(f96,plain,(
% 31.51/4.49    v1_funct_1(sK2)),
% 31.51/4.49    inference(cnf_transformation,[],[f60])).
% 31.51/4.49  
% 31.51/4.49  fof(f97,plain,(
% 31.51/4.49    v1_funct_2(sK2,sK0,sK1)),
% 31.51/4.49    inference(cnf_transformation,[],[f60])).
% 31.51/4.49  
% 31.51/4.49  fof(f98,plain,(
% 31.51/4.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 31.51/4.49    inference(cnf_transformation,[],[f60])).
% 31.51/4.49  
% 31.51/4.49  fof(f99,plain,(
% 31.51/4.49    v1_funct_1(sK3)),
% 31.51/4.49    inference(cnf_transformation,[],[f60])).
% 31.51/4.49  
% 31.51/4.49  fof(f100,plain,(
% 31.51/4.49    v1_funct_2(sK3,sK1,sK0)),
% 31.51/4.49    inference(cnf_transformation,[],[f60])).
% 31.51/4.49  
% 31.51/4.49  fof(f101,plain,(
% 31.51/4.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 31.51/4.49    inference(cnf_transformation,[],[f60])).
% 31.51/4.49  
% 31.51/4.49  fof(f18,axiom,(
% 31.51/4.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 31.51/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.51/4.49  
% 31.51/4.49  fof(f50,plain,(
% 31.51/4.49    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 31.51/4.49    inference(ennf_transformation,[],[f18])).
% 31.51/4.49  
% 31.51/4.49  fof(f51,plain,(
% 31.51/4.49    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 31.51/4.49    inference(flattening,[],[f50])).
% 31.51/4.49  
% 31.51/4.49  fof(f91,plain,(
% 31.51/4.49    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 31.51/4.49    inference(cnf_transformation,[],[f51])).
% 31.51/4.49  
% 31.51/4.49  fof(f105,plain,(
% 31.51/4.49    k1_xboole_0 != sK0),
% 31.51/4.49    inference(cnf_transformation,[],[f60])).
% 31.51/4.49  
% 31.51/4.49  fof(f2,axiom,(
% 31.51/4.49    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 31.51/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.51/4.49  
% 31.51/4.49  fof(f64,plain,(
% 31.51/4.49    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 31.51/4.49    inference(cnf_transformation,[],[f2])).
% 31.51/4.49  
% 31.51/4.49  fof(f14,axiom,(
% 31.51/4.49    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 31.51/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.51/4.49  
% 31.51/4.49  fof(f82,plain,(
% 31.51/4.49    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 31.51/4.49    inference(cnf_transformation,[],[f14])).
% 31.51/4.49  
% 31.51/4.49  fof(f108,plain,(
% 31.51/4.49    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 31.51/4.49    inference(definition_unfolding,[],[f64,f82])).
% 31.51/4.49  
% 31.51/4.49  fof(f13,axiom,(
% 31.51/4.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 31.51/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.51/4.49  
% 31.51/4.49  fof(f42,plain,(
% 31.51/4.49    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 31.51/4.49    inference(ennf_transformation,[],[f13])).
% 31.51/4.49  
% 31.51/4.49  fof(f43,plain,(
% 31.51/4.49    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 31.51/4.49    inference(flattening,[],[f42])).
% 31.51/4.49  
% 31.51/4.49  fof(f81,plain,(
% 31.51/4.49    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 31.51/4.49    inference(cnf_transformation,[],[f43])).
% 31.51/4.49  
% 31.51/4.49  fof(f10,axiom,(
% 31.51/4.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 31.51/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.51/4.49  
% 31.51/4.49  fof(f36,plain,(
% 31.51/4.49    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 31.51/4.49    inference(ennf_transformation,[],[f10])).
% 31.51/4.49  
% 31.51/4.49  fof(f37,plain,(
% 31.51/4.49    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.51/4.49    inference(flattening,[],[f36])).
% 31.51/4.49  
% 31.51/4.49  fof(f56,plain,(
% 31.51/4.49    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.51/4.49    inference(nnf_transformation,[],[f37])).
% 31.51/4.49  
% 31.51/4.49  fof(f75,plain,(
% 31.51/4.49    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 31.51/4.49    inference(cnf_transformation,[],[f56])).
% 31.51/4.49  
% 31.51/4.49  fof(f104,plain,(
% 31.51/4.49    v2_funct_1(sK2)),
% 31.51/4.49    inference(cnf_transformation,[],[f60])).
% 31.51/4.49  
% 31.51/4.49  fof(f1,axiom,(
% 31.51/4.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 31.51/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.51/4.49  
% 31.51/4.49  fof(f23,plain,(
% 31.51/4.49    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 31.51/4.49    inference(ennf_transformation,[],[f1])).
% 31.51/4.49  
% 31.51/4.49  fof(f24,plain,(
% 31.51/4.49    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 31.51/4.49    inference(flattening,[],[f23])).
% 31.51/4.49  
% 31.51/4.49  fof(f62,plain,(
% 31.51/4.49    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 31.51/4.49    inference(cnf_transformation,[],[f24])).
% 31.51/4.49  
% 31.51/4.49  fof(f102,plain,(
% 31.51/4.49    k2_relset_1(sK0,sK1,sK2) = sK1),
% 31.51/4.49    inference(cnf_transformation,[],[f60])).
% 31.51/4.49  
% 31.51/4.49  fof(f7,axiom,(
% 31.51/4.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 31.51/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.51/4.49  
% 31.51/4.49  fof(f33,plain,(
% 31.51/4.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.51/4.49    inference(ennf_transformation,[],[f7])).
% 31.51/4.49  
% 31.51/4.49  fof(f72,plain,(
% 31.51/4.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 31.51/4.49    inference(cnf_transformation,[],[f33])).
% 31.51/4.49  
% 31.51/4.49  fof(f17,axiom,(
% 31.51/4.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 31.51/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.51/4.49  
% 31.51/4.49  fof(f48,plain,(
% 31.51/4.49    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 31.51/4.49    inference(ennf_transformation,[],[f17])).
% 31.51/4.49  
% 31.51/4.49  fof(f49,plain,(
% 31.51/4.49    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 31.51/4.49    inference(flattening,[],[f48])).
% 31.51/4.49  
% 31.51/4.49  fof(f90,plain,(
% 31.51/4.49    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 31.51/4.49    inference(cnf_transformation,[],[f49])).
% 31.51/4.49  
% 31.51/4.49  fof(f12,axiom,(
% 31.51/4.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 31.51/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.51/4.49  
% 31.51/4.49  fof(f40,plain,(
% 31.51/4.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 31.51/4.49    inference(ennf_transformation,[],[f12])).
% 31.51/4.49  
% 31.51/4.49  fof(f41,plain,(
% 31.51/4.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 31.51/4.49    inference(flattening,[],[f40])).
% 31.51/4.49  
% 31.51/4.49  fof(f80,plain,(
% 31.51/4.49    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 31.51/4.49    inference(cnf_transformation,[],[f41])).
% 31.51/4.49  
% 31.51/4.49  fof(f5,axiom,(
% 31.51/4.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))))),
% 31.51/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.51/4.49  
% 31.51/4.49  fof(f29,plain,(
% 31.51/4.49    ! [X0] : (((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 31.51/4.49    inference(ennf_transformation,[],[f5])).
% 31.51/4.49  
% 31.51/4.49  fof(f30,plain,(
% 31.51/4.49    ! [X0] : ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 31.51/4.49    inference(flattening,[],[f29])).
% 31.51/4.49  
% 31.51/4.49  fof(f69,plain,(
% 31.51/4.49    ( ! [X0] : (k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 31.51/4.49    inference(cnf_transformation,[],[f30])).
% 31.51/4.49  
% 31.51/4.49  fof(f111,plain,(
% 31.51/4.49    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 31.51/4.49    inference(definition_unfolding,[],[f69,f82])).
% 31.51/4.49  
% 31.51/4.49  fof(f106,plain,(
% 31.51/4.49    k1_xboole_0 != sK1),
% 31.51/4.49    inference(cnf_transformation,[],[f60])).
% 31.51/4.49  
% 31.51/4.49  fof(f16,axiom,(
% 31.51/4.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 31.51/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.51/4.49  
% 31.51/4.49  fof(f46,plain,(
% 31.51/4.49    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 31.51/4.49    inference(ennf_transformation,[],[f16])).
% 31.51/4.49  
% 31.51/4.49  fof(f47,plain,(
% 31.51/4.49    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 31.51/4.49    inference(flattening,[],[f46])).
% 31.51/4.49  
% 31.51/4.49  fof(f86,plain,(
% 31.51/4.49    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X4) | k1_xboole_0 = X2 | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 31.51/4.49    inference(cnf_transformation,[],[f47])).
% 31.51/4.49  
% 31.51/4.49  fof(f9,axiom,(
% 31.51/4.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 31.51/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.51/4.49  
% 31.51/4.49  fof(f35,plain,(
% 31.51/4.49    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.51/4.49    inference(ennf_transformation,[],[f9])).
% 31.51/4.49  
% 31.51/4.49  fof(f74,plain,(
% 31.51/4.49    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 31.51/4.49    inference(cnf_transformation,[],[f35])).
% 31.51/4.49  
% 31.51/4.49  fof(f19,axiom,(
% 31.51/4.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 31.51/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.51/4.49  
% 31.51/4.49  fof(f52,plain,(
% 31.51/4.49    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 31.51/4.49    inference(ennf_transformation,[],[f19])).
% 31.51/4.49  
% 31.51/4.49  fof(f53,plain,(
% 31.51/4.49    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 31.51/4.49    inference(flattening,[],[f52])).
% 31.51/4.49  
% 31.51/4.49  fof(f95,plain,(
% 31.51/4.49    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 31.51/4.49    inference(cnf_transformation,[],[f53])).
% 31.51/4.49  
% 31.51/4.49  fof(f94,plain,(
% 31.51/4.49    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 31.51/4.49    inference(cnf_transformation,[],[f53])).
% 31.51/4.49  
% 31.51/4.49  fof(f88,plain,(
% 31.51/4.49    ( ! [X2,X0,X1] : (v1_funct_1(k2_funct_1(X2)) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 31.51/4.49    inference(cnf_transformation,[],[f49])).
% 31.51/4.49  
% 31.51/4.49  fof(f76,plain,(
% 31.51/4.49    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 31.51/4.49    inference(cnf_transformation,[],[f56])).
% 31.51/4.49  
% 31.51/4.49  fof(f113,plain,(
% 31.51/4.49    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 31.51/4.49    inference(equality_resolution,[],[f76])).
% 31.51/4.49  
% 31.51/4.49  fof(f4,axiom,(
% 31.51/4.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 31.51/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.51/4.49  
% 31.51/4.49  fof(f27,plain,(
% 31.51/4.49    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 31.51/4.49    inference(ennf_transformation,[],[f4])).
% 31.51/4.49  
% 31.51/4.49  fof(f28,plain,(
% 31.51/4.49    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 31.51/4.49    inference(flattening,[],[f27])).
% 31.51/4.49  
% 31.51/4.49  fof(f68,plain,(
% 31.51/4.49    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 31.51/4.49    inference(cnf_transformation,[],[f28])).
% 31.51/4.49  
% 31.51/4.49  fof(f61,plain,(
% 31.51/4.49    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 31.51/4.49    inference(cnf_transformation,[],[f24])).
% 31.51/4.49  
% 31.51/4.49  fof(f6,axiom,(
% 31.51/4.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 31.51/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.51/4.49  
% 31.51/4.49  fof(f31,plain,(
% 31.51/4.49    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 31.51/4.49    inference(ennf_transformation,[],[f6])).
% 31.51/4.49  
% 31.51/4.49  fof(f32,plain,(
% 31.51/4.49    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 31.51/4.49    inference(flattening,[],[f31])).
% 31.51/4.49  
% 31.51/4.49  fof(f71,plain,(
% 31.51/4.49    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 31.51/4.49    inference(cnf_transformation,[],[f32])).
% 31.51/4.49  
% 31.51/4.49  fof(f112,plain,(
% 31.51/4.49    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 31.51/4.49    inference(definition_unfolding,[],[f71,f82])).
% 31.51/4.49  
% 31.51/4.49  fof(f67,plain,(
% 31.51/4.49    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 31.51/4.49    inference(cnf_transformation,[],[f28])).
% 31.51/4.49  
% 31.51/4.49  fof(f89,plain,(
% 31.51/4.49    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 31.51/4.49    inference(cnf_transformation,[],[f49])).
% 31.51/4.49  
% 31.51/4.49  fof(f3,axiom,(
% 31.51/4.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 31.51/4.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.51/4.49  
% 31.51/4.49  fof(f25,plain,(
% 31.51/4.49    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 31.51/4.49    inference(ennf_transformation,[],[f3])).
% 31.51/4.49  
% 31.51/4.49  fof(f26,plain,(
% 31.51/4.49    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 31.51/4.49    inference(flattening,[],[f25])).
% 31.51/4.49  
% 31.51/4.49  fof(f65,plain,(
% 31.51/4.49    ( ! [X0,X1] : (v2_funct_1(X1) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 31.51/4.49    inference(cnf_transformation,[],[f26])).
% 31.51/4.49  
% 31.51/4.49  fof(f92,plain,(
% 31.51/4.49    ( ! [X2,X0,X1] : (k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 31.51/4.49    inference(cnf_transformation,[],[f51])).
% 31.51/4.49  
% 31.51/4.49  fof(f107,plain,(
% 31.51/4.49    k2_funct_1(sK2) != sK3),
% 31.51/4.49    inference(cnf_transformation,[],[f60])).
% 31.51/4.49  
% 31.51/4.49  cnf(c_867,plain,
% 31.51/4.49      ( X0_50 != X1_50 | k2_funct_1(X0_50) = k2_funct_1(X1_50) ),
% 31.51/4.49      theory(equality) ).
% 31.51/4.49  
% 31.51/4.49  cnf(c_82192,plain,
% 31.51/4.49      ( k2_funct_1(k2_funct_1(sK3)) = k2_funct_1(sK2)
% 31.51/4.49      | k2_funct_1(sK3) != sK2 ),
% 31.51/4.49      inference(instantiation,[status(thm)],[c_867]) ).
% 31.51/4.49  
% 31.51/4.49  cnf(c_865,plain,
% 31.51/4.49      ( X0_50 != X1_50 | X2_50 != X1_50 | X2_50 = X0_50 ),
% 31.51/4.49      theory(equality) ).
% 31.51/4.49  
% 31.51/4.49  cnf(c_64456,plain,
% 31.51/4.49      ( X0_50 != X1_50
% 31.51/4.49      | X0_50 = k2_funct_1(X2_50)
% 31.51/4.49      | k2_funct_1(X2_50) != X1_50 ),
% 31.51/4.49      inference(instantiation,[status(thm)],[c_865]) ).
% 31.51/4.49  
% 31.51/4.49  cnf(c_66274,plain,
% 31.51/4.49      ( X0_50 != k2_funct_1(X1_50)
% 31.51/4.49      | X0_50 = k2_funct_1(X2_50)
% 31.51/4.49      | k2_funct_1(X2_50) != k2_funct_1(X1_50) ),
% 31.51/4.49      inference(instantiation,[status(thm)],[c_64456]) ).
% 31.51/4.49  
% 31.51/4.49  cnf(c_67000,plain,
% 31.51/4.49      ( k2_funct_1(X0_50) != k2_funct_1(X0_50)
% 31.51/4.49      | k2_funct_1(X1_50) != k2_funct_1(X0_50)
% 31.51/4.49      | k2_funct_1(X0_50) = k2_funct_1(X1_50) ),
% 31.51/4.49      inference(instantiation,[status(thm)],[c_66274]) ).
% 31.51/4.49  
% 31.51/4.49  cnf(c_72469,plain,
% 31.51/4.49      ( k2_funct_1(k2_funct_1(sK3)) != k2_funct_1(sK2)
% 31.51/4.49      | k2_funct_1(sK2) = k2_funct_1(k2_funct_1(sK3))
% 31.51/4.49      | k2_funct_1(sK2) != k2_funct_1(sK2) ),
% 31.51/4.49      inference(instantiation,[status(thm)],[c_67000]) ).
% 31.51/4.49  
% 31.51/4.49  cnf(c_63481,plain,
% 31.51/4.49      ( k2_funct_1(sK2) != X0_50 | k2_funct_1(sK2) = sK3 | sK3 != X0_50 ),
% 31.51/4.49      inference(instantiation,[status(thm)],[c_865]) ).
% 31.51/4.49  
% 31.51/4.49  cnf(c_69903,plain,
% 31.51/4.49      ( k2_funct_1(sK2) != k2_funct_1(k2_funct_1(sK3))
% 31.51/4.49      | k2_funct_1(sK2) = sK3
% 31.51/4.49      | sK3 != k2_funct_1(k2_funct_1(sK3)) ),
% 31.51/4.49      inference(instantiation,[status(thm)],[c_63481]) ).
% 31.51/4.49  
% 31.51/4.49  cnf(c_21,plain,
% 31.51/4.49      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 31.51/4.49      | ~ v1_funct_2(X2,X0,X1)
% 31.51/4.49      | ~ v1_funct_2(X3,X1,X0)
% 31.51/4.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 31.51/4.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 31.51/4.49      | ~ v1_funct_1(X2)
% 31.51/4.49      | ~ v1_funct_1(X3)
% 31.51/4.49      | k2_relset_1(X1,X0,X3) = X0 ),
% 31.51/4.49      inference(cnf_transformation,[],[f83]) ).
% 31.51/4.49  
% 31.51/4.49  cnf(c_38,negated_conjecture,
% 31.51/4.49      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 31.51/4.49      inference(cnf_transformation,[],[f103]) ).
% 31.51/4.49  
% 31.51/4.49  cnf(c_519,plain,
% 31.51/4.49      ( ~ v1_funct_2(X0,X1,X2)
% 31.51/4.49      | ~ v1_funct_2(X3,X2,X1)
% 31.51/4.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 31.51/4.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.51/4.49      | ~ v1_funct_1(X0)
% 31.51/4.49      | ~ v1_funct_1(X3)
% 31.51/4.49      | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 31.51/4.49      | k2_relset_1(X1,X2,X0) = X2
% 31.51/4.49      | k6_partfun1(X2) != k6_partfun1(sK0)
% 31.51/4.49      | sK0 != X2 ),
% 31.51/4.49      inference(resolution_lifted,[status(thm)],[c_21,c_38]) ).
% 31.51/4.49  
% 31.51/4.49  cnf(c_520,plain,
% 31.51/4.49      ( ~ v1_funct_2(X0,X1,sK0)
% 31.51/4.49      | ~ v1_funct_2(X2,sK0,X1)
% 31.51/4.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 31.51/4.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 31.51/4.49      | ~ v1_funct_1(X0)
% 31.51/4.49      | ~ v1_funct_1(X2)
% 31.51/4.49      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 31.51/4.49      | k2_relset_1(X1,sK0,X0) = sK0
% 31.51/4.49      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 31.51/4.49      inference(unflattening,[status(thm)],[c_519]) ).
% 31.51/4.49  
% 31.51/4.49  cnf(c_612,plain,
% 31.51/4.49      ( ~ v1_funct_2(X0,X1,sK0)
% 31.51/4.49      | ~ v1_funct_2(X2,sK0,X1)
% 31.51/4.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 31.51/4.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 31.51/4.49      | ~ v1_funct_1(X0)
% 31.51/4.49      | ~ v1_funct_1(X2)
% 31.51/4.49      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 31.51/4.49      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 31.51/4.49      inference(equality_resolution_simp,[status(thm)],[c_520]) ).
% 31.51/4.49  
% 31.51/4.49  cnf(c_819,plain,
% 31.51/4.49      ( ~ v1_funct_2(X0_50,X0_51,sK0)
% 31.51/4.49      | ~ v1_funct_2(X1_50,sK0,X0_51)
% 31.51/4.49      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK0)))
% 31.51/4.49      | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_51)))
% 31.51/4.49      | ~ v1_funct_1(X0_50)
% 31.51/4.49      | ~ v1_funct_1(X1_50)
% 31.51/4.49      | k2_relset_1(X0_51,sK0,X0_50) = sK0
% 31.51/4.49      | k1_partfun1(sK0,X0_51,X0_51,sK0,X1_50,X0_50) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 31.51/4.49      inference(subtyping,[status(esa)],[c_612]) ).
% 31.51/4.49  
% 31.51/4.49  cnf(c_1528,plain,
% 31.51/4.49      ( k2_relset_1(X0_51,sK0,X0_50) = sK0
% 31.51/4.49      | k1_partfun1(sK0,X0_51,X0_51,sK0,X1_50,X0_50) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 31.51/4.49      | v1_funct_2(X0_50,X0_51,sK0) != iProver_top
% 31.51/4.49      | v1_funct_2(X1_50,sK0,X0_51) != iProver_top
% 31.51/4.49      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK0))) != iProver_top
% 31.51/4.49      | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_51))) != iProver_top
% 31.51/4.49      | v1_funct_1(X0_50) != iProver_top
% 31.51/4.49      | v1_funct_1(X1_50) != iProver_top ),
% 31.51/4.49      inference(predicate_to_equality,[status(thm)],[c_819]) ).
% 31.51/4.49  
% 31.51/4.49  cnf(c_2003,plain,
% 31.51/4.49      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 31.51/4.49      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 31.51/4.49      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 31.51/4.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 31.51/4.49      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 31.51/4.49      | v1_funct_1(sK3) != iProver_top
% 31.51/4.49      | v1_funct_1(sK2) != iProver_top ),
% 31.51/4.49      inference(equality_resolution,[status(thm)],[c_1528]) ).
% 31.51/4.49  
% 31.51/4.49  cnf(c_45,negated_conjecture,
% 31.51/4.49      ( v1_funct_1(sK2) ),
% 31.51/4.49      inference(cnf_transformation,[],[f96]) ).
% 31.51/4.49  
% 31.51/4.49  cnf(c_44,negated_conjecture,
% 31.51/4.49      ( v1_funct_2(sK2,sK0,sK1) ),
% 31.51/4.49      inference(cnf_transformation,[],[f97]) ).
% 31.51/4.49  
% 31.51/4.49  cnf(c_43,negated_conjecture,
% 31.51/4.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 31.51/4.49      inference(cnf_transformation,[],[f98]) ).
% 31.51/4.49  
% 31.51/4.49  cnf(c_42,negated_conjecture,
% 31.51/4.49      ( v1_funct_1(sK3) ),
% 31.51/4.49      inference(cnf_transformation,[],[f99]) ).
% 31.51/4.49  
% 31.51/4.49  cnf(c_41,negated_conjecture,
% 31.51/4.49      ( v1_funct_2(sK3,sK1,sK0) ),
% 31.51/4.49      inference(cnf_transformation,[],[f100]) ).
% 31.51/4.49  
% 31.51/4.49  cnf(c_40,negated_conjecture,
% 31.51/4.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 31.51/4.49      inference(cnf_transformation,[],[f101]) ).
% 31.51/4.49  
% 31.51/4.49  cnf(c_1609,plain,
% 31.51/4.49      ( ~ v1_funct_2(X0_50,sK0,sK1)
% 31.51/4.49      | ~ v1_funct_2(sK3,sK1,sK0)
% 31.51/4.49      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 31.51/4.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 31.51/4.49      | ~ v1_funct_1(X0_50)
% 31.51/4.49      | ~ v1_funct_1(sK3)
% 31.51/4.49      | k2_relset_1(sK1,sK0,sK3) = sK0
% 31.51/4.49      | k1_partfun1(sK0,sK1,sK1,sK0,X0_50,sK3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 31.51/4.49      inference(instantiation,[status(thm)],[c_819]) ).
% 31.51/4.49  
% 31.51/4.49  cnf(c_1611,plain,
% 31.51/4.49      ( ~ v1_funct_2(sK3,sK1,sK0)
% 31.51/4.49      | ~ v1_funct_2(sK2,sK0,sK1)
% 31.51/4.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 31.51/4.49      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 31.51/4.49      | ~ v1_funct_1(sK3)
% 31.51/4.49      | ~ v1_funct_1(sK2)
% 31.51/4.49      | k2_relset_1(sK1,sK0,sK3) = sK0
% 31.51/4.49      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 31.51/4.49      inference(instantiation,[status(thm)],[c_1609]) ).
% 31.51/4.49  
% 31.51/4.49  cnf(c_861,plain,( X0_50 = X0_50 ),theory(equality) ).
% 31.51/4.49  
% 31.51/4.49  cnf(c_1776,plain,
% 31.51/4.49      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 31.51/4.49      inference(instantiation,[status(thm)],[c_861]) ).
% 31.51/4.49  
% 31.51/4.49  cnf(c_2060,plain,
% 31.51/4.49      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 31.51/4.49      inference(global_propositional_subsumption,
% 31.51/4.49                [status(thm)],
% 31.51/4.49                [c_2003,c_45,c_44,c_43,c_42,c_41,c_40,c_1611,c_1776]) ).
% 31.51/4.49  
% 31.51/4.49  cnf(c_30,plain,
% 31.51/4.49      ( ~ v1_funct_2(X0,X1,X2)
% 31.51/4.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.51/4.49      | ~ v2_funct_1(X0)
% 31.51/4.50      | ~ v1_funct_1(X0)
% 31.51/4.50      | k2_relset_1(X1,X2,X0) != X2
% 31.51/4.50      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 31.51/4.50      | k1_xboole_0 = X2 ),
% 31.51/4.50      inference(cnf_transformation,[],[f91]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_836,plain,
% 31.51/4.50      ( ~ v1_funct_2(X0_50,X0_51,X1_51)
% 31.51/4.50      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 31.51/4.50      | ~ v2_funct_1(X0_50)
% 31.51/4.50      | ~ v1_funct_1(X0_50)
% 31.51/4.50      | k2_relset_1(X0_51,X1_51,X0_50) != X1_51
% 31.51/4.50      | k1_xboole_0 = X1_51
% 31.51/4.50      | k5_relat_1(X0_50,k2_funct_1(X0_50)) = k6_partfun1(X0_51) ),
% 31.51/4.50      inference(subtyping,[status(esa)],[c_30]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_1515,plain,
% 31.51/4.50      ( k2_relset_1(X0_51,X1_51,X0_50) != X1_51
% 31.51/4.50      | k1_xboole_0 = X1_51
% 31.51/4.50      | k5_relat_1(X0_50,k2_funct_1(X0_50)) = k6_partfun1(X0_51)
% 31.51/4.50      | v1_funct_2(X0_50,X0_51,X1_51) != iProver_top
% 31.51/4.50      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 31.51/4.50      | v2_funct_1(X0_50) != iProver_top
% 31.51/4.50      | v1_funct_1(X0_50) != iProver_top ),
% 31.51/4.50      inference(predicate_to_equality,[status(thm)],[c_836]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_5224,plain,
% 31.51/4.50      ( sK0 = k1_xboole_0
% 31.51/4.50      | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 31.51/4.50      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 31.51/4.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 31.51/4.50      | v2_funct_1(sK3) != iProver_top
% 31.51/4.50      | v1_funct_1(sK3) != iProver_top ),
% 31.51/4.50      inference(superposition,[status(thm)],[c_2060,c_1515]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_49,plain,
% 31.51/4.50      ( v1_funct_1(sK3) = iProver_top ),
% 31.51/4.50      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_50,plain,
% 31.51/4.50      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 31.51/4.50      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_51,plain,
% 31.51/4.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 31.51/4.50      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_862,plain,( X0_51 = X0_51 ),theory(equality) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_897,plain,
% 31.51/4.50      ( k1_xboole_0 = k1_xboole_0 ),
% 31.51/4.50      inference(instantiation,[status(thm)],[c_862]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_36,negated_conjecture,
% 31.51/4.50      ( k1_xboole_0 != sK0 ),
% 31.51/4.50      inference(cnf_transformation,[],[f105]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_831,negated_conjecture,
% 31.51/4.50      ( k1_xboole_0 != sK0 ),
% 31.51/4.50      inference(subtyping,[status(esa)],[c_36]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_866,plain,
% 31.51/4.50      ( X0_51 != X1_51 | X2_51 != X1_51 | X2_51 = X0_51 ),
% 31.51/4.50      theory(equality) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_1585,plain,
% 31.51/4.50      ( sK0 != X0_51 | k1_xboole_0 != X0_51 | k1_xboole_0 = sK0 ),
% 31.51/4.50      inference(instantiation,[status(thm)],[c_866]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_1586,plain,
% 31.51/4.50      ( sK0 != k1_xboole_0
% 31.51/4.50      | k1_xboole_0 = sK0
% 31.51/4.50      | k1_xboole_0 != k1_xboole_0 ),
% 31.51/4.50      inference(instantiation,[status(thm)],[c_1585]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_2,plain,
% 31.51/4.50      ( v2_funct_1(k6_partfun1(X0)) ),
% 31.51/4.50      inference(cnf_transformation,[],[f108]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_857,plain,
% 31.51/4.50      ( v2_funct_1(k6_partfun1(X0_51)) ),
% 31.51/4.50      inference(subtyping,[status(esa)],[c_2]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_5082,plain,
% 31.51/4.50      ( v2_funct_1(k6_partfun1(sK0)) ),
% 31.51/4.50      inference(instantiation,[status(thm)],[c_857]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_5083,plain,
% 31.51/4.50      ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
% 31.51/4.50      inference(predicate_to_equality,[status(thm)],[c_5082]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_825,negated_conjecture,
% 31.51/4.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 31.51/4.50      inference(subtyping,[status(esa)],[c_43]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_1522,plain,
% 31.51/4.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 31.51/4.50      inference(predicate_to_equality,[status(thm)],[c_825]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_828,negated_conjecture,
% 31.51/4.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 31.51/4.50      inference(subtyping,[status(esa)],[c_40]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_1519,plain,
% 31.51/4.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 31.51/4.50      inference(predicate_to_equality,[status(thm)],[c_828]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_20,plain,
% 31.51/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.51/4.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 31.51/4.50      | ~ v1_funct_1(X0)
% 31.51/4.50      | ~ v1_funct_1(X3)
% 31.51/4.50      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 31.51/4.50      inference(cnf_transformation,[],[f81]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_844,plain,
% 31.51/4.50      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 31.51/4.50      | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51)))
% 31.51/4.50      | ~ v1_funct_1(X0_50)
% 31.51/4.50      | ~ v1_funct_1(X1_50)
% 31.51/4.50      | k1_partfun1(X2_51,X3_51,X0_51,X1_51,X1_50,X0_50) = k5_relat_1(X1_50,X0_50) ),
% 31.51/4.50      inference(subtyping,[status(esa)],[c_20]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_1507,plain,
% 31.51/4.50      ( k1_partfun1(X0_51,X1_51,X2_51,X3_51,X0_50,X1_50) = k5_relat_1(X0_50,X1_50)
% 31.51/4.50      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 31.51/4.50      | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51))) != iProver_top
% 31.51/4.50      | v1_funct_1(X1_50) != iProver_top
% 31.51/4.50      | v1_funct_1(X0_50) != iProver_top ),
% 31.51/4.50      inference(predicate_to_equality,[status(thm)],[c_844]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_3887,plain,
% 31.51/4.50      ( k1_partfun1(X0_51,X1_51,sK1,sK0,X0_50,sK3) = k5_relat_1(X0_50,sK3)
% 31.51/4.50      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 31.51/4.50      | v1_funct_1(X0_50) != iProver_top
% 31.51/4.50      | v1_funct_1(sK3) != iProver_top ),
% 31.51/4.50      inference(superposition,[status(thm)],[c_1519,c_1507]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_4013,plain,
% 31.51/4.50      ( v1_funct_1(X0_50) != iProver_top
% 31.51/4.50      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 31.51/4.50      | k1_partfun1(X0_51,X1_51,sK1,sK0,X0_50,sK3) = k5_relat_1(X0_50,sK3) ),
% 31.51/4.50      inference(global_propositional_subsumption,
% 31.51/4.50                [status(thm)],
% 31.51/4.50                [c_3887,c_49]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_4014,plain,
% 31.51/4.50      ( k1_partfun1(X0_51,X1_51,sK1,sK0,X0_50,sK3) = k5_relat_1(X0_50,sK3)
% 31.51/4.50      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 31.51/4.50      | v1_funct_1(X0_50) != iProver_top ),
% 31.51/4.50      inference(renaming,[status(thm)],[c_4013]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_4020,plain,
% 31.51/4.50      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 31.51/4.50      | v1_funct_1(sK2) != iProver_top ),
% 31.51/4.50      inference(superposition,[status(thm)],[c_1522,c_4014]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_2434,plain,
% 31.51/4.50      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 31.51/4.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 31.51/4.50      | ~ v1_funct_1(sK3)
% 31.51/4.50      | ~ v1_funct_1(sK2)
% 31.51/4.50      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 31.51/4.50      inference(instantiation,[status(thm)],[c_844]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_4311,plain,
% 31.51/4.50      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 31.51/4.50      inference(global_propositional_subsumption,
% 31.51/4.50                [status(thm)],
% 31.51/4.50                [c_4020,c_45,c_43,c_42,c_40,c_2434]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_15,plain,
% 31.51/4.50      ( ~ r2_relset_1(X0,X1,X2,X3)
% 31.51/4.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 31.51/4.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 31.51/4.50      | X3 = X2 ),
% 31.51/4.50      inference(cnf_transformation,[],[f75]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_506,plain,
% 31.51/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.51/4.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.51/4.50      | X3 = X0
% 31.51/4.50      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 31.51/4.50      | k6_partfun1(sK0) != X3
% 31.51/4.50      | sK0 != X2
% 31.51/4.50      | sK0 != X1 ),
% 31.51/4.50      inference(resolution_lifted,[status(thm)],[c_15,c_38]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_507,plain,
% 31.51/4.50      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 31.51/4.50      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 31.51/4.50      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 31.51/4.50      inference(unflattening,[status(thm)],[c_506]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_820,plain,
% 31.51/4.50      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 31.51/4.50      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 31.51/4.50      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 31.51/4.50      inference(subtyping,[status(esa)],[c_507]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_1527,plain,
% 31.51/4.50      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 31.51/4.50      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 31.51/4.50      | m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 31.51/4.50      inference(predicate_to_equality,[status(thm)],[c_820]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_4314,plain,
% 31.51/4.50      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 31.51/4.50      | m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 31.51/4.50      | m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 31.51/4.50      inference(demodulation,[status(thm)],[c_4311,c_1527]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_46,plain,
% 31.51/4.50      ( v1_funct_1(sK2) = iProver_top ),
% 31.51/4.50      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_47,plain,
% 31.51/4.50      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 31.51/4.50      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_48,plain,
% 31.51/4.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 31.51/4.50      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_37,negated_conjecture,
% 31.51/4.50      ( v2_funct_1(sK2) ),
% 31.51/4.50      inference(cnf_transformation,[],[f104]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_53,plain,
% 31.51/4.50      ( v2_funct_1(sK2) = iProver_top ),
% 31.51/4.50      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_0,plain,
% 31.51/4.50      ( ~ v1_relat_1(X0)
% 31.51/4.50      | ~ v1_funct_1(X0)
% 31.51/4.50      | v1_funct_1(k2_funct_1(X0)) ),
% 31.51/4.50      inference(cnf_transformation,[],[f62]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_859,plain,
% 31.51/4.50      ( ~ v1_relat_1(X0_50)
% 31.51/4.50      | ~ v1_funct_1(X0_50)
% 31.51/4.50      | v1_funct_1(k2_funct_1(X0_50)) ),
% 31.51/4.50      inference(subtyping,[status(esa)],[c_0]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_900,plain,
% 31.51/4.50      ( v1_relat_1(X0_50) != iProver_top
% 31.51/4.50      | v1_funct_1(X0_50) != iProver_top
% 31.51/4.50      | v1_funct_1(k2_funct_1(X0_50)) = iProver_top ),
% 31.51/4.50      inference(predicate_to_equality,[status(thm)],[c_859]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_902,plain,
% 31.51/4.50      ( v1_relat_1(sK2) != iProver_top
% 31.51/4.50      | v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 31.51/4.50      | v1_funct_1(sK2) != iProver_top ),
% 31.51/4.50      inference(instantiation,[status(thm)],[c_900]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_39,negated_conjecture,
% 31.51/4.50      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 31.51/4.50      inference(cnf_transformation,[],[f102]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_829,negated_conjecture,
% 31.51/4.50      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 31.51/4.50      inference(subtyping,[status(esa)],[c_39]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_11,plain,
% 31.51/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.51/4.50      | v1_relat_1(X0) ),
% 31.51/4.50      inference(cnf_transformation,[],[f72]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_848,plain,
% 31.51/4.50      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 31.51/4.50      | v1_relat_1(X0_50) ),
% 31.51/4.50      inference(subtyping,[status(esa)],[c_11]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_1624,plain,
% 31.51/4.50      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 31.51/4.50      | v1_relat_1(sK2) ),
% 31.51/4.50      inference(instantiation,[status(thm)],[c_848]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_1685,plain,
% 31.51/4.50      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 31.51/4.50      | v1_relat_1(sK2) ),
% 31.51/4.50      inference(instantiation,[status(thm)],[c_1624]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_1686,plain,
% 31.51/4.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 31.51/4.50      | v1_relat_1(sK2) = iProver_top ),
% 31.51/4.50      inference(predicate_to_equality,[status(thm)],[c_1685]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_26,plain,
% 31.51/4.50      ( ~ v1_funct_2(X0,X1,X2)
% 31.51/4.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.51/4.50      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 31.51/4.50      | ~ v2_funct_1(X0)
% 31.51/4.50      | ~ v1_funct_1(X0)
% 31.51/4.50      | k2_relset_1(X1,X2,X0) != X2 ),
% 31.51/4.50      inference(cnf_transformation,[],[f90]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_839,plain,
% 31.51/4.50      ( ~ v1_funct_2(X0_50,X0_51,X1_51)
% 31.51/4.50      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 31.51/4.50      | m1_subset_1(k2_funct_1(X0_50),k1_zfmisc_1(k2_zfmisc_1(X1_51,X0_51)))
% 31.51/4.50      | ~ v2_funct_1(X0_50)
% 31.51/4.50      | ~ v1_funct_1(X0_50)
% 31.51/4.50      | k2_relset_1(X0_51,X1_51,X0_50) != X1_51 ),
% 31.51/4.50      inference(subtyping,[status(esa)],[c_26]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_2249,plain,
% 31.51/4.50      ( ~ v1_funct_2(X0_50,sK0,sK1)
% 31.51/4.50      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 31.51/4.50      | m1_subset_1(k2_funct_1(X0_50),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 31.51/4.50      | ~ v2_funct_1(X0_50)
% 31.51/4.50      | ~ v1_funct_1(X0_50)
% 31.51/4.50      | k2_relset_1(sK0,sK1,X0_50) != sK1 ),
% 31.51/4.50      inference(instantiation,[status(thm)],[c_839]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_2250,plain,
% 31.51/4.50      ( k2_relset_1(sK0,sK1,X0_50) != sK1
% 31.51/4.50      | v1_funct_2(X0_50,sK0,sK1) != iProver_top
% 31.51/4.50      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 31.51/4.50      | m1_subset_1(k2_funct_1(X0_50),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
% 31.51/4.50      | v2_funct_1(X0_50) != iProver_top
% 31.51/4.50      | v1_funct_1(X0_50) != iProver_top ),
% 31.51/4.50      inference(predicate_to_equality,[status(thm)],[c_2249]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_2252,plain,
% 31.51/4.50      ( k2_relset_1(sK0,sK1,sK2) != sK1
% 31.51/4.50      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 31.51/4.50      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
% 31.51/4.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 31.51/4.50      | v2_funct_1(sK2) != iProver_top
% 31.51/4.50      | v1_funct_1(sK2) != iProver_top ),
% 31.51/4.50      inference(instantiation,[status(thm)],[c_2250]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_18,plain,
% 31.51/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.51/4.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 31.51/4.50      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 31.51/4.50      | ~ v1_funct_1(X0)
% 31.51/4.50      | ~ v1_funct_1(X3) ),
% 31.51/4.50      inference(cnf_transformation,[],[f80]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_846,plain,
% 31.51/4.50      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 31.51/4.50      | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51)))
% 31.51/4.50      | m1_subset_1(k1_partfun1(X2_51,X3_51,X0_51,X1_51,X1_50,X0_50),k1_zfmisc_1(k2_zfmisc_1(X2_51,X1_51)))
% 31.51/4.50      | ~ v1_funct_1(X0_50)
% 31.51/4.50      | ~ v1_funct_1(X1_50) ),
% 31.51/4.50      inference(subtyping,[status(esa)],[c_18]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_1505,plain,
% 31.51/4.50      ( m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 31.51/4.50      | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51))) != iProver_top
% 31.51/4.50      | m1_subset_1(k1_partfun1(X0_51,X1_51,X2_51,X3_51,X0_50,X1_50),k1_zfmisc_1(k2_zfmisc_1(X0_51,X3_51))) = iProver_top
% 31.51/4.50      | v1_funct_1(X1_50) != iProver_top
% 31.51/4.50      | v1_funct_1(X0_50) != iProver_top ),
% 31.51/4.50      inference(predicate_to_equality,[status(thm)],[c_846]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_4898,plain,
% 31.51/4.50      ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 31.51/4.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 31.51/4.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 31.51/4.50      | v1_funct_1(sK3) != iProver_top
% 31.51/4.50      | v1_funct_1(sK2) != iProver_top ),
% 31.51/4.50      inference(superposition,[status(thm)],[c_4311,c_1505]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_1512,plain,
% 31.51/4.50      ( k2_relset_1(X0_51,X1_51,X0_50) != X1_51
% 31.51/4.50      | v1_funct_2(X0_50,X0_51,X1_51) != iProver_top
% 31.51/4.50      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 31.51/4.50      | m1_subset_1(k2_funct_1(X0_50),k1_zfmisc_1(k2_zfmisc_1(X1_51,X0_51))) = iProver_top
% 31.51/4.50      | v2_funct_1(X0_50) != iProver_top
% 31.51/4.50      | v1_funct_1(X0_50) != iProver_top ),
% 31.51/4.50      inference(predicate_to_equality,[status(thm)],[c_839]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_5089,plain,
% 31.51/4.50      ( v1_funct_2(sK2,sK0,sK1) != iProver_top
% 31.51/4.50      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
% 31.51/4.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 31.51/4.50      | v2_funct_1(sK2) != iProver_top
% 31.51/4.50      | v1_funct_1(sK2) != iProver_top ),
% 31.51/4.50      inference(superposition,[status(thm)],[c_829,c_1512]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_5099,plain,
% 31.51/4.50      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 31.51/4.50      inference(global_propositional_subsumption,
% 31.51/4.50                [status(thm)],
% 31.51/4.50                [c_5089,c_46,c_47,c_48,c_53,c_829,c_2252]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_5108,plain,
% 31.51/4.50      ( k1_partfun1(X0_51,X1_51,sK1,sK0,X0_50,k2_funct_1(sK2)) = k5_relat_1(X0_50,k2_funct_1(sK2))
% 31.51/4.50      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 31.51/4.50      | v1_funct_1(X0_50) != iProver_top
% 31.51/4.50      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 31.51/4.50      inference(superposition,[status(thm)],[c_5099,c_1507]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_5297,plain,
% 31.51/4.50      ( v1_funct_1(X0_50) != iProver_top
% 31.51/4.50      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 31.51/4.50      | k1_partfun1(X0_51,X1_51,sK1,sK0,X0_50,k2_funct_1(sK2)) = k5_relat_1(X0_50,k2_funct_1(sK2)) ),
% 31.51/4.50      inference(global_propositional_subsumption,
% 31.51/4.50                [status(thm)],
% 31.51/4.50                [c_5108,c_46,c_48,c_902,c_1686]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_5298,plain,
% 31.51/4.50      ( k1_partfun1(X0_51,X1_51,sK1,sK0,X0_50,k2_funct_1(sK2)) = k5_relat_1(X0_50,k2_funct_1(sK2))
% 31.51/4.50      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 31.51/4.50      | v1_funct_1(X0_50) != iProver_top ),
% 31.51/4.50      inference(renaming,[status(thm)],[c_5297]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_5304,plain,
% 31.51/4.50      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2))
% 31.51/4.50      | v1_funct_1(sK2) != iProver_top ),
% 31.51/4.50      inference(superposition,[status(thm)],[c_1522,c_5298]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_830,negated_conjecture,
% 31.51/4.50      ( v2_funct_1(sK2) ),
% 31.51/4.50      inference(subtyping,[status(esa)],[c_37]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_1518,plain,
% 31.51/4.50      ( v2_funct_1(sK2) = iProver_top ),
% 31.51/4.50      inference(predicate_to_equality,[status(thm)],[c_830]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_9,plain,
% 31.51/4.50      ( ~ v2_funct_1(X0)
% 31.51/4.50      | ~ v1_relat_1(X0)
% 31.51/4.50      | ~ v1_funct_1(X0)
% 31.51/4.50      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
% 31.51/4.50      inference(cnf_transformation,[],[f111]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_850,plain,
% 31.51/4.50      ( ~ v2_funct_1(X0_50)
% 31.51/4.50      | ~ v1_relat_1(X0_50)
% 31.51/4.50      | ~ v1_funct_1(X0_50)
% 31.51/4.50      | k5_relat_1(X0_50,k2_funct_1(X0_50)) = k6_partfun1(k1_relat_1(X0_50)) ),
% 31.51/4.50      inference(subtyping,[status(esa)],[c_9]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_1501,plain,
% 31.51/4.50      ( k5_relat_1(X0_50,k2_funct_1(X0_50)) = k6_partfun1(k1_relat_1(X0_50))
% 31.51/4.50      | v2_funct_1(X0_50) != iProver_top
% 31.51/4.50      | v1_relat_1(X0_50) != iProver_top
% 31.51/4.50      | v1_funct_1(X0_50) != iProver_top ),
% 31.51/4.50      inference(predicate_to_equality,[status(thm)],[c_850]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_3274,plain,
% 31.51/4.50      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
% 31.51/4.50      | v1_relat_1(sK2) != iProver_top
% 31.51/4.50      | v1_funct_1(sK2) != iProver_top ),
% 31.51/4.50      inference(superposition,[status(thm)],[c_1518,c_1501]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_920,plain,
% 31.51/4.50      ( ~ v2_funct_1(sK2)
% 31.51/4.50      | ~ v1_relat_1(sK2)
% 31.51/4.50      | ~ v1_funct_1(sK2)
% 31.51/4.50      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
% 31.51/4.50      inference(instantiation,[status(thm)],[c_850]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_3552,plain,
% 31.51/4.50      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
% 31.51/4.50      inference(global_propositional_subsumption,
% 31.51/4.50                [status(thm)],
% 31.51/4.50                [c_3274,c_45,c_43,c_37,c_920,c_1685]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_5312,plain,
% 31.51/4.50      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
% 31.51/4.50      | v1_funct_1(sK2) != iProver_top ),
% 31.51/4.50      inference(light_normalisation,[status(thm)],[c_5304,c_3552]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_5856,plain,
% 31.51/4.50      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
% 31.51/4.50      inference(global_propositional_subsumption,
% 31.51/4.50                [status(thm)],
% 31.51/4.50                [c_5312,c_46]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_5223,plain,
% 31.51/4.50      ( sK1 = k1_xboole_0
% 31.51/4.50      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
% 31.51/4.50      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 31.51/4.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 31.51/4.50      | v2_funct_1(sK2) != iProver_top
% 31.51/4.50      | v1_funct_1(sK2) != iProver_top ),
% 31.51/4.50      inference(superposition,[status(thm)],[c_829,c_1515]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_5228,plain,
% 31.51/4.50      ( sK1 = k1_xboole_0
% 31.51/4.50      | k6_partfun1(k1_relat_1(sK2)) = k6_partfun1(sK0)
% 31.51/4.50      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 31.51/4.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 31.51/4.50      | v2_funct_1(sK2) != iProver_top
% 31.51/4.50      | v1_funct_1(sK2) != iProver_top ),
% 31.51/4.50      inference(demodulation,[status(thm)],[c_5223,c_3552]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_35,negated_conjecture,
% 31.51/4.50      ( k1_xboole_0 != sK1 ),
% 31.51/4.50      inference(cnf_transformation,[],[f106]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_832,negated_conjecture,
% 31.51/4.50      ( k1_xboole_0 != sK1 ),
% 31.51/4.50      inference(subtyping,[status(esa)],[c_35]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_1597,plain,
% 31.51/4.50      ( sK1 != X0_51 | k1_xboole_0 != X0_51 | k1_xboole_0 = sK1 ),
% 31.51/4.50      inference(instantiation,[status(thm)],[c_866]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_1598,plain,
% 31.51/4.50      ( sK1 != k1_xboole_0
% 31.51/4.50      | k1_xboole_0 = sK1
% 31.51/4.50      | k1_xboole_0 != k1_xboole_0 ),
% 31.51/4.50      inference(instantiation,[status(thm)],[c_1597]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_5418,plain,
% 31.51/4.50      ( k6_partfun1(k1_relat_1(sK2)) = k6_partfun1(sK0) ),
% 31.51/4.50      inference(global_propositional_subsumption,
% 31.51/4.50                [status(thm)],
% 31.51/4.50                [c_5228,c_46,c_47,c_48,c_53,c_897,c_832,c_1598]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_5858,plain,
% 31.51/4.50      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
% 31.51/4.50      inference(light_normalisation,[status(thm)],[c_5856,c_5418]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_5859,plain,
% 31.51/4.50      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 31.51/4.50      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 31.51/4.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 31.51/4.50      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 31.51/4.50      | v1_funct_1(sK2) != iProver_top ),
% 31.51/4.50      inference(superposition,[status(thm)],[c_5858,c_1505]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_8888,plain,
% 31.51/4.50      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 31.51/4.50      inference(global_propositional_subsumption,
% 31.51/4.50                [status(thm)],
% 31.51/4.50                [c_4314,c_46,c_47,c_48,c_49,c_51,c_53,c_902,c_829,c_1686,
% 31.51/4.50                 c_2252,c_4898,c_5859]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_23,plain,
% 31.51/4.50      ( ~ v1_funct_2(X0,X1,X2)
% 31.51/4.50      | ~ v1_funct_2(X3,X4,X1)
% 31.51/4.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 31.51/4.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.51/4.50      | v2_funct_1(X0)
% 31.51/4.50      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 31.51/4.50      | ~ v1_funct_1(X0)
% 31.51/4.50      | ~ v1_funct_1(X3)
% 31.51/4.50      | k2_relset_1(X4,X1,X3) != X1
% 31.51/4.50      | k1_xboole_0 = X2 ),
% 31.51/4.50      inference(cnf_transformation,[],[f86]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_842,plain,
% 31.51/4.50      ( ~ v1_funct_2(X0_50,X0_51,X1_51)
% 31.51/4.50      | ~ v1_funct_2(X1_50,X2_51,X0_51)
% 31.51/4.50      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 31.51/4.50      | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X2_51,X0_51)))
% 31.51/4.50      | v2_funct_1(X0_50)
% 31.51/4.50      | ~ v2_funct_1(k1_partfun1(X2_51,X0_51,X0_51,X1_51,X1_50,X0_50))
% 31.51/4.50      | ~ v1_funct_1(X0_50)
% 31.51/4.50      | ~ v1_funct_1(X1_50)
% 31.51/4.50      | k2_relset_1(X2_51,X0_51,X1_50) != X0_51
% 31.51/4.50      | k1_xboole_0 = X1_51 ),
% 31.51/4.50      inference(subtyping,[status(esa)],[c_23]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_1509,plain,
% 31.51/4.50      ( k2_relset_1(X0_51,X1_51,X0_50) != X1_51
% 31.51/4.50      | k1_xboole_0 = X2_51
% 31.51/4.50      | v1_funct_2(X1_50,X1_51,X2_51) != iProver_top
% 31.51/4.50      | v1_funct_2(X0_50,X0_51,X1_51) != iProver_top
% 31.51/4.50      | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51))) != iProver_top
% 31.51/4.50      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 31.51/4.50      | v2_funct_1(X1_50) = iProver_top
% 31.51/4.50      | v2_funct_1(k1_partfun1(X0_51,X1_51,X1_51,X2_51,X0_50,X1_50)) != iProver_top
% 31.51/4.50      | v1_funct_1(X1_50) != iProver_top
% 31.51/4.50      | v1_funct_1(X0_50) != iProver_top ),
% 31.51/4.50      inference(predicate_to_equality,[status(thm)],[c_842]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_5569,plain,
% 31.51/4.50      ( k1_xboole_0 = X0_51
% 31.51/4.50      | v1_funct_2(X0_50,sK1,X0_51) != iProver_top
% 31.51/4.50      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 31.51/4.50      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK1,X0_51))) != iProver_top
% 31.51/4.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 31.51/4.50      | v2_funct_1(X0_50) = iProver_top
% 31.51/4.50      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0_51,sK2,X0_50)) != iProver_top
% 31.51/4.50      | v1_funct_1(X0_50) != iProver_top
% 31.51/4.50      | v1_funct_1(sK2) != iProver_top ),
% 31.51/4.50      inference(superposition,[status(thm)],[c_829,c_1509]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_5582,plain,
% 31.51/4.50      ( v1_funct_1(X0_50) != iProver_top
% 31.51/4.50      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0_51,sK2,X0_50)) != iProver_top
% 31.51/4.50      | v2_funct_1(X0_50) = iProver_top
% 31.51/4.50      | v1_funct_2(X0_50,sK1,X0_51) != iProver_top
% 31.51/4.50      | k1_xboole_0 = X0_51
% 31.51/4.50      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK1,X0_51))) != iProver_top ),
% 31.51/4.50      inference(global_propositional_subsumption,
% 31.51/4.50                [status(thm)],
% 31.51/4.50                [c_5569,c_46,c_47,c_48]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_5583,plain,
% 31.51/4.50      ( k1_xboole_0 = X0_51
% 31.51/4.50      | v1_funct_2(X0_50,sK1,X0_51) != iProver_top
% 31.51/4.50      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(sK1,X0_51))) != iProver_top
% 31.51/4.50      | v2_funct_1(X0_50) = iProver_top
% 31.51/4.50      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0_51,sK2,X0_50)) != iProver_top
% 31.51/4.50      | v1_funct_1(X0_50) != iProver_top ),
% 31.51/4.50      inference(renaming,[status(thm)],[c_5582]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_5586,plain,
% 31.51/4.50      ( sK0 = k1_xboole_0
% 31.51/4.50      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 31.51/4.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 31.51/4.50      | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
% 31.51/4.50      | v2_funct_1(sK3) = iProver_top
% 31.51/4.50      | v1_funct_1(sK3) != iProver_top ),
% 31.51/4.50      inference(superposition,[status(thm)],[c_4311,c_5583]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_5696,plain,
% 31.51/4.50      ( v2_funct_1(sK3) = iProver_top
% 31.51/4.50      | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top ),
% 31.51/4.50      inference(global_propositional_subsumption,
% 31.51/4.50                [status(thm)],
% 31.51/4.50                [c_5586,c_49,c_50,c_51,c_897,c_831,c_1586]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_5697,plain,
% 31.51/4.50      ( v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
% 31.51/4.50      | v2_funct_1(sK3) = iProver_top ),
% 31.51/4.50      inference(renaming,[status(thm)],[c_5696]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_8890,plain,
% 31.51/4.50      ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 31.51/4.50      | v2_funct_1(sK3) = iProver_top ),
% 31.51/4.50      inference(demodulation,[status(thm)],[c_8888,c_5697]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_33931,plain,
% 31.51/4.50      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
% 31.51/4.50      inference(global_propositional_subsumption,
% 31.51/4.50                [status(thm)],
% 31.51/4.50                [c_5224,c_49,c_50,c_51,c_897,c_831,c_1586,c_5083,c_8890]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_8989,plain,
% 31.51/4.50      ( v2_funct_1(sK3) = iProver_top ),
% 31.51/4.50      inference(global_propositional_subsumption,
% 31.51/4.50                [status(thm)],
% 31.51/4.50                [c_8890,c_5083]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_8993,plain,
% 31.51/4.50      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
% 31.51/4.50      | v1_relat_1(sK3) != iProver_top
% 31.51/4.50      | v1_funct_1(sK3) != iProver_top ),
% 31.51/4.50      inference(superposition,[status(thm)],[c_8989,c_1501]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_1885,plain,
% 31.51/4.50      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 31.51/4.50      | v1_relat_1(sK3) ),
% 31.51/4.50      inference(instantiation,[status(thm)],[c_848]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_1994,plain,
% 31.51/4.50      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 31.51/4.50      | v1_relat_1(sK3) ),
% 31.51/4.50      inference(instantiation,[status(thm)],[c_1885]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_1995,plain,
% 31.51/4.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 31.51/4.50      | v1_relat_1(sK3) = iProver_top ),
% 31.51/4.50      inference(predicate_to_equality,[status(thm)],[c_1994]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_13,plain,
% 31.51/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.51/4.50      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 31.51/4.50      inference(cnf_transformation,[],[f74]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_847,plain,
% 31.51/4.50      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 31.51/4.50      | k2_relset_1(X0_51,X1_51,X0_50) = k2_relat_1(X0_50) ),
% 31.51/4.50      inference(subtyping,[status(esa)],[c_13]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_1504,plain,
% 31.51/4.50      ( k2_relset_1(X0_51,X1_51,X0_50) = k2_relat_1(X0_50)
% 31.51/4.50      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top ),
% 31.51/4.50      inference(predicate_to_equality,[status(thm)],[c_847]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_2358,plain,
% 31.51/4.50      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 31.51/4.50      inference(superposition,[status(thm)],[c_1519,c_1504]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_2361,plain,
% 31.51/4.50      ( k2_relat_1(sK3) = sK0 ),
% 31.51/4.50      inference(light_normalisation,[status(thm)],[c_2358,c_2060]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_31,plain,
% 31.51/4.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 31.51/4.50      | ~ v1_relat_1(X0)
% 31.51/4.50      | ~ v1_funct_1(X0) ),
% 31.51/4.50      inference(cnf_transformation,[],[f95]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_835,plain,
% 31.51/4.50      ( m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_50),k2_relat_1(X0_50))))
% 31.51/4.50      | ~ v1_relat_1(X0_50)
% 31.51/4.50      | ~ v1_funct_1(X0_50) ),
% 31.51/4.50      inference(subtyping,[status(esa)],[c_31]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_1516,plain,
% 31.51/4.50      ( m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0_50),k2_relat_1(X0_50)))) = iProver_top
% 31.51/4.50      | v1_relat_1(X0_50) != iProver_top
% 31.51/4.50      | v1_funct_1(X0_50) != iProver_top ),
% 31.51/4.50      inference(predicate_to_equality,[status(thm)],[c_835]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_2587,plain,
% 31.51/4.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK0))) = iProver_top
% 31.51/4.50      | v1_relat_1(sK3) != iProver_top
% 31.51/4.50      | v1_funct_1(sK3) != iProver_top ),
% 31.51/4.50      inference(superposition,[status(thm)],[c_2361,c_1516]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_32,plain,
% 31.51/4.50      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 31.51/4.50      | ~ v1_relat_1(X0)
% 31.51/4.50      | ~ v1_funct_1(X0) ),
% 31.51/4.50      inference(cnf_transformation,[],[f94]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_834,plain,
% 31.51/4.50      ( v1_funct_2(X0_50,k1_relat_1(X0_50),k2_relat_1(X0_50))
% 31.51/4.50      | ~ v1_relat_1(X0_50)
% 31.51/4.50      | ~ v1_funct_1(X0_50) ),
% 31.51/4.50      inference(subtyping,[status(esa)],[c_32]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_1517,plain,
% 31.51/4.50      ( v1_funct_2(X0_50,k1_relat_1(X0_50),k2_relat_1(X0_50)) = iProver_top
% 31.51/4.50      | v1_relat_1(X0_50) != iProver_top
% 31.51/4.50      | v1_funct_1(X0_50) != iProver_top ),
% 31.51/4.50      inference(predicate_to_equality,[status(thm)],[c_834]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_2588,plain,
% 31.51/4.50      ( v1_funct_2(sK3,k1_relat_1(sK3),sK0) = iProver_top
% 31.51/4.50      | v1_relat_1(sK3) != iProver_top
% 31.51/4.50      | v1_funct_1(sK3) != iProver_top ),
% 31.51/4.50      inference(superposition,[status(thm)],[c_2361,c_1517]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_2713,plain,
% 31.51/4.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK0))) = iProver_top ),
% 31.51/4.50      inference(global_propositional_subsumption,
% 31.51/4.50                [status(thm)],
% 31.51/4.50                [c_2587,c_49,c_51,c_1995]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_2717,plain,
% 31.51/4.50      ( k2_relset_1(k1_relat_1(sK3),sK0,sK3) = k2_relat_1(sK3) ),
% 31.51/4.50      inference(superposition,[status(thm)],[c_2713,c_1504]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_2719,plain,
% 31.51/4.50      ( k2_relset_1(k1_relat_1(sK3),sK0,sK3) = sK0 ),
% 31.51/4.50      inference(light_normalisation,[status(thm)],[c_2717,c_2361]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_5226,plain,
% 31.51/4.50      ( sK0 = k1_xboole_0
% 31.51/4.50      | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
% 31.51/4.50      | v1_funct_2(sK3,k1_relat_1(sK3),sK0) != iProver_top
% 31.51/4.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK0))) != iProver_top
% 31.51/4.50      | v2_funct_1(sK3) != iProver_top
% 31.51/4.50      | v1_funct_1(sK3) != iProver_top ),
% 31.51/4.50      inference(superposition,[status(thm)],[c_2719,c_1515]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_9174,plain,
% 31.51/4.50      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3)) ),
% 31.51/4.50      inference(global_propositional_subsumption,
% 31.51/4.50                [status(thm)],
% 31.51/4.50                [c_8993,c_49,c_51,c_897,c_831,c_1586,c_1995,c_2587,
% 31.51/4.50                 c_2588,c_5083,c_5226,c_8890]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_33933,plain,
% 31.51/4.50      ( k6_partfun1(k1_relat_1(sK3)) = k6_partfun1(sK1) ),
% 31.51/4.50      inference(demodulation,[status(thm)],[c_33931,c_9174]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_5090,plain,
% 31.51/4.50      ( v1_funct_2(sK3,sK1,sK0) != iProver_top
% 31.51/4.50      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 31.51/4.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 31.51/4.50      | v2_funct_1(sK3) != iProver_top
% 31.51/4.50      | v1_funct_1(sK3) != iProver_top ),
% 31.51/4.50      inference(superposition,[status(thm)],[c_2060,c_1512]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_26223,plain,
% 31.51/4.50      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 31.51/4.50      inference(global_propositional_subsumption,
% 31.51/4.50                [status(thm)],
% 31.51/4.50                [c_5090,c_49,c_50,c_51,c_5083,c_8890]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_26242,plain,
% 31.51/4.50      ( k1_partfun1(X0_51,X1_51,sK0,sK1,X0_50,k2_funct_1(sK3)) = k5_relat_1(X0_50,k2_funct_1(sK3))
% 31.51/4.50      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 31.51/4.50      | v1_funct_1(X0_50) != iProver_top
% 31.51/4.50      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 31.51/4.50      inference(superposition,[status(thm)],[c_26223,c_1507]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_28,plain,
% 31.51/4.50      ( ~ v1_funct_2(X0,X1,X2)
% 31.51/4.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.51/4.50      | ~ v2_funct_1(X0)
% 31.51/4.50      | ~ v1_funct_1(X0)
% 31.51/4.50      | v1_funct_1(k2_funct_1(X0))
% 31.51/4.50      | k2_relset_1(X1,X2,X0) != X2 ),
% 31.51/4.50      inference(cnf_transformation,[],[f88]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_245,plain,
% 31.51/4.50      ( v1_funct_1(k2_funct_1(X0))
% 31.51/4.50      | ~ v1_funct_1(X0)
% 31.51/4.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 31.51/4.50      inference(global_propositional_subsumption,
% 31.51/4.50                [status(thm)],
% 31.51/4.50                [c_28,c_11,c_0]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_246,plain,
% 31.51/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.51/4.50      | ~ v1_funct_1(X0)
% 31.51/4.50      | v1_funct_1(k2_funct_1(X0)) ),
% 31.51/4.50      inference(renaming,[status(thm)],[c_245]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_822,plain,
% 31.51/4.50      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 31.51/4.50      | ~ v1_funct_1(X0_50)
% 31.51/4.50      | v1_funct_1(k2_funct_1(X0_50)) ),
% 31.51/4.50      inference(subtyping,[status(esa)],[c_246]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_1525,plain,
% 31.51/4.50      ( m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 31.51/4.50      | v1_funct_1(X0_50) != iProver_top
% 31.51/4.50      | v1_funct_1(k2_funct_1(X0_50)) = iProver_top ),
% 31.51/4.50      inference(predicate_to_equality,[status(thm)],[c_822]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_2820,plain,
% 31.51/4.50      ( v1_funct_1(k2_funct_1(sK3)) = iProver_top
% 31.51/4.50      | v1_funct_1(sK3) != iProver_top ),
% 31.51/4.50      inference(superposition,[status(thm)],[c_2713,c_1525]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_26405,plain,
% 31.51/4.50      ( v1_funct_1(X0_50) != iProver_top
% 31.51/4.50      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 31.51/4.50      | k1_partfun1(X0_51,X1_51,sK0,sK1,X0_50,k2_funct_1(sK3)) = k5_relat_1(X0_50,k2_funct_1(sK3)) ),
% 31.51/4.50      inference(global_propositional_subsumption,
% 31.51/4.50                [status(thm)],
% 31.51/4.50                [c_26242,c_49,c_2820]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_26406,plain,
% 31.51/4.50      ( k1_partfun1(X0_51,X1_51,sK0,sK1,X0_50,k2_funct_1(sK3)) = k5_relat_1(X0_50,k2_funct_1(sK3))
% 31.51/4.50      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 31.51/4.50      | v1_funct_1(X0_50) != iProver_top ),
% 31.51/4.50      inference(renaming,[status(thm)],[c_26405]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_26411,plain,
% 31.51/4.50      ( k1_partfun1(sK1,sK0,sK0,sK1,sK3,k2_funct_1(sK3)) = k5_relat_1(sK3,k2_funct_1(sK3))
% 31.51/4.50      | v1_funct_1(sK3) != iProver_top ),
% 31.51/4.50      inference(superposition,[status(thm)],[c_1519,c_26406]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_26435,plain,
% 31.51/4.50      ( k1_partfun1(sK1,sK0,sK0,sK1,sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
% 31.51/4.50      | v1_funct_1(sK3) != iProver_top ),
% 31.51/4.50      inference(light_normalisation,[status(thm)],[c_26411,c_9174]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_26687,plain,
% 31.51/4.50      ( k1_partfun1(sK1,sK0,sK0,sK1,sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3)) ),
% 31.51/4.50      inference(global_propositional_subsumption,
% 31.51/4.50                [status(thm)],
% 31.51/4.50                [c_26435,c_49]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_14,plain,
% 31.51/4.50      ( r2_relset_1(X0,X1,X2,X2)
% 31.51/4.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 31.51/4.50      inference(cnf_transformation,[],[f113]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_471,plain,
% 31.51/4.50      ( ~ v1_funct_2(X0,X1,X2)
% 31.51/4.50      | ~ v1_funct_2(X3,X2,X1)
% 31.51/4.50      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
% 31.51/4.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.51/4.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 31.51/4.50      | ~ v1_funct_1(X0)
% 31.51/4.50      | ~ v1_funct_1(X3)
% 31.51/4.50      | X1 != X6
% 31.51/4.50      | X1 != X5
% 31.51/4.50      | k1_partfun1(X1,X2,X2,X1,X0,X3) != X4
% 31.51/4.50      | k2_relset_1(X2,X1,X3) = X1
% 31.51/4.50      | k6_partfun1(X1) != X4 ),
% 31.51/4.50      inference(resolution_lifted,[status(thm)],[c_14,c_21]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_472,plain,
% 31.51/4.50      ( ~ v1_funct_2(X0,X1,X2)
% 31.51/4.50      | ~ v1_funct_2(X3,X2,X1)
% 31.51/4.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.51/4.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 31.51/4.50      | ~ m1_subset_1(k1_partfun1(X1,X2,X2,X1,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 31.51/4.50      | ~ v1_funct_1(X0)
% 31.51/4.50      | ~ v1_funct_1(X3)
% 31.51/4.50      | k2_relset_1(X2,X1,X3) = X1
% 31.51/4.50      | k6_partfun1(X1) != k1_partfun1(X1,X2,X2,X1,X0,X3) ),
% 31.51/4.50      inference(unflattening,[status(thm)],[c_471]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_494,plain,
% 31.51/4.50      ( ~ v1_funct_2(X0,X1,X2)
% 31.51/4.50      | ~ v1_funct_2(X3,X2,X1)
% 31.51/4.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.51/4.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 31.51/4.50      | ~ v1_funct_1(X0)
% 31.51/4.50      | ~ v1_funct_1(X3)
% 31.51/4.50      | k2_relset_1(X2,X1,X3) = X1
% 31.51/4.50      | k6_partfun1(X1) != k1_partfun1(X1,X2,X2,X1,X0,X3) ),
% 31.51/4.50      inference(forward_subsumption_resolution,
% 31.51/4.50                [status(thm)],
% 31.51/4.50                [c_472,c_18]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_821,plain,
% 31.51/4.50      ( ~ v1_funct_2(X0_50,X0_51,X1_51)
% 31.51/4.50      | ~ v1_funct_2(X1_50,X1_51,X0_51)
% 31.51/4.50      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 31.51/4.50      | ~ m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X1_51,X0_51)))
% 31.51/4.50      | ~ v1_funct_1(X0_50)
% 31.51/4.50      | ~ v1_funct_1(X1_50)
% 31.51/4.50      | k2_relset_1(X1_51,X0_51,X1_50) = X0_51
% 31.51/4.50      | k6_partfun1(X0_51) != k1_partfun1(X0_51,X1_51,X1_51,X0_51,X0_50,X1_50) ),
% 31.51/4.50      inference(subtyping,[status(esa)],[c_494]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_1526,plain,
% 31.51/4.50      ( k2_relset_1(X0_51,X1_51,X0_50) = X1_51
% 31.51/4.50      | k6_partfun1(X1_51) != k1_partfun1(X1_51,X0_51,X0_51,X1_51,X1_50,X0_50)
% 31.51/4.50      | v1_funct_2(X1_50,X1_51,X0_51) != iProver_top
% 31.51/4.50      | v1_funct_2(X0_50,X0_51,X1_51) != iProver_top
% 31.51/4.50      | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X1_51,X0_51))) != iProver_top
% 31.51/4.50      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 31.51/4.50      | v1_funct_1(X1_50) != iProver_top
% 31.51/4.50      | v1_funct_1(X0_50) != iProver_top ),
% 31.51/4.50      inference(predicate_to_equality,[status(thm)],[c_821]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_26693,plain,
% 31.51/4.50      ( k2_relset_1(sK0,sK1,k2_funct_1(sK3)) = sK1
% 31.51/4.50      | k6_partfun1(k1_relat_1(sK3)) != k6_partfun1(sK1)
% 31.51/4.50      | v1_funct_2(k2_funct_1(sK3),sK0,sK1) != iProver_top
% 31.51/4.50      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 31.51/4.50      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 31.51/4.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 31.51/4.50      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 31.51/4.50      | v1_funct_1(sK3) != iProver_top ),
% 31.51/4.50      inference(superposition,[status(thm)],[c_26687,c_1526]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_26240,plain,
% 31.51/4.50      ( k2_relset_1(sK0,sK1,k2_funct_1(sK3)) = k2_relat_1(k2_funct_1(sK3)) ),
% 31.51/4.50      inference(superposition,[status(thm)],[c_26223,c_1504]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_6,plain,
% 31.51/4.50      ( ~ v2_funct_1(X0)
% 31.51/4.50      | ~ v1_relat_1(X0)
% 31.51/4.50      | ~ v1_funct_1(X0)
% 31.51/4.50      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 31.51/4.50      inference(cnf_transformation,[],[f68]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_853,plain,
% 31.51/4.50      ( ~ v2_funct_1(X0_50)
% 31.51/4.50      | ~ v1_relat_1(X0_50)
% 31.51/4.50      | ~ v1_funct_1(X0_50)
% 31.51/4.50      | k2_relat_1(k2_funct_1(X0_50)) = k1_relat_1(X0_50) ),
% 31.51/4.50      inference(subtyping,[status(esa)],[c_6]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_1498,plain,
% 31.51/4.50      ( k2_relat_1(k2_funct_1(X0_50)) = k1_relat_1(X0_50)
% 31.51/4.50      | v2_funct_1(X0_50) != iProver_top
% 31.51/4.50      | v1_relat_1(X0_50) != iProver_top
% 31.51/4.50      | v1_funct_1(X0_50) != iProver_top ),
% 31.51/4.50      inference(predicate_to_equality,[status(thm)],[c_853]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_8996,plain,
% 31.51/4.50      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
% 31.51/4.50      | v1_relat_1(sK3) != iProver_top
% 31.51/4.50      | v1_funct_1(sK3) != iProver_top ),
% 31.51/4.50      inference(superposition,[status(thm)],[c_8989,c_1498]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_9009,plain,
% 31.51/4.50      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 31.51/4.50      inference(global_propositional_subsumption,
% 31.51/4.50                [status(thm)],
% 31.51/4.50                [c_8996,c_49,c_51,c_1995]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_26245,plain,
% 31.51/4.50      ( k2_relset_1(sK0,sK1,k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 31.51/4.50      inference(light_normalisation,[status(thm)],[c_26240,c_9009]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_26694,plain,
% 31.51/4.50      ( k1_relat_1(sK3) = sK1
% 31.51/4.50      | k6_partfun1(k1_relat_1(sK3)) != k6_partfun1(sK1)
% 31.51/4.50      | v1_funct_2(k2_funct_1(sK3),sK0,sK1) != iProver_top
% 31.51/4.50      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 31.51/4.50      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 31.51/4.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 31.51/4.50      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 31.51/4.50      | v1_funct_1(sK3) != iProver_top ),
% 31.51/4.50      inference(demodulation,[status(thm)],[c_26693,c_26245]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_1,plain,
% 31.51/4.50      ( ~ v1_relat_1(X0)
% 31.51/4.50      | v1_relat_1(k2_funct_1(X0))
% 31.51/4.50      | ~ v1_funct_1(X0) ),
% 31.51/4.50      inference(cnf_transformation,[],[f61]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_858,plain,
% 31.51/4.50      ( ~ v1_relat_1(X0_50)
% 31.51/4.50      | v1_relat_1(k2_funct_1(X0_50))
% 31.51/4.50      | ~ v1_funct_1(X0_50) ),
% 31.51/4.50      inference(subtyping,[status(esa)],[c_1]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_22705,plain,
% 31.51/4.50      ( v1_relat_1(k2_funct_1(sK3))
% 31.51/4.50      | ~ v1_relat_1(sK3)
% 31.51/4.50      | ~ v1_funct_1(sK3) ),
% 31.51/4.50      inference(instantiation,[status(thm)],[c_858]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_2616,plain,
% 31.51/4.50      ( X0_50 != X1_50
% 31.51/4.50      | X0_50 = k2_funct_1(X2_50)
% 31.51/4.50      | k2_funct_1(X2_50) != X1_50 ),
% 31.51/4.50      inference(instantiation,[status(thm)],[c_865]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_7967,plain,
% 31.51/4.50      ( X0_50 != X1_50
% 31.51/4.50      | X0_50 = k2_funct_1(k2_funct_1(X1_50))
% 31.51/4.50      | k2_funct_1(k2_funct_1(X1_50)) != X1_50 ),
% 31.51/4.50      inference(instantiation,[status(thm)],[c_2616]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_22163,plain,
% 31.51/4.50      ( k2_funct_1(k2_funct_1(X0_50)) != X0_50
% 31.51/4.50      | k2_funct_1(sK3) != X0_50
% 31.51/4.50      | k2_funct_1(sK3) = k2_funct_1(k2_funct_1(X0_50)) ),
% 31.51/4.50      inference(instantiation,[status(thm)],[c_7967]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_22168,plain,
% 31.51/4.50      ( k2_funct_1(k2_funct_1(sK2)) != sK2
% 31.51/4.50      | k2_funct_1(sK3) = k2_funct_1(k2_funct_1(sK2))
% 31.51/4.50      | k2_funct_1(sK3) != sK2 ),
% 31.51/4.50      inference(instantiation,[status(thm)],[c_22163]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_871,plain,
% 31.51/4.50      ( ~ v2_funct_1(X0_50) | v2_funct_1(X1_50) | X1_50 != X0_50 ),
% 31.51/4.50      theory(equality) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_1814,plain,
% 31.51/4.50      ( ~ v2_funct_1(X0_50)
% 31.51/4.50      | v2_funct_1(k2_funct_1(X1_50))
% 31.51/4.50      | k2_funct_1(X1_50) != X0_50 ),
% 31.51/4.50      inference(instantiation,[status(thm)],[c_871]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_2071,plain,
% 31.51/4.50      ( ~ v2_funct_1(k2_funct_1(X0_50))
% 31.51/4.50      | v2_funct_1(k2_funct_1(X1_50))
% 31.51/4.50      | k2_funct_1(X1_50) != k2_funct_1(X0_50) ),
% 31.51/4.50      inference(instantiation,[status(thm)],[c_1814]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_9235,plain,
% 31.51/4.50      ( ~ v2_funct_1(k2_funct_1(X0_50))
% 31.51/4.50      | v2_funct_1(k2_funct_1(sK3))
% 31.51/4.50      | k2_funct_1(sK3) != k2_funct_1(X0_50) ),
% 31.51/4.50      inference(instantiation,[status(thm)],[c_2071]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_22162,plain,
% 31.51/4.50      ( ~ v2_funct_1(k2_funct_1(k2_funct_1(X0_50)))
% 31.51/4.50      | v2_funct_1(k2_funct_1(sK3))
% 31.51/4.50      | k2_funct_1(sK3) != k2_funct_1(k2_funct_1(X0_50)) ),
% 31.51/4.50      inference(instantiation,[status(thm)],[c_9235]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_22165,plain,
% 31.51/4.50      ( ~ v2_funct_1(k2_funct_1(k2_funct_1(sK2)))
% 31.51/4.50      | v2_funct_1(k2_funct_1(sK3))
% 31.51/4.50      | k2_funct_1(sK3) != k2_funct_1(k2_funct_1(sK2)) ),
% 31.51/4.50      inference(instantiation,[status(thm)],[c_22162]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_10,plain,
% 31.51/4.50      ( ~ v2_funct_1(X0)
% 31.51/4.50      | ~ v1_relat_1(X0)
% 31.51/4.50      | ~ v1_relat_1(X1)
% 31.51/4.50      | ~ v1_funct_1(X0)
% 31.51/4.50      | ~ v1_funct_1(X1)
% 31.51/4.50      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
% 31.51/4.50      | k1_relat_1(X0) != k2_relat_1(X1)
% 31.51/4.50      | k2_funct_1(X0) = X1 ),
% 31.51/4.50      inference(cnf_transformation,[],[f112]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_849,plain,
% 31.51/4.50      ( ~ v2_funct_1(X0_50)
% 31.51/4.50      | ~ v1_relat_1(X0_50)
% 31.51/4.50      | ~ v1_relat_1(X1_50)
% 31.51/4.50      | ~ v1_funct_1(X0_50)
% 31.51/4.50      | ~ v1_funct_1(X1_50)
% 31.51/4.50      | k1_relat_1(X0_50) != k2_relat_1(X1_50)
% 31.51/4.50      | k5_relat_1(X1_50,X0_50) != k6_partfun1(k2_relat_1(X0_50))
% 31.51/4.50      | k2_funct_1(X0_50) = X1_50 ),
% 31.51/4.50      inference(subtyping,[status(esa)],[c_10]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_1502,plain,
% 31.51/4.50      ( k1_relat_1(X0_50) != k2_relat_1(X1_50)
% 31.51/4.50      | k5_relat_1(X1_50,X0_50) != k6_partfun1(k2_relat_1(X0_50))
% 31.51/4.50      | k2_funct_1(X0_50) = X1_50
% 31.51/4.50      | v2_funct_1(X0_50) != iProver_top
% 31.51/4.50      | v1_relat_1(X0_50) != iProver_top
% 31.51/4.50      | v1_relat_1(X1_50) != iProver_top
% 31.51/4.50      | v1_funct_1(X0_50) != iProver_top
% 31.51/4.50      | v1_funct_1(X1_50) != iProver_top ),
% 31.51/4.50      inference(predicate_to_equality,[status(thm)],[c_849]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_8894,plain,
% 31.51/4.50      ( k1_relat_1(sK3) != k2_relat_1(sK2)
% 31.51/4.50      | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
% 31.51/4.50      | k2_funct_1(sK3) = sK2
% 31.51/4.50      | v2_funct_1(sK3) != iProver_top
% 31.51/4.50      | v1_relat_1(sK3) != iProver_top
% 31.51/4.50      | v1_relat_1(sK2) != iProver_top
% 31.51/4.50      | v1_funct_1(sK3) != iProver_top
% 31.51/4.50      | v1_funct_1(sK2) != iProver_top ),
% 31.51/4.50      inference(superposition,[status(thm)],[c_8888,c_1502]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_2359,plain,
% 31.51/4.50      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 31.51/4.50      inference(superposition,[status(thm)],[c_1522,c_1504]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_2360,plain,
% 31.51/4.50      ( k2_relat_1(sK2) = sK1 ),
% 31.51/4.50      inference(light_normalisation,[status(thm)],[c_2359,c_829]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_8895,plain,
% 31.51/4.50      ( k1_relat_1(sK3) != sK1
% 31.51/4.50      | k6_partfun1(sK0) != k6_partfun1(sK0)
% 31.51/4.50      | k2_funct_1(sK3) = sK2
% 31.51/4.50      | v2_funct_1(sK3) != iProver_top
% 31.51/4.50      | v1_relat_1(sK3) != iProver_top
% 31.51/4.50      | v1_relat_1(sK2) != iProver_top
% 31.51/4.50      | v1_funct_1(sK3) != iProver_top
% 31.51/4.50      | v1_funct_1(sK2) != iProver_top ),
% 31.51/4.50      inference(light_normalisation,[status(thm)],[c_8894,c_2360,c_2361]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_8896,plain,
% 31.51/4.50      ( k1_relat_1(sK3) != sK1
% 31.51/4.50      | k2_funct_1(sK3) = sK2
% 31.51/4.50      | v2_funct_1(sK3) != iProver_top
% 31.51/4.50      | v1_relat_1(sK3) != iProver_top
% 31.51/4.50      | v1_relat_1(sK2) != iProver_top
% 31.51/4.50      | v1_funct_1(sK3) != iProver_top
% 31.51/4.50      | v1_funct_1(sK2) != iProver_top ),
% 31.51/4.50      inference(equality_resolution_simp,[status(thm)],[c_8895]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_10318,plain,
% 31.51/4.50      ( k2_funct_1(sK3) = sK2 | k1_relat_1(sK3) != sK1 ),
% 31.51/4.50      inference(global_propositional_subsumption,
% 31.51/4.50                [status(thm)],
% 31.51/4.50                [c_8896,c_46,c_48,c_49,c_51,c_1686,c_1995,c_5083,c_8890]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_10319,plain,
% 31.51/4.50      ( k1_relat_1(sK3) != sK1 | k2_funct_1(sK3) = sK2 ),
% 31.51/4.50      inference(renaming,[status(thm)],[c_10318]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_9176,plain,
% 31.51/4.50      ( k1_relat_1(k2_funct_1(sK3)) != k2_relat_1(sK3)
% 31.51/4.50      | k6_partfun1(k2_relat_1(k2_funct_1(sK3))) != k6_partfun1(k1_relat_1(sK3))
% 31.51/4.50      | k2_funct_1(k2_funct_1(sK3)) = sK3
% 31.51/4.50      | v2_funct_1(k2_funct_1(sK3)) != iProver_top
% 31.51/4.50      | v1_relat_1(k2_funct_1(sK3)) != iProver_top
% 31.51/4.50      | v1_relat_1(sK3) != iProver_top
% 31.51/4.50      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 31.51/4.50      | v1_funct_1(sK3) != iProver_top ),
% 31.51/4.50      inference(superposition,[status(thm)],[c_9174,c_1502]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_9177,plain,
% 31.51/4.50      ( k1_relat_1(k2_funct_1(sK3)) != sK0
% 31.51/4.50      | k6_partfun1(k1_relat_1(sK3)) != k6_partfun1(k1_relat_1(sK3))
% 31.51/4.50      | k2_funct_1(k2_funct_1(sK3)) = sK3
% 31.51/4.50      | v2_funct_1(k2_funct_1(sK3)) != iProver_top
% 31.51/4.50      | v1_relat_1(k2_funct_1(sK3)) != iProver_top
% 31.51/4.50      | v1_relat_1(sK3) != iProver_top
% 31.51/4.50      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 31.51/4.50      | v1_funct_1(sK3) != iProver_top ),
% 31.51/4.50      inference(light_normalisation,[status(thm)],[c_9176,c_2361,c_9009]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_9178,plain,
% 31.51/4.50      ( k1_relat_1(k2_funct_1(sK3)) != sK0
% 31.51/4.50      | k2_funct_1(k2_funct_1(sK3)) = sK3
% 31.51/4.50      | v2_funct_1(k2_funct_1(sK3)) != iProver_top
% 31.51/4.50      | v1_relat_1(k2_funct_1(sK3)) != iProver_top
% 31.51/4.50      | v1_relat_1(sK3) != iProver_top
% 31.51/4.50      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 31.51/4.50      | v1_funct_1(sK3) != iProver_top ),
% 31.51/4.50      inference(equality_resolution_simp,[status(thm)],[c_9177]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_9179,plain,
% 31.51/4.50      ( ~ v2_funct_1(k2_funct_1(sK3))
% 31.51/4.50      | ~ v1_relat_1(k2_funct_1(sK3))
% 31.51/4.50      | ~ v1_relat_1(sK3)
% 31.51/4.50      | ~ v1_funct_1(k2_funct_1(sK3))
% 31.51/4.50      | ~ v1_funct_1(sK3)
% 31.51/4.50      | k1_relat_1(k2_funct_1(sK3)) != sK0
% 31.51/4.50      | k2_funct_1(k2_funct_1(sK3)) = sK3 ),
% 31.51/4.50      inference(predicate_to_equality_rev,[status(thm)],[c_9178]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_7,plain,
% 31.51/4.50      ( ~ v2_funct_1(X0)
% 31.51/4.50      | ~ v1_relat_1(X0)
% 31.51/4.50      | ~ v1_funct_1(X0)
% 31.51/4.50      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 31.51/4.50      inference(cnf_transformation,[],[f67]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_852,plain,
% 31.51/4.50      ( ~ v2_funct_1(X0_50)
% 31.51/4.50      | ~ v1_relat_1(X0_50)
% 31.51/4.50      | ~ v1_funct_1(X0_50)
% 31.51/4.50      | k1_relat_1(k2_funct_1(X0_50)) = k2_relat_1(X0_50) ),
% 31.51/4.50      inference(subtyping,[status(esa)],[c_7]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_1499,plain,
% 31.51/4.50      ( k1_relat_1(k2_funct_1(X0_50)) = k2_relat_1(X0_50)
% 31.51/4.50      | v2_funct_1(X0_50) != iProver_top
% 31.51/4.50      | v1_relat_1(X0_50) != iProver_top
% 31.51/4.50      | v1_funct_1(X0_50) != iProver_top ),
% 31.51/4.50      inference(predicate_to_equality,[status(thm)],[c_852]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_8995,plain,
% 31.51/4.50      ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
% 31.51/4.50      | v1_relat_1(sK3) != iProver_top
% 31.51/4.50      | v1_funct_1(sK3) != iProver_top ),
% 31.51/4.50      inference(superposition,[status(thm)],[c_8989,c_1499]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_8997,plain,
% 31.51/4.50      ( k1_relat_1(k2_funct_1(sK3)) = sK0
% 31.51/4.50      | v1_relat_1(sK3) != iProver_top
% 31.51/4.50      | v1_funct_1(sK3) != iProver_top ),
% 31.51/4.50      inference(light_normalisation,[status(thm)],[c_8995,c_2361]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_1637,plain,
% 31.51/4.50      ( X0_50 != X1_50 | sK3 != X1_50 | sK3 = X0_50 ),
% 31.51/4.50      inference(instantiation,[status(thm)],[c_865]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_1787,plain,
% 31.51/4.50      ( X0_50 != sK3 | sK3 = X0_50 | sK3 != sK3 ),
% 31.51/4.50      inference(instantiation,[status(thm)],[c_1637]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_7920,plain,
% 31.51/4.50      ( k2_funct_1(k2_funct_1(sK3)) != sK3
% 31.51/4.50      | sK3 = k2_funct_1(k2_funct_1(sK3))
% 31.51/4.50      | sK3 != sK3 ),
% 31.51/4.50      inference(instantiation,[status(thm)],[c_1787]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_7911,plain,
% 31.51/4.50      ( ~ v2_funct_1(X0_50)
% 31.51/4.50      | v2_funct_1(k2_funct_1(k2_funct_1(X0_50)))
% 31.51/4.50      | k2_funct_1(k2_funct_1(X0_50)) != X0_50 ),
% 31.51/4.50      inference(instantiation,[status(thm)],[c_1814]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_7913,plain,
% 31.51/4.50      ( v2_funct_1(k2_funct_1(k2_funct_1(sK2)))
% 31.51/4.50      | ~ v2_funct_1(sK2)
% 31.51/4.50      | k2_funct_1(k2_funct_1(sK2)) != sK2 ),
% 31.51/4.50      inference(instantiation,[status(thm)],[c_7911]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_27,plain,
% 31.51/4.50      ( ~ v1_funct_2(X0,X1,X2)
% 31.51/4.50      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 31.51/4.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.51/4.50      | ~ v2_funct_1(X0)
% 31.51/4.50      | ~ v1_funct_1(X0)
% 31.51/4.50      | k2_relset_1(X1,X2,X0) != X2 ),
% 31.51/4.50      inference(cnf_transformation,[],[f89]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_838,plain,
% 31.51/4.50      ( ~ v1_funct_2(X0_50,X0_51,X1_51)
% 31.51/4.50      | v1_funct_2(k2_funct_1(X0_50),X1_51,X0_51)
% 31.51/4.50      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 31.51/4.50      | ~ v2_funct_1(X0_50)
% 31.51/4.50      | ~ v1_funct_1(X0_50)
% 31.51/4.50      | k2_relset_1(X0_51,X1_51,X0_50) != X1_51 ),
% 31.51/4.50      inference(subtyping,[status(esa)],[c_27]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_1513,plain,
% 31.51/4.50      ( k2_relset_1(X0_51,X1_51,X0_50) != X1_51
% 31.51/4.50      | v1_funct_2(X0_50,X0_51,X1_51) != iProver_top
% 31.51/4.50      | v1_funct_2(k2_funct_1(X0_50),X1_51,X0_51) = iProver_top
% 31.51/4.50      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 31.51/4.50      | v2_funct_1(X0_50) != iProver_top
% 31.51/4.50      | v1_funct_1(X0_50) != iProver_top ),
% 31.51/4.50      inference(predicate_to_equality,[status(thm)],[c_838]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_3913,plain,
% 31.51/4.50      ( v1_funct_2(k2_funct_1(sK3),sK0,sK1) = iProver_top
% 31.51/4.50      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 31.51/4.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 31.51/4.50      | v2_funct_1(sK3) != iProver_top
% 31.51/4.50      | v1_funct_1(sK3) != iProver_top ),
% 31.51/4.50      inference(superposition,[status(thm)],[c_2060,c_1513]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_3742,plain,
% 31.51/4.50      ( k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2)
% 31.51/4.50      | k6_partfun1(k2_relat_1(k2_funct_1(sK2))) != k6_partfun1(k1_relat_1(sK2))
% 31.51/4.50      | k2_funct_1(k2_funct_1(sK2)) = sK2
% 31.51/4.50      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 31.51/4.50      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 31.51/4.50      | v1_relat_1(sK2) != iProver_top
% 31.51/4.50      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 31.51/4.50      | v1_funct_1(sK2) != iProver_top ),
% 31.51/4.50      inference(superposition,[status(thm)],[c_3552,c_1502]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_3211,plain,
% 31.51/4.50      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 31.51/4.50      | v1_relat_1(sK2) != iProver_top
% 31.51/4.50      | v1_funct_1(sK2) != iProver_top ),
% 31.51/4.50      inference(superposition,[status(thm)],[c_1518,c_1499]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_3213,plain,
% 31.51/4.50      ( k1_relat_1(k2_funct_1(sK2)) = sK1
% 31.51/4.50      | v1_relat_1(sK2) != iProver_top
% 31.51/4.50      | v1_funct_1(sK2) != iProver_top ),
% 31.51/4.50      inference(light_normalisation,[status(thm)],[c_3211,c_2360]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_3281,plain,
% 31.51/4.50      ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
% 31.51/4.50      inference(global_propositional_subsumption,
% 31.51/4.50                [status(thm)],
% 31.51/4.50                [c_3213,c_46,c_48,c_1686]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_3022,plain,
% 31.51/4.50      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 31.51/4.50      | v1_relat_1(sK2) != iProver_top
% 31.51/4.50      | v1_funct_1(sK2) != iProver_top ),
% 31.51/4.50      inference(superposition,[status(thm)],[c_1518,c_1498]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_911,plain,
% 31.51/4.50      ( ~ v2_funct_1(sK2)
% 31.51/4.50      | ~ v1_relat_1(sK2)
% 31.51/4.50      | ~ v1_funct_1(sK2)
% 31.51/4.50      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 31.51/4.50      inference(instantiation,[status(thm)],[c_853]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_3372,plain,
% 31.51/4.50      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 31.51/4.50      inference(global_propositional_subsumption,
% 31.51/4.50                [status(thm)],
% 31.51/4.50                [c_3022,c_45,c_43,c_37,c_911,c_1685]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_3743,plain,
% 31.51/4.50      ( sK1 != sK1
% 31.51/4.50      | k6_partfun1(k1_relat_1(sK2)) != k6_partfun1(k1_relat_1(sK2))
% 31.51/4.50      | k2_funct_1(k2_funct_1(sK2)) = sK2
% 31.51/4.50      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 31.51/4.50      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 31.51/4.50      | v1_relat_1(sK2) != iProver_top
% 31.51/4.50      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 31.51/4.50      | v1_funct_1(sK2) != iProver_top ),
% 31.51/4.50      inference(light_normalisation,
% 31.51/4.50                [status(thm)],
% 31.51/4.50                [c_3742,c_2360,c_3281,c_3372]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_3744,plain,
% 31.51/4.50      ( k2_funct_1(k2_funct_1(sK2)) = sK2
% 31.51/4.50      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 31.51/4.50      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 31.51/4.50      | v1_relat_1(sK2) != iProver_top
% 31.51/4.50      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 31.51/4.50      | v1_funct_1(sK2) != iProver_top ),
% 31.51/4.50      inference(equality_resolution_simp,[status(thm)],[c_3743]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_5,plain,
% 31.51/4.50      ( v2_funct_1(X0)
% 31.51/4.50      | ~ v2_funct_1(k5_relat_1(X0,X1))
% 31.51/4.50      | ~ v1_relat_1(X1)
% 31.51/4.50      | ~ v1_relat_1(X0)
% 31.51/4.50      | ~ v1_funct_1(X1)
% 31.51/4.50      | ~ v1_funct_1(X0)
% 31.51/4.50      | k1_relat_1(X1) != k2_relat_1(X0) ),
% 31.51/4.50      inference(cnf_transformation,[],[f65]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_854,plain,
% 31.51/4.50      ( v2_funct_1(X0_50)
% 31.51/4.50      | ~ v2_funct_1(k5_relat_1(X0_50,X1_50))
% 31.51/4.50      | ~ v1_relat_1(X0_50)
% 31.51/4.50      | ~ v1_relat_1(X1_50)
% 31.51/4.50      | ~ v1_funct_1(X0_50)
% 31.51/4.50      | ~ v1_funct_1(X1_50)
% 31.51/4.50      | k1_relat_1(X1_50) != k2_relat_1(X0_50) ),
% 31.51/4.50      inference(subtyping,[status(esa)],[c_5]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_1497,plain,
% 31.51/4.50      ( k1_relat_1(X0_50) != k2_relat_1(X1_50)
% 31.51/4.50      | v2_funct_1(X1_50) = iProver_top
% 31.51/4.50      | v2_funct_1(k5_relat_1(X1_50,X0_50)) != iProver_top
% 31.51/4.50      | v1_relat_1(X1_50) != iProver_top
% 31.51/4.50      | v1_relat_1(X0_50) != iProver_top
% 31.51/4.50      | v1_funct_1(X1_50) != iProver_top
% 31.51/4.50      | v1_funct_1(X0_50) != iProver_top ),
% 31.51/4.50      inference(predicate_to_equality,[status(thm)],[c_854]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_3376,plain,
% 31.51/4.50      ( k1_relat_1(X0_50) != k1_relat_1(sK2)
% 31.51/4.50      | v2_funct_1(k5_relat_1(k2_funct_1(sK2),X0_50)) != iProver_top
% 31.51/4.50      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 31.51/4.50      | v1_relat_1(X0_50) != iProver_top
% 31.51/4.50      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 31.51/4.50      | v1_funct_1(X0_50) != iProver_top
% 31.51/4.50      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 31.51/4.50      inference(superposition,[status(thm)],[c_3372,c_1497]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_3381,plain,
% 31.51/4.50      ( k1_relat_1(sK2) != k1_relat_1(sK2)
% 31.51/4.50      | v2_funct_1(k5_relat_1(k2_funct_1(sK2),sK2)) != iProver_top
% 31.51/4.50      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 31.51/4.50      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 31.51/4.50      | v1_relat_1(sK2) != iProver_top
% 31.51/4.50      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 31.51/4.50      | v1_funct_1(sK2) != iProver_top ),
% 31.51/4.50      inference(instantiation,[status(thm)],[c_3376]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_2975,plain,
% 31.51/4.50      ( v2_funct_1(k6_partfun1(sK1)) ),
% 31.51/4.50      inference(instantiation,[status(thm)],[c_857]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_2976,plain,
% 31.51/4.50      ( v2_funct_1(k6_partfun1(sK1)) = iProver_top ),
% 31.51/4.50      inference(predicate_to_equality,[status(thm)],[c_2975]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_2821,plain,
% 31.51/4.50      ( v1_funct_1(k2_funct_1(sK3)) | ~ v1_funct_1(sK3) ),
% 31.51/4.50      inference(predicate_to_equality_rev,[status(thm)],[c_2820]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_2104,plain,
% 31.51/4.50      ( ~ v2_funct_1(X0_50)
% 31.51/4.50      | v2_funct_1(k5_relat_1(k2_funct_1(X1_50),X2_50))
% 31.51/4.50      | k5_relat_1(k2_funct_1(X1_50),X2_50) != X0_50 ),
% 31.51/4.50      inference(instantiation,[status(thm)],[c_871]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_2481,plain,
% 31.51/4.50      ( v2_funct_1(k5_relat_1(k2_funct_1(sK2),sK2))
% 31.51/4.50      | ~ v2_funct_1(k6_partfun1(sK1))
% 31.51/4.50      | k5_relat_1(k2_funct_1(sK2),sK2) != k6_partfun1(sK1) ),
% 31.51/4.50      inference(instantiation,[status(thm)],[c_2104]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_2482,plain,
% 31.51/4.50      ( k5_relat_1(k2_funct_1(sK2),sK2) != k6_partfun1(sK1)
% 31.51/4.50      | v2_funct_1(k5_relat_1(k2_funct_1(sK2),sK2)) = iProver_top
% 31.51/4.50      | v2_funct_1(k6_partfun1(sK1)) != iProver_top ),
% 31.51/4.50      inference(predicate_to_equality,[status(thm)],[c_2481]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_2045,plain,
% 31.51/4.50      ( sK3 = sK3 ),
% 31.51/4.50      inference(instantiation,[status(thm)],[c_861]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_29,plain,
% 31.51/4.50      ( ~ v1_funct_2(X0,X1,X2)
% 31.51/4.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.51/4.50      | ~ v2_funct_1(X0)
% 31.51/4.50      | ~ v1_funct_1(X0)
% 31.51/4.50      | k2_relset_1(X1,X2,X0) != X2
% 31.51/4.50      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
% 31.51/4.50      | k1_xboole_0 = X2 ),
% 31.51/4.50      inference(cnf_transformation,[],[f92]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_837,plain,
% 31.51/4.50      ( ~ v1_funct_2(X0_50,X0_51,X1_51)
% 31.51/4.50      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 31.51/4.50      | ~ v2_funct_1(X0_50)
% 31.51/4.50      | ~ v1_funct_1(X0_50)
% 31.51/4.50      | k2_relset_1(X0_51,X1_51,X0_50) != X1_51
% 31.51/4.50      | k1_xboole_0 = X1_51
% 31.51/4.50      | k5_relat_1(k2_funct_1(X0_50),X0_50) = k6_partfun1(X1_51) ),
% 31.51/4.50      inference(subtyping,[status(esa)],[c_29]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_1588,plain,
% 31.51/4.50      ( ~ v1_funct_2(X0_50,X0_51,sK1)
% 31.51/4.50      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1)))
% 31.51/4.50      | ~ v2_funct_1(X0_50)
% 31.51/4.50      | ~ v1_funct_1(X0_50)
% 31.51/4.50      | k2_relset_1(X0_51,sK1,X0_50) != sK1
% 31.51/4.50      | k1_xboole_0 = sK1
% 31.51/4.50      | k5_relat_1(k2_funct_1(X0_50),X0_50) = k6_partfun1(sK1) ),
% 31.51/4.50      inference(instantiation,[status(thm)],[c_837]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_1654,plain,
% 31.51/4.50      ( ~ v1_funct_2(sK2,sK0,sK1)
% 31.51/4.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 31.51/4.50      | ~ v2_funct_1(sK2)
% 31.51/4.50      | ~ v1_funct_1(sK2)
% 31.51/4.50      | k2_relset_1(sK0,sK1,sK2) != sK1
% 31.51/4.50      | k1_xboole_0 = sK1
% 31.51/4.50      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
% 31.51/4.50      inference(instantiation,[status(thm)],[c_1588]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_34,negated_conjecture,
% 31.51/4.50      ( k2_funct_1(sK2) != sK3 ),
% 31.51/4.50      inference(cnf_transformation,[],[f107]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_833,negated_conjecture,
% 31.51/4.50      ( k2_funct_1(sK2) != sK3 ),
% 31.51/4.50      inference(subtyping,[status(esa)],[c_34]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_903,plain,
% 31.51/4.50      ( v1_relat_1(X0_50) != iProver_top
% 31.51/4.50      | v1_relat_1(k2_funct_1(X0_50)) = iProver_top
% 31.51/4.50      | v1_funct_1(X0_50) != iProver_top ),
% 31.51/4.50      inference(predicate_to_equality,[status(thm)],[c_858]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_905,plain,
% 31.51/4.50      ( v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 31.51/4.50      | v1_relat_1(sK2) != iProver_top
% 31.51/4.50      | v1_funct_1(sK2) != iProver_top ),
% 31.51/4.50      inference(instantiation,[status(thm)],[c_903]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_896,plain,
% 31.51/4.50      ( sK2 = sK2 ),
% 31.51/4.50      inference(instantiation,[status(thm)],[c_861]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_873,plain,
% 31.51/4.50      ( k1_relat_1(X0_50) = k1_relat_1(X1_50) | X0_50 != X1_50 ),
% 31.51/4.50      theory(equality) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_887,plain,
% 31.51/4.50      ( k1_relat_1(sK2) = k1_relat_1(sK2) | sK2 != sK2 ),
% 31.51/4.50      inference(instantiation,[status(thm)],[c_873]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(c_881,plain,
% 31.51/4.50      ( k2_funct_1(sK2) = k2_funct_1(sK2) | sK2 != sK2 ),
% 31.51/4.50      inference(instantiation,[status(thm)],[c_867]) ).
% 31.51/4.50  
% 31.51/4.50  cnf(contradiction,plain,
% 31.51/4.50      ( $false ),
% 31.51/4.50      inference(minisat,
% 31.51/4.50                [status(thm)],
% 31.51/4.50                [c_82192,c_72469,c_69903,c_33933,c_26694,c_22705,c_22168,
% 31.51/4.50                 c_22165,c_10319,c_9179,c_8997,c_8890,c_7920,c_7913,
% 31.51/4.50                 c_5090,c_5083,c_3913,c_3744,c_3381,c_2976,c_2821,c_2820,
% 31.51/4.50                 c_2482,c_2045,c_1995,c_1994,c_1686,c_1654,c_829,c_832,
% 31.51/4.50                 c_833,c_905,c_902,c_896,c_887,c_881,c_37,c_51,c_40,c_50,
% 31.51/4.50                 c_49,c_42,c_48,c_43,c_44,c_46,c_45]) ).
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  % SZS output end CNFRefutation for theBenchmark.p
% 31.51/4.50  
% 31.51/4.50  ------                               Statistics
% 31.51/4.50  
% 31.51/4.50  ------ General
% 31.51/4.50  
% 31.51/4.50  abstr_ref_over_cycles:                  0
% 31.51/4.50  abstr_ref_under_cycles:                 0
% 31.51/4.50  gc_basic_clause_elim:                   0
% 31.51/4.50  forced_gc_time:                         0
% 31.51/4.50  parsing_time:                           0.022
% 31.51/4.50  unif_index_cands_time:                  0.
% 31.51/4.50  unif_index_add_time:                    0.
% 31.51/4.50  orderings_time:                         0.
% 31.51/4.50  out_proof_time:                         0.035
% 31.51/4.50  total_time:                             3.572
% 31.51/4.50  num_of_symbols:                         57
% 31.51/4.50  num_of_terms:                           116410
% 31.51/4.50  
% 31.51/4.50  ------ Preprocessing
% 31.51/4.50  
% 31.51/4.50  num_of_splits:                          0
% 31.51/4.50  num_of_split_atoms:                     0
% 31.51/4.50  num_of_reused_defs:                     0
% 31.51/4.50  num_eq_ax_congr_red:                    2
% 31.51/4.50  num_of_sem_filtered_clauses:            1
% 31.51/4.50  num_of_subtypes:                        4
% 31.51/4.50  monotx_restored_types:                  1
% 31.51/4.50  sat_num_of_epr_types:                   0
% 31.51/4.50  sat_num_of_non_cyclic_types:            0
% 31.51/4.50  sat_guarded_non_collapsed_types:        1
% 31.51/4.50  num_pure_diseq_elim:                    0
% 31.51/4.50  simp_replaced_by:                       0
% 31.51/4.50  res_preprocessed:                       209
% 31.51/4.50  prep_upred:                             0
% 31.51/4.50  prep_unflattend:                        14
% 31.51/4.50  smt_new_axioms:                         0
% 31.51/4.50  pred_elim_cands:                        5
% 31.51/4.50  pred_elim:                              3
% 31.51/4.50  pred_elim_cl:                           4
% 31.51/4.50  pred_elim_cycles:                       5
% 31.51/4.50  merged_defs:                            0
% 31.51/4.50  merged_defs_ncl:                        0
% 31.51/4.50  bin_hyper_res:                          0
% 31.51/4.50  prep_cycles:                            4
% 31.51/4.50  pred_elim_time:                         0.005
% 31.51/4.50  splitting_time:                         0.
% 31.51/4.50  sem_filter_time:                        0.
% 31.51/4.50  monotx_time:                            0.001
% 31.51/4.50  subtype_inf_time:                       0.003
% 31.51/4.50  
% 31.51/4.50  ------ Problem properties
% 31.51/4.50  
% 31.51/4.50  clauses:                                41
% 31.51/4.50  conjectures:                            11
% 31.51/4.50  epr:                                    7
% 31.51/4.50  horn:                                   37
% 31.51/4.50  ground:                                 12
% 31.51/4.50  unary:                                  13
% 31.51/4.50  binary:                                 2
% 31.51/4.50  lits:                                   168
% 31.51/4.50  lits_eq:                                34
% 31.51/4.50  fd_pure:                                0
% 31.51/4.50  fd_pseudo:                              0
% 31.51/4.50  fd_cond:                                4
% 31.51/4.50  fd_pseudo_cond:                         1
% 31.51/4.50  ac_symbols:                             0
% 31.51/4.50  
% 31.51/4.50  ------ Propositional Solver
% 31.51/4.50  
% 31.51/4.50  prop_solver_calls:                      45
% 31.51/4.50  prop_fast_solver_calls:                 5120
% 31.51/4.50  smt_solver_calls:                       0
% 31.51/4.50  smt_fast_solver_calls:                  0
% 31.51/4.50  prop_num_of_clauses:                    37715
% 31.51/4.50  prop_preprocess_simplified:             68944
% 31.51/4.50  prop_fo_subsumed:                       1220
% 31.51/4.50  prop_solver_time:                       0.
% 31.51/4.50  smt_solver_time:                        0.
% 31.51/4.50  smt_fast_solver_time:                   0.
% 31.51/4.50  prop_fast_solver_time:                  0.
% 31.51/4.50  prop_unsat_core_time:                   0.007
% 31.51/4.50  
% 31.51/4.50  ------ QBF
% 31.51/4.50  
% 31.51/4.50  qbf_q_res:                              0
% 31.51/4.50  qbf_num_tautologies:                    0
% 31.51/4.50  qbf_prep_cycles:                        0
% 31.51/4.50  
% 31.51/4.50  ------ BMC1
% 31.51/4.50  
% 31.51/4.50  bmc1_current_bound:                     -1
% 31.51/4.50  bmc1_last_solved_bound:                 -1
% 31.51/4.50  bmc1_unsat_core_size:                   -1
% 31.51/4.50  bmc1_unsat_core_parents_size:           -1
% 31.51/4.50  bmc1_merge_next_fun:                    0
% 31.51/4.50  bmc1_unsat_core_clauses_time:           0.
% 31.51/4.50  
% 31.51/4.50  ------ Instantiation
% 31.51/4.50  
% 31.51/4.50  inst_num_of_clauses:                    2247
% 31.51/4.50  inst_num_in_passive:                    1069
% 31.51/4.50  inst_num_in_active:                     3630
% 31.51/4.50  inst_num_in_unprocessed:                247
% 31.51/4.50  inst_num_of_loops:                      3945
% 31.51/4.50  inst_num_of_learning_restarts:          1
% 31.51/4.50  inst_num_moves_active_passive:          305
% 31.51/4.50  inst_lit_activity:                      0
% 31.51/4.50  inst_lit_activity_moves:                1
% 31.51/4.50  inst_num_tautologies:                   0
% 31.51/4.50  inst_num_prop_implied:                  0
% 31.51/4.50  inst_num_existing_simplified:           0
% 31.51/4.50  inst_num_eq_res_simplified:             0
% 31.51/4.50  inst_num_child_elim:                    0
% 31.51/4.50  inst_num_of_dismatching_blockings:      6866
% 31.51/4.50  inst_num_of_non_proper_insts:           9498
% 31.51/4.50  inst_num_of_duplicates:                 0
% 31.51/4.50  inst_inst_num_from_inst_to_res:         0
% 31.51/4.50  inst_dismatching_checking_time:         0.
% 31.51/4.50  
% 31.51/4.50  ------ Resolution
% 31.51/4.50  
% 31.51/4.50  res_num_of_clauses:                     61
% 31.51/4.50  res_num_in_passive:                     61
% 31.51/4.50  res_num_in_active:                      0
% 31.51/4.50  res_num_of_loops:                       213
% 31.51/4.50  res_forward_subset_subsumed:            859
% 31.51/4.50  res_backward_subset_subsumed:           4
% 31.51/4.50  res_forward_subsumed:                   0
% 31.51/4.50  res_backward_subsumed:                  0
% 31.51/4.50  res_forward_subsumption_resolution:     1
% 31.51/4.50  res_backward_subsumption_resolution:    0
% 31.51/4.50  res_clause_to_clause_subsumption:       10281
% 31.51/4.50  res_orphan_elimination:                 0
% 31.51/4.50  res_tautology_del:                      662
% 31.51/4.50  res_num_eq_res_simplified:              1
% 31.51/4.50  res_num_sel_changes:                    0
% 31.51/4.50  res_moves_from_active_to_pass:          0
% 31.51/4.50  
% 31.51/4.50  ------ Superposition
% 31.51/4.50  
% 31.51/4.50  sup_time_total:                         0.
% 31.51/4.50  sup_time_generating:                    0.
% 31.51/4.50  sup_time_sim_full:                      0.
% 31.51/4.50  sup_time_sim_immed:                     0.
% 31.51/4.50  
% 31.51/4.50  sup_num_of_clauses:                     5749
% 31.51/4.50  sup_num_in_active:                      660
% 31.51/4.50  sup_num_in_passive:                     5089
% 31.51/4.50  sup_num_of_loops:                       788
% 31.51/4.50  sup_fw_superposition:                   2998
% 31.51/4.50  sup_bw_superposition:                   3548
% 31.51/4.50  sup_immediate_simplified:               1441
% 31.51/4.50  sup_given_eliminated:                   0
% 31.51/4.50  comparisons_done:                       0
% 31.51/4.50  comparisons_avoided:                    0
% 31.51/4.50  
% 31.51/4.50  ------ Simplifications
% 31.51/4.50  
% 31.51/4.50  
% 31.51/4.50  sim_fw_subset_subsumed:                 169
% 31.51/4.50  sim_bw_subset_subsumed:                 132
% 31.51/4.50  sim_fw_subsumed:                        73
% 31.51/4.50  sim_bw_subsumed:                        4
% 31.51/4.50  sim_fw_subsumption_res:                 0
% 31.51/4.50  sim_bw_subsumption_res:                 0
% 31.51/4.50  sim_tautology_del:                      2
% 31.51/4.50  sim_eq_tautology_del:                   192
% 31.51/4.50  sim_eq_res_simp:                        5
% 31.51/4.50  sim_fw_demodulated:                     38
% 31.51/4.50  sim_bw_demodulated:                     120
% 31.51/4.50  sim_light_normalised:                   1253
% 31.51/4.50  sim_joinable_taut:                      0
% 31.51/4.50  sim_joinable_simp:                      0
% 31.51/4.50  sim_ac_normalised:                      0
% 31.51/4.50  sim_smt_subsumption:                    0
% 31.51/4.50  
%------------------------------------------------------------------------------
