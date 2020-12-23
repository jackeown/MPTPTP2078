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
% DateTime   : Thu Dec  3 12:03:13 EST 2020

% Result     : Theorem 7.83s
% Output     : CNFRefutation 7.83s
% Verified   : 
% Statistics : Number of formulae       :  309 (6000 expanded)
%              Number of clauses        :  217 (1751 expanded)
%              Number of leaves         :   26 (1514 expanded)
%              Depth                    :   28
%              Number of atoms          : 1348 (52773 expanded)
%              Number of equality atoms :  631 (18303 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   24 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

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

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f57])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f21])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f56,f59,f58])).

fof(f102,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f60])).

fof(f13,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f82,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f95,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f60])).

fof(f97,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f60])).

fof(f98,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f60])).

fof(f100,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f60])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f43])).

fof(f81,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f44])).

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

fof(f47,plain,(
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

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f96,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f60])).

fof(f99,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f60])).

fof(f19,axiom,(
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

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f53])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f103,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f60])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f61,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f26,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f65,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f104,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f60])).

fof(f101,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f60])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

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

fof(f49,plain,(
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

fof(f50,plain,(
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
    inference(flattening,[],[f49])).

fof(f88,plain,(
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
    inference(cnf_transformation,[],[f50])).

fof(f105,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f60])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v2_funct_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1)
        & v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v2_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v2_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v2_funct_1(k5_relat_1(X0,X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f51])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f46,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f45])).

fof(f83,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_funct_1(X2))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ( k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f32,plain,(
    ! [X0] :
      ( ( k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f70,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
          & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f34,plain,(
    ! [X0] :
      ( ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f72,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
              & k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f15,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f84,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f107,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f74,f84])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f30,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f69,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f106,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_18,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_37,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_499,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_37])).

cnf(c_500,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_499])).

cnf(c_21,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_508,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_500,c_21])).

cnf(c_819,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_508])).

cnf(c_1551,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_819])).

cnf(c_44,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_42,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_41,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_39,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_844,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49)))
    | m1_subset_1(k1_partfun1(X2_49,X3_49,X0_49,X1_49,X1_48,X0_48),k1_zfmisc_1(k2_zfmisc_1(X2_49,X1_49)))
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(X1_48) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1629,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_844])).

cnf(c_1938,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1551,c_44,c_42,c_41,c_39,c_819,c_1629])).

cnf(c_23,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_512,plain,
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
    inference(resolution_lifted,[status(thm)],[c_23,c_37])).

cnf(c_513,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0
    | k6_partfun1(sK0) != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_512])).

cnf(c_605,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_513])).

cnf(c_818,plain,
    ( ~ v1_funct_2(X0_48,X0_49,sK0)
    | ~ v1_funct_2(X1_48,sK0,X0_49)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,sK0)))
    | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_49)))
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(X1_48)
    | k2_relset_1(X0_49,sK0,X0_48) = sK0
    | k1_partfun1(sK0,X0_49,X0_49,sK0,X1_48,X0_48) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_605])).

cnf(c_1552,plain,
    ( k2_relset_1(X0_49,sK0,X0_48) = sK0
    | k1_partfun1(sK0,X0_49,X0_49,sK0,X1_48,X0_48) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | v1_funct_2(X0_48,X0_49,sK0) != iProver_top
    | v1_funct_2(X1_48,sK0,X0_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,sK0))) != iProver_top
    | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_49))) != iProver_top
    | v1_funct_1(X1_48) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_818])).

cnf(c_1967,plain,
    ( k2_relset_1(X0_49,sK0,X0_48) = sK0
    | k1_partfun1(sK0,X0_49,X0_49,sK0,X1_48,X0_48) != k6_partfun1(sK0)
    | v1_funct_2(X0_48,X0_49,sK0) != iProver_top
    | v1_funct_2(X1_48,sK0,X0_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,sK0))) != iProver_top
    | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_49))) != iProver_top
    | v1_funct_1(X1_48) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1552,c_1938])).

cnf(c_1971,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1938,c_1967])).

cnf(c_43,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_40,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1637,plain,
    ( ~ v1_funct_2(X0_48,sK0,sK1)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(sK3)
    | k2_relset_1(sK1,sK0,sK3) = sK0
    | k1_partfun1(sK0,sK1,sK1,sK0,X0_48,sK3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_818])).

cnf(c_1639,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(sK1,sK0,sK3) = sK0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1637])).

cnf(c_861,plain,
    ( X0_48 = X0_48 ),
    theory(equality)).

cnf(c_1776,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_861])).

cnf(c_1974,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1971,c_44,c_43,c_42,c_41,c_40,c_39,c_1639,c_1776])).

cnf(c_32,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_833,plain,
    ( ~ v1_funct_2(X0_48,X0_49,X1_49)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ v2_funct_1(X0_48)
    | ~ v1_funct_1(X0_48)
    | k2_relset_1(X0_49,X1_49,X0_48) != X1_49
    | k1_xboole_0 = X1_49
    | k5_relat_1(X0_48,k2_funct_1(X0_48)) = k6_partfun1(X0_49) ),
    inference(subtyping,[status(esa)],[c_32])).

cnf(c_1541,plain,
    ( k2_relset_1(X0_49,X1_49,X0_48) != X1_49
    | k1_xboole_0 = X1_49
    | k5_relat_1(X0_48,k2_funct_1(X0_48)) = k6_partfun1(X0_49)
    | v1_funct_2(X0_48,X0_49,X1_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v2_funct_1(X0_48) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_833])).

cnf(c_4889,plain,
    ( sK0 = k1_xboole_0
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1974,c_1541])).

cnf(c_45,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_46,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_47,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_48,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_49,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_50,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_36,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_52,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_862,plain,
    ( X0_49 = X0_49 ),
    theory(equality)).

cnf(c_897,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_862])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_859,plain,
    ( ~ v1_relat_1(X0_48)
    | ~ v1_funct_1(X0_48)
    | v1_funct_1(k2_funct_1(X0_48)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_900,plain,
    ( v1_relat_1(X0_48) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(k2_funct_1(X0_48)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_859])).

cnf(c_902,plain,
    ( v1_relat_1(sK2) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_900])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_858,plain,
    ( ~ v1_relat_1(X0_48)
    | v1_relat_1(k2_funct_1(X0_48))
    | ~ v1_funct_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_903,plain,
    ( v1_relat_1(X0_48) != iProver_top
    | v1_relat_1(k2_funct_1(X0_48)) = iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_858])).

cnf(c_905,plain,
    ( v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_903])).

cnf(c_2,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_857,plain,
    ( ~ v2_funct_1(X0_48)
    | v2_funct_1(k2_funct_1(X0_48))
    | ~ v1_relat_1(X0_48)
    | ~ v1_funct_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_906,plain,
    ( v2_funct_1(X0_48) != iProver_top
    | v2_funct_1(k2_funct_1(X0_48)) = iProver_top
    | v1_relat_1(X0_48) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_857])).

cnf(c_908,plain,
    ( v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_906])).

cnf(c_35,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_830,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(subtyping,[status(esa)],[c_35])).

cnf(c_38,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_828,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(subtyping,[status(esa)],[c_38])).

cnf(c_866,plain,
    ( X0_49 != X1_49
    | X2_49 != X1_49
    | X2_49 = X0_49 ),
    theory(equality)).

cnf(c_1610,plain,
    ( sK0 != X0_49
    | k1_xboole_0 != X0_49
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_866])).

cnf(c_1611,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1610])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_846,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | v1_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1652,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_846])).

cnf(c_1713,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1652])).

cnf(c_1714,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1713])).

cnf(c_25,plain,
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
    inference(cnf_transformation,[],[f88])).

cnf(c_839,plain,
    ( ~ v1_funct_2(X0_48,X0_49,X1_49)
    | ~ v1_funct_2(X1_48,X2_49,X0_49)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X0_49)))
    | v2_funct_1(X0_48)
    | ~ v2_funct_1(k1_partfun1(X2_49,X0_49,X0_49,X1_49,X1_48,X0_48))
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(X1_48)
    | k2_relset_1(X2_49,X0_49,X1_48) != X0_49
    | k1_xboole_0 = X1_49 ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1750,plain,
    ( ~ v1_funct_2(X0_48,X0_49,X1_49)
    | ~ v1_funct_2(sK3,X1_49,X2_49)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)))
    | ~ v2_funct_1(k1_partfun1(X0_49,X1_49,X1_49,X2_49,X0_48,sK3))
    | v2_funct_1(sK3)
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(sK3)
    | k2_relset_1(X0_49,X1_49,X0_48) != X1_49
    | k1_xboole_0 = X2_49 ),
    inference(instantiation,[status(thm)],[c_839])).

cnf(c_1836,plain,
    ( ~ v1_funct_2(X0_48,X0_49,X1_49)
    | ~ v1_funct_2(sK3,X1_49,sK0)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1_49,sK0)))
    | ~ v2_funct_1(k1_partfun1(X0_49,X1_49,X1_49,sK0,X0_48,sK3))
    | v2_funct_1(sK3)
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(sK3)
    | k2_relset_1(X0_49,X1_49,X0_48) != X1_49
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1750])).

cnf(c_1940,plain,
    ( ~ v1_funct_2(X0_48,X0_49,sK1)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v2_funct_1(k1_partfun1(X0_49,sK1,sK1,sK0,X0_48,sK3))
    | v2_funct_1(sK3)
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(sK3)
    | k2_relset_1(X0_49,sK1,X0_48) != sK1
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1836])).

cnf(c_2166,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(sK0,sK1,sK2) != sK1
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1940])).

cnf(c_2167,plain,
    ( k2_relset_1(sK0,sK1,sK2) != sK1
    | k1_xboole_0 = sK0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2166])).

cnf(c_865,plain,
    ( X0_48 != X1_48
    | X2_48 != X1_48
    | X2_48 = X0_48 ),
    theory(equality)).

cnf(c_1794,plain,
    ( X0_48 != X1_48
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X1_48
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = X0_48 ),
    inference(instantiation,[status(thm)],[c_865])).

cnf(c_2023,plain,
    ( X0_48 != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = X0_48
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1794])).

cnf(c_2239,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | k6_partfun1(sK0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_2023])).

cnf(c_870,plain,
    ( ~ v2_funct_1(X0_48)
    | v2_funct_1(X1_48)
    | X1_48 != X0_48 ),
    theory(equality)).

cnf(c_2450,plain,
    ( ~ v2_funct_1(X0_48)
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0_48 ),
    inference(instantiation,[status(thm)],[c_870])).

cnf(c_3135,plain,
    ( v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | ~ v2_funct_1(k6_partfun1(sK0))
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != k6_partfun1(sK0) ),
    inference(instantiation,[status(thm)],[c_2450])).

cnf(c_3136,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != k6_partfun1(sK0)
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) = iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3135])).

cnf(c_4888,plain,
    ( sK1 = k1_xboole_0
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_828,c_1541])).

cnf(c_34,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f105])).

cnf(c_831,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(subtyping,[status(esa)],[c_34])).

cnf(c_1612,plain,
    ( ~ v1_funct_2(X0_48,X0_49,sK1)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,sK1)))
    | ~ v2_funct_1(X0_48)
    | ~ v1_funct_1(X0_48)
    | k2_relset_1(X0_49,sK1,X0_48) != sK1
    | k1_xboole_0 = sK1
    | k5_relat_1(X0_48,k2_funct_1(X0_48)) = k6_partfun1(X0_49) ),
    inference(instantiation,[status(thm)],[c_833])).

cnf(c_1704,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(sK0,sK1,sK2) != sK1
    | k1_xboole_0 = sK1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
    inference(instantiation,[status(thm)],[c_1612])).

cnf(c_4895,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4888,c_44,c_43,c_42,c_36,c_831,c_828,c_1704])).

cnf(c_5,plain,
    ( ~ v2_funct_1(X0)
    | ~ v2_funct_1(X1)
    | v2_funct_1(k5_relat_1(X0,X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_856,plain,
    ( ~ v2_funct_1(X0_48)
    | ~ v2_funct_1(X1_48)
    | v2_funct_1(k5_relat_1(X0_48,X1_48))
    | ~ v1_relat_1(X0_48)
    | ~ v1_relat_1(X1_48)
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(X1_48) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1518,plain,
    ( v2_funct_1(X0_48) != iProver_top
    | v2_funct_1(X1_48) != iProver_top
    | v2_funct_1(k5_relat_1(X1_48,X0_48)) = iProver_top
    | v1_relat_1(X1_48) != iProver_top
    | v1_relat_1(X0_48) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(X1_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_856])).

cnf(c_4901,plain,
    ( v2_funct_1(k6_partfun1(sK0)) = iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4895,c_1518])).

cnf(c_15509,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4889,c_44,c_45,c_46,c_42,c_47,c_41,c_48,c_49,c_39,c_50,c_52,c_897,c_902,c_905,c_908,c_830,c_828,c_819,c_1611,c_1629,c_1714,c_1776,c_2167,c_2239,c_3136,c_4901])).

cnf(c_827,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subtyping,[status(esa)],[c_39])).

cnf(c_1543,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_827])).

cnf(c_28,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_836,plain,
    ( ~ v1_funct_2(X0_48,X0_49,X1_49)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | m1_subset_1(k2_funct_1(X0_48),k1_zfmisc_1(k2_zfmisc_1(X1_49,X0_49)))
    | ~ v2_funct_1(X0_48)
    | ~ v1_funct_1(X0_48)
    | k2_relset_1(X0_49,X1_49,X0_48) != X1_49 ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_1538,plain,
    ( k2_relset_1(X0_49,X1_49,X0_48) != X1_49
    | v1_funct_2(X0_48,X0_49,X1_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | m1_subset_1(k2_funct_1(X0_48),k1_zfmisc_1(k2_zfmisc_1(X1_49,X0_49))) = iProver_top
    | v2_funct_1(X0_48) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_836])).

cnf(c_4359,plain,
    ( v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1974,c_1538])).

cnf(c_9317,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4359,c_44,c_45,c_46,c_42,c_47,c_41,c_48,c_49,c_39,c_50,c_52,c_902,c_905,c_908,c_830,c_828,c_819,c_1629,c_1714,c_1776,c_2167,c_2239,c_3136,c_4901])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_841,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49)))
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(X1_48)
    | k1_partfun1(X2_49,X3_49,X0_49,X1_49,X1_48,X0_48) = k5_relat_1(X1_48,X0_48) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1533,plain,
    ( k1_partfun1(X0_49,X1_49,X2_49,X3_49,X0_48,X1_48) = k5_relat_1(X0_48,X1_48)
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(X1_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_841])).

cnf(c_9328,plain,
    ( k1_partfun1(X0_49,X1_49,sK0,sK1,X0_48,k2_funct_1(sK3)) = k5_relat_1(X0_48,k2_funct_1(sK3))
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9317,c_1533])).

cnf(c_30,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_241,plain,
    ( v1_funct_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_30,c_15,c_0])).

cnf(c_242,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0)) ),
    inference(renaming,[status(thm)],[c_241])).

cnf(c_821,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ v1_funct_1(X0_48)
    | v1_funct_1(k2_funct_1(X0_48)) ),
    inference(subtyping,[status(esa)],[c_242])).

cnf(c_1549,plain,
    ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(k2_funct_1(X0_48)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_821])).

cnf(c_2600,plain,
    ( v1_funct_1(k2_funct_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1543,c_1549])).

cnf(c_10327,plain,
    ( v1_funct_1(X0_48) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | k1_partfun1(X0_49,X1_49,sK0,sK1,X0_48,k2_funct_1(sK3)) = k5_relat_1(X0_48,k2_funct_1(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9328,c_48,c_2600])).

cnf(c_10328,plain,
    ( k1_partfun1(X0_49,X1_49,sK0,sK1,X0_48,k2_funct_1(sK3)) = k5_relat_1(X0_48,k2_funct_1(sK3))
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(renaming,[status(thm)],[c_10327])).

cnf(c_10333,plain,
    ( k1_partfun1(sK1,sK0,sK0,sK1,sK3,k2_funct_1(sK3)) = k5_relat_1(sK3,k2_funct_1(sK3))
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1543,c_10328])).

cnf(c_10358,plain,
    ( k1_partfun1(sK1,sK0,sK0,sK1,sK3,k2_funct_1(sK3)) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10333,c_48])).

cnf(c_15512,plain,
    ( k1_partfun1(sK1,sK0,sK0,sK1,sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    inference(demodulation,[status(thm)],[c_15509,c_10358])).

cnf(c_824,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_42])).

cnf(c_1546,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_824])).

cnf(c_3642,plain,
    ( k1_partfun1(X0_49,X1_49,sK0,sK1,X0_48,sK2) = k5_relat_1(X0_48,sK2)
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1546,c_1533])).

cnf(c_4082,plain,
    ( v1_funct_1(X0_48) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | k1_partfun1(X0_49,X1_49,sK0,sK1,X0_48,sK2) = k5_relat_1(X0_48,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3642,c_45])).

cnf(c_4083,plain,
    ( k1_partfun1(X0_49,X1_49,sK0,sK1,X0_48,sK2) = k5_relat_1(X0_48,sK2)
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(renaming,[status(thm)],[c_4082])).

cnf(c_4086,plain,
    ( k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) = k5_relat_1(sK3,sK2)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1543,c_4083])).

cnf(c_4095,plain,
    ( k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) = k5_relat_1(sK3,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4086,c_48])).

cnf(c_1535,plain,
    ( k2_relset_1(X0_49,X1_49,X0_48) != X1_49
    | k1_xboole_0 = X2_49
    | v1_funct_2(X1_48,X1_49,X2_49) != iProver_top
    | v1_funct_2(X0_48,X0_49,X1_49) != iProver_top
    | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49))) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v2_funct_1(X1_48) = iProver_top
    | v2_funct_1(k1_partfun1(X0_49,X1_49,X1_49,X2_49,X0_48,X1_48)) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(X1_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_839])).

cnf(c_4963,plain,
    ( k1_xboole_0 = X0_49
    | v1_funct_2(X0_48,sK1,X0_49) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(sK1,X0_49))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v2_funct_1(X0_48) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0_49,sK2,X0_48)) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_828,c_1535])).

cnf(c_5087,plain,
    ( v1_funct_1(X0_48) != iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0_49,sK2,X0_48)) != iProver_top
    | v2_funct_1(X0_48) = iProver_top
    | v1_funct_2(X0_48,sK1,X0_49) != iProver_top
    | k1_xboole_0 = X0_49
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(sK1,X0_49))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4963,c_45,c_46,c_47])).

cnf(c_5088,plain,
    ( k1_xboole_0 = X0_49
    | v1_funct_2(X0_48,sK1,X0_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(sK1,X0_49))) != iProver_top
    | v2_funct_1(X0_48) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0_49,sK2,X0_48)) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(renaming,[status(thm)],[c_5087])).

cnf(c_5091,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1938,c_5088])).

cnf(c_5420,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5091,c_44,c_45,c_46,c_42,c_47,c_41,c_48,c_49,c_39,c_50,c_52,c_902,c_905,c_908,c_830,c_828,c_819,c_1629,c_1714,c_1776,c_2167,c_2239,c_3136,c_4901])).

cnf(c_10,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_851,plain,
    ( ~ v2_funct_1(X0_48)
    | ~ v1_relat_1(X0_48)
    | ~ v1_funct_1(X0_48)
    | k1_relat_1(k5_relat_1(X0_48,k2_funct_1(X0_48))) = k1_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1523,plain,
    ( k1_relat_1(k5_relat_1(X0_48,k2_funct_1(X0_48))) = k1_relat_1(X0_48)
    | v2_funct_1(X0_48) != iProver_top
    | v1_relat_1(X0_48) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_851])).

cnf(c_5428,plain,
    ( k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) = k1_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5420,c_1523])).

cnf(c_1851,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_846])).

cnf(c_1949,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1851])).

cnf(c_1950,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1949])).

cnf(c_5647,plain,
    ( k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5428,c_48,c_50,c_1950])).

cnf(c_15514,plain,
    ( k1_relat_1(k6_partfun1(sK1)) = k1_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_15509,c_5647])).

cnf(c_31,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_834,plain,
    ( ~ v1_funct_2(X0_48,X0_49,X1_49)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ v2_funct_1(X0_48)
    | ~ v1_funct_1(X0_48)
    | k2_relset_1(X0_49,X1_49,X0_48) != X1_49
    | k1_xboole_0 = X1_49
    | k5_relat_1(k2_funct_1(X0_48),X0_48) = k6_partfun1(X1_49) ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_1540,plain,
    ( k2_relset_1(X0_49,X1_49,X0_48) != X1_49
    | k1_xboole_0 = X1_49
    | k5_relat_1(k2_funct_1(X0_48),X0_48) = k6_partfun1(X1_49)
    | v1_funct_2(X0_48,X0_49,X1_49) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v2_funct_1(X0_48) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_834])).

cnf(c_4468,plain,
    ( sK1 = k1_xboole_0
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_828,c_1540])).

cnf(c_1613,plain,
    ( ~ v1_funct_2(X0_48,X0_49,sK1)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,sK1)))
    | ~ v2_funct_1(X0_48)
    | ~ v1_funct_1(X0_48)
    | k2_relset_1(X0_49,sK1,X0_48) != sK1
    | k1_xboole_0 = sK1
    | k5_relat_1(k2_funct_1(X0_48),X0_48) = k6_partfun1(sK1) ),
    inference(instantiation,[status(thm)],[c_834])).

cnf(c_1682,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(sK0,sK1,sK2) != sK1
    | k1_xboole_0 = sK1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(instantiation,[status(thm)],[c_1613])).

cnf(c_4475,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4468,c_44,c_43,c_42,c_36,c_831,c_828,c_1682])).

cnf(c_829,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_36])).

cnf(c_1542,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_829])).

cnf(c_12,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_849,plain,
    ( ~ v2_funct_1(X0_48)
    | ~ v1_relat_1(X0_48)
    | ~ v1_funct_1(X0_48)
    | k1_relat_1(k5_relat_1(k2_funct_1(X0_48),X0_48)) = k2_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1525,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1(X0_48),X0_48)) = k2_relat_1(X0_48)
    | v2_funct_1(X0_48) != iProver_top
    | v1_relat_1(X0_48) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_849])).

cnf(c_3351,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1(sK2),sK2)) = k2_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1542,c_1525])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_845,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | k2_relset_1(X0_49,X1_49,X0_48) = k2_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1529,plain,
    ( k2_relset_1(X0_49,X1_49,X0_48) = k2_relat_1(X0_48)
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_845])).

cnf(c_2280,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1546,c_1529])).

cnf(c_2282,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2280,c_828])).

cnf(c_3354,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1(sK2),sK2)) = sK1
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3351,c_2282])).

cnf(c_3429,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1(sK2),sK2)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3354,c_45,c_47,c_1714])).

cnf(c_4477,plain,
    ( k1_relat_1(k6_partfun1(sK1)) = sK1 ),
    inference(demodulation,[status(thm)],[c_4475,c_3429])).

cnf(c_15515,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_15514,c_4477])).

cnf(c_3641,plain,
    ( k1_partfun1(X0_49,X1_49,sK1,sK0,X0_48,sK3) = k5_relat_1(X0_48,sK3)
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1543,c_1533])).

cnf(c_3891,plain,
    ( v1_funct_1(X0_48) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | k1_partfun1(X0_49,X1_49,sK1,sK0,X0_48,sK3) = k5_relat_1(X0_48,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3641,c_48])).

cnf(c_3892,plain,
    ( k1_partfun1(X0_49,X1_49,sK1,sK0,X0_48,sK3) = k5_relat_1(X0_48,sK3)
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(renaming,[status(thm)],[c_3891])).

cnf(c_3898,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1546,c_3892])).

cnf(c_3900,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3898,c_1938])).

cnf(c_4188,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3900,c_45])).

cnf(c_13,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
    | k1_relat_1(X0) != k2_relat_1(X1)
    | k2_funct_1(X0) = X1 ),
    inference(cnf_transformation,[],[f107])).

cnf(c_848,plain,
    ( ~ v2_funct_1(X0_48)
    | ~ v1_relat_1(X0_48)
    | ~ v1_relat_1(X1_48)
    | ~ v1_funct_1(X0_48)
    | ~ v1_funct_1(X1_48)
    | k1_relat_1(X0_48) != k2_relat_1(X1_48)
    | k5_relat_1(X1_48,X0_48) != k6_partfun1(k2_relat_1(X0_48))
    | k2_funct_1(X0_48) = X1_48 ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1526,plain,
    ( k1_relat_1(X0_48) != k2_relat_1(X1_48)
    | k5_relat_1(X1_48,X0_48) != k6_partfun1(k2_relat_1(X0_48))
    | k2_funct_1(X0_48) = X1_48
    | v2_funct_1(X0_48) != iProver_top
    | v1_relat_1(X0_48) != iProver_top
    | v1_relat_1(X1_48) != iProver_top
    | v1_funct_1(X1_48) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_848])).

cnf(c_4274,plain,
    ( k1_relat_1(sK3) != k2_relat_1(sK2)
    | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
    | k2_funct_1(sK3) = sK2
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4188,c_1526])).

cnf(c_2279,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1543,c_1529])).

cnf(c_2283,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_2279,c_1974])).

cnf(c_4275,plain,
    ( k1_relat_1(sK3) != sK1
    | k6_partfun1(sK0) != k6_partfun1(sK0)
    | k2_funct_1(sK3) = sK2
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4274,c_2282,c_2283])).

cnf(c_4276,plain,
    ( k1_relat_1(sK3) != sK1
    | k2_funct_1(sK3) = sK2
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4275])).

cnf(c_901,plain,
    ( ~ v1_relat_1(sK2)
    | v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_859])).

cnf(c_904,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_858])).

cnf(c_907,plain,
    ( v2_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_857])).

cnf(c_4277,plain,
    ( ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k1_relat_1(sK3) != sK1
    | k2_funct_1(sK3) = sK2 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4276])).

cnf(c_4902,plain,
    ( v2_funct_1(k6_partfun1(sK0))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4901])).

cnf(c_9717,plain,
    ( k2_funct_1(sK3) = sK2
    | k1_relat_1(sK3) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4276,c_44,c_43,c_42,c_41,c_40,c_39,c_36,c_901,c_904,c_907,c_830,c_828,c_819,c_1629,c_1713,c_1776,c_1949,c_2166,c_2239,c_3135,c_4277,c_4902])).

cnf(c_9718,plain,
    ( k1_relat_1(sK3) != sK1
    | k2_funct_1(sK3) = sK2 ),
    inference(renaming,[status(thm)],[c_9717])).

cnf(c_15570,plain,
    ( sK1 != sK1
    | k2_funct_1(sK3) = sK2 ),
    inference(demodulation,[status(thm)],[c_15515,c_9718])).

cnf(c_15572,plain,
    ( k2_funct_1(sK3) = sK2 ),
    inference(equality_resolution_simp,[status(thm)],[c_15570])).

cnf(c_15574,plain,
    ( k5_relat_1(sK3,sK2) = k6_partfun1(sK1) ),
    inference(light_normalisation,[status(thm)],[c_15512,c_4095,c_15512,c_15572])).

cnf(c_15611,plain,
    ( k1_relat_1(sK2) != k2_relat_1(sK3)
    | k6_partfun1(k2_relat_1(sK2)) != k6_partfun1(sK1)
    | k2_funct_1(sK2) = sK3
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_15574,c_1526])).

cnf(c_15614,plain,
    ( k1_relat_1(sK2) != sK0
    | k6_partfun1(sK1) != k6_partfun1(sK1)
    | k2_funct_1(sK2) = sK3
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_15611,c_2282,c_2283])).

cnf(c_15615,plain,
    ( k1_relat_1(sK2) != sK0
    | k2_funct_1(sK2) = sK3
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_15614])).

cnf(c_4358,plain,
    ( v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_828,c_1538])).

cnf(c_2161,plain,
    ( ~ v1_funct_2(X0_48,sK0,sK1)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | m1_subset_1(k2_funct_1(X0_48),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v2_funct_1(X0_48)
    | ~ v1_funct_1(X0_48)
    | k2_relset_1(sK0,sK1,X0_48) != sK1 ),
    inference(instantiation,[status(thm)],[c_836])).

cnf(c_2162,plain,
    ( k2_relset_1(sK0,sK1,X0_48) != sK1
    | v1_funct_2(X0_48,sK0,sK1) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(k2_funct_1(X0_48),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
    | v2_funct_1(X0_48) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2161])).

cnf(c_2164,plain,
    ( k2_relset_1(sK0,sK1,sK2) != sK1
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2162])).

cnf(c_4367,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4358,c_45,c_46,c_47,c_52,c_828,c_2164])).

cnf(c_4376,plain,
    ( k1_partfun1(X0_49,X1_49,sK1,sK0,X0_48,k2_funct_1(sK2)) = k5_relat_1(X0_48,k2_funct_1(sK2))
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4367,c_1533])).

cnf(c_4682,plain,
    ( v1_funct_1(X0_48) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | k1_partfun1(X0_49,X1_49,sK1,sK0,X0_48,k2_funct_1(sK2)) = k5_relat_1(X0_48,k2_funct_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4376,c_45,c_47,c_902,c_1714])).

cnf(c_4683,plain,
    ( k1_partfun1(X0_49,X1_49,sK1,sK0,X0_48,k2_funct_1(sK2)) = k5_relat_1(X0_48,k2_funct_1(sK2))
    | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(renaming,[status(thm)],[c_4682])).

cnf(c_4689,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2))
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1546,c_4683])).

cnf(c_5158,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4689,c_45])).

cnf(c_5160,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
    inference(light_normalisation,[status(thm)],[c_5158,c_4895])).

cnf(c_5161,plain,
    ( k2_relset_1(sK1,sK0,k2_funct_1(sK2)) = sK0
    | v1_funct_2(k2_funct_1(sK2),sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5160,c_1967])).

cnf(c_4374,plain,
    ( k2_relset_1(sK1,sK0,k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_4367,c_1529])).

cnf(c_7,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_854,plain,
    ( ~ v2_funct_1(X0_48)
    | ~ v1_relat_1(X0_48)
    | ~ v1_funct_1(X0_48)
    | k2_relat_1(k2_funct_1(X0_48)) = k1_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1520,plain,
    ( k2_relat_1(k2_funct_1(X0_48)) = k1_relat_1(X0_48)
    | v2_funct_1(X0_48) != iProver_top
    | v1_relat_1(X0_48) != iProver_top
    | v1_funct_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_854])).

cnf(c_2345,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1542,c_1520])).

cnf(c_916,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_854])).

cnf(c_2468,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2345,c_44,c_42,c_36,c_916,c_1713])).

cnf(c_4377,plain,
    ( k2_relset_1(sK1,sK0,k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_4374,c_2468])).

cnf(c_5165,plain,
    ( k1_relat_1(sK2) = sK0
    | v1_funct_2(k2_funct_1(sK2),sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5161,c_4377])).

cnf(c_29,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_835,plain,
    ( ~ v1_funct_2(X0_48,X0_49,X1_49)
    | v1_funct_2(k2_funct_1(X0_48),X1_49,X0_49)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
    | ~ v2_funct_1(X0_48)
    | ~ v1_funct_1(X0_48)
    | k2_relset_1(X0_49,X1_49,X0_48) != X1_49 ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_1796,plain,
    ( ~ v1_funct_2(X0_48,sK0,X0_49)
    | v1_funct_2(k2_funct_1(X0_48),X0_49,sK0)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_49)))
    | ~ v2_funct_1(X0_48)
    | ~ v1_funct_1(X0_48)
    | k2_relset_1(sK0,X0_49,X0_48) != X0_49 ),
    inference(instantiation,[status(thm)],[c_835])).

cnf(c_2041,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(sK0,sK1,sK2) != sK1 ),
    inference(instantiation,[status(thm)],[c_1796])).

cnf(c_2042,plain,
    ( k2_relset_1(sK0,sK1,sK2) != sK1
    | v1_funct_2(k2_funct_1(sK2),sK1,sK0) = iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2041])).

cnf(c_33,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f106])).

cnf(c_832,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(subtyping,[status(esa)],[c_33])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_15615,c_5165,c_2164,c_2042,c_1950,c_1714,c_828,c_832,c_902,c_52,c_50,c_48,c_47,c_46,c_45])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:03:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.83/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.83/1.49  
% 7.83/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.83/1.49  
% 7.83/1.49  ------  iProver source info
% 7.83/1.49  
% 7.83/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.83/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.83/1.49  git: non_committed_changes: false
% 7.83/1.49  git: last_make_outside_of_git: false
% 7.83/1.49  
% 7.83/1.49  ------ 
% 7.83/1.49  
% 7.83/1.49  ------ Input Options
% 7.83/1.49  
% 7.83/1.49  --out_options                           all
% 7.83/1.49  --tptp_safe_out                         true
% 7.83/1.49  --problem_path                          ""
% 7.83/1.49  --include_path                          ""
% 7.83/1.49  --clausifier                            res/vclausify_rel
% 7.83/1.49  --clausifier_options                    ""
% 7.83/1.49  --stdin                                 false
% 7.83/1.49  --stats_out                             all
% 7.83/1.49  
% 7.83/1.49  ------ General Options
% 7.83/1.49  
% 7.83/1.49  --fof                                   false
% 7.83/1.49  --time_out_real                         305.
% 7.83/1.49  --time_out_virtual                      -1.
% 7.83/1.49  --symbol_type_check                     false
% 7.83/1.49  --clausify_out                          false
% 7.83/1.49  --sig_cnt_out                           false
% 7.83/1.49  --trig_cnt_out                          false
% 7.83/1.49  --trig_cnt_out_tolerance                1.
% 7.83/1.49  --trig_cnt_out_sk_spl                   false
% 7.83/1.49  --abstr_cl_out                          false
% 7.83/1.49  
% 7.83/1.49  ------ Global Options
% 7.83/1.49  
% 7.83/1.49  --schedule                              default
% 7.83/1.49  --add_important_lit                     false
% 7.83/1.49  --prop_solver_per_cl                    1000
% 7.83/1.49  --min_unsat_core                        false
% 7.83/1.49  --soft_assumptions                      false
% 7.83/1.49  --soft_lemma_size                       3
% 7.83/1.49  --prop_impl_unit_size                   0
% 7.83/1.49  --prop_impl_unit                        []
% 7.83/1.49  --share_sel_clauses                     true
% 7.83/1.49  --reset_solvers                         false
% 7.83/1.49  --bc_imp_inh                            [conj_cone]
% 7.83/1.49  --conj_cone_tolerance                   3.
% 7.83/1.49  --extra_neg_conj                        none
% 7.83/1.49  --large_theory_mode                     true
% 7.83/1.49  --prolific_symb_bound                   200
% 7.83/1.49  --lt_threshold                          2000
% 7.83/1.49  --clause_weak_htbl                      true
% 7.83/1.49  --gc_record_bc_elim                     false
% 7.83/1.49  
% 7.83/1.49  ------ Preprocessing Options
% 7.83/1.49  
% 7.83/1.49  --preprocessing_flag                    true
% 7.83/1.49  --time_out_prep_mult                    0.1
% 7.83/1.49  --splitting_mode                        input
% 7.83/1.49  --splitting_grd                         true
% 7.83/1.49  --splitting_cvd                         false
% 7.83/1.49  --splitting_cvd_svl                     false
% 7.83/1.49  --splitting_nvd                         32
% 7.83/1.49  --sub_typing                            true
% 7.83/1.49  --prep_gs_sim                           true
% 7.83/1.49  --prep_unflatten                        true
% 7.83/1.49  --prep_res_sim                          true
% 7.83/1.49  --prep_upred                            true
% 7.83/1.49  --prep_sem_filter                       exhaustive
% 7.83/1.49  --prep_sem_filter_out                   false
% 7.83/1.49  --pred_elim                             true
% 7.83/1.49  --res_sim_input                         true
% 7.83/1.49  --eq_ax_congr_red                       true
% 7.83/1.49  --pure_diseq_elim                       true
% 7.83/1.49  --brand_transform                       false
% 7.83/1.49  --non_eq_to_eq                          false
% 7.83/1.49  --prep_def_merge                        true
% 7.83/1.49  --prep_def_merge_prop_impl              false
% 7.83/1.49  --prep_def_merge_mbd                    true
% 7.83/1.49  --prep_def_merge_tr_red                 false
% 7.83/1.49  --prep_def_merge_tr_cl                  false
% 7.83/1.49  --smt_preprocessing                     true
% 7.83/1.49  --smt_ac_axioms                         fast
% 7.83/1.49  --preprocessed_out                      false
% 7.83/1.49  --preprocessed_stats                    false
% 7.83/1.49  
% 7.83/1.49  ------ Abstraction refinement Options
% 7.83/1.49  
% 7.83/1.49  --abstr_ref                             []
% 7.83/1.49  --abstr_ref_prep                        false
% 7.83/1.49  --abstr_ref_until_sat                   false
% 7.83/1.49  --abstr_ref_sig_restrict                funpre
% 7.83/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.83/1.49  --abstr_ref_under                       []
% 7.83/1.49  
% 7.83/1.49  ------ SAT Options
% 7.83/1.49  
% 7.83/1.49  --sat_mode                              false
% 7.83/1.49  --sat_fm_restart_options                ""
% 7.83/1.49  --sat_gr_def                            false
% 7.83/1.49  --sat_epr_types                         true
% 7.83/1.49  --sat_non_cyclic_types                  false
% 7.83/1.49  --sat_finite_models                     false
% 7.83/1.49  --sat_fm_lemmas                         false
% 7.83/1.49  --sat_fm_prep                           false
% 7.83/1.49  --sat_fm_uc_incr                        true
% 7.83/1.49  --sat_out_model                         small
% 7.83/1.49  --sat_out_clauses                       false
% 7.83/1.49  
% 7.83/1.49  ------ QBF Options
% 7.83/1.49  
% 7.83/1.49  --qbf_mode                              false
% 7.83/1.49  --qbf_elim_univ                         false
% 7.83/1.49  --qbf_dom_inst                          none
% 7.83/1.49  --qbf_dom_pre_inst                      false
% 7.83/1.49  --qbf_sk_in                             false
% 7.83/1.49  --qbf_pred_elim                         true
% 7.83/1.49  --qbf_split                             512
% 7.83/1.49  
% 7.83/1.49  ------ BMC1 Options
% 7.83/1.49  
% 7.83/1.49  --bmc1_incremental                      false
% 7.83/1.49  --bmc1_axioms                           reachable_all
% 7.83/1.49  --bmc1_min_bound                        0
% 7.83/1.49  --bmc1_max_bound                        -1
% 7.83/1.49  --bmc1_max_bound_default                -1
% 7.83/1.49  --bmc1_symbol_reachability              true
% 7.83/1.49  --bmc1_property_lemmas                  false
% 7.83/1.49  --bmc1_k_induction                      false
% 7.83/1.49  --bmc1_non_equiv_states                 false
% 7.83/1.49  --bmc1_deadlock                         false
% 7.83/1.49  --bmc1_ucm                              false
% 7.83/1.49  --bmc1_add_unsat_core                   none
% 7.83/1.49  --bmc1_unsat_core_children              false
% 7.83/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.83/1.49  --bmc1_out_stat                         full
% 7.83/1.49  --bmc1_ground_init                      false
% 7.83/1.49  --bmc1_pre_inst_next_state              false
% 7.83/1.49  --bmc1_pre_inst_state                   false
% 7.83/1.49  --bmc1_pre_inst_reach_state             false
% 7.83/1.49  --bmc1_out_unsat_core                   false
% 7.83/1.49  --bmc1_aig_witness_out                  false
% 7.83/1.49  --bmc1_verbose                          false
% 7.83/1.49  --bmc1_dump_clauses_tptp                false
% 7.83/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.83/1.49  --bmc1_dump_file                        -
% 7.83/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.83/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.83/1.49  --bmc1_ucm_extend_mode                  1
% 7.83/1.49  --bmc1_ucm_init_mode                    2
% 7.83/1.49  --bmc1_ucm_cone_mode                    none
% 7.83/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.83/1.49  --bmc1_ucm_relax_model                  4
% 7.83/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.83/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.83/1.49  --bmc1_ucm_layered_model                none
% 7.83/1.49  --bmc1_ucm_max_lemma_size               10
% 7.83/1.49  
% 7.83/1.49  ------ AIG Options
% 7.83/1.49  
% 7.83/1.49  --aig_mode                              false
% 7.83/1.49  
% 7.83/1.49  ------ Instantiation Options
% 7.83/1.49  
% 7.83/1.49  --instantiation_flag                    true
% 7.83/1.49  --inst_sos_flag                         true
% 7.83/1.49  --inst_sos_phase                        true
% 7.83/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.83/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.83/1.49  --inst_lit_sel_side                     num_symb
% 7.83/1.49  --inst_solver_per_active                1400
% 7.83/1.49  --inst_solver_calls_frac                1.
% 7.83/1.49  --inst_passive_queue_type               priority_queues
% 7.83/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.83/1.49  --inst_passive_queues_freq              [25;2]
% 7.83/1.49  --inst_dismatching                      true
% 7.83/1.49  --inst_eager_unprocessed_to_passive     true
% 7.83/1.49  --inst_prop_sim_given                   true
% 7.83/1.49  --inst_prop_sim_new                     false
% 7.83/1.49  --inst_subs_new                         false
% 7.83/1.49  --inst_eq_res_simp                      false
% 7.83/1.49  --inst_subs_given                       false
% 7.83/1.49  --inst_orphan_elimination               true
% 7.83/1.49  --inst_learning_loop_flag               true
% 7.83/1.49  --inst_learning_start                   3000
% 7.83/1.49  --inst_learning_factor                  2
% 7.83/1.49  --inst_start_prop_sim_after_learn       3
% 7.83/1.49  --inst_sel_renew                        solver
% 7.83/1.49  --inst_lit_activity_flag                true
% 7.83/1.49  --inst_restr_to_given                   false
% 7.83/1.49  --inst_activity_threshold               500
% 7.83/1.49  --inst_out_proof                        true
% 7.83/1.49  
% 7.83/1.49  ------ Resolution Options
% 7.83/1.49  
% 7.83/1.49  --resolution_flag                       true
% 7.83/1.49  --res_lit_sel                           adaptive
% 7.83/1.49  --res_lit_sel_side                      none
% 7.83/1.49  --res_ordering                          kbo
% 7.83/1.49  --res_to_prop_solver                    active
% 7.83/1.49  --res_prop_simpl_new                    false
% 7.83/1.49  --res_prop_simpl_given                  true
% 7.83/1.49  --res_passive_queue_type                priority_queues
% 7.83/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.83/1.49  --res_passive_queues_freq               [15;5]
% 7.83/1.49  --res_forward_subs                      full
% 7.83/1.49  --res_backward_subs                     full
% 7.83/1.49  --res_forward_subs_resolution           true
% 7.83/1.49  --res_backward_subs_resolution          true
% 7.83/1.49  --res_orphan_elimination                true
% 7.83/1.49  --res_time_limit                        2.
% 7.83/1.49  --res_out_proof                         true
% 7.83/1.49  
% 7.83/1.49  ------ Superposition Options
% 7.83/1.49  
% 7.83/1.49  --superposition_flag                    true
% 7.83/1.49  --sup_passive_queue_type                priority_queues
% 7.83/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.83/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.83/1.49  --demod_completeness_check              fast
% 7.83/1.49  --demod_use_ground                      true
% 7.83/1.49  --sup_to_prop_solver                    passive
% 7.83/1.49  --sup_prop_simpl_new                    true
% 7.83/1.49  --sup_prop_simpl_given                  true
% 7.83/1.49  --sup_fun_splitting                     true
% 7.83/1.49  --sup_smt_interval                      50000
% 7.83/1.49  
% 7.83/1.49  ------ Superposition Simplification Setup
% 7.83/1.49  
% 7.83/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.83/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.83/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.83/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.83/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.83/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.83/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.83/1.49  --sup_immed_triv                        [TrivRules]
% 7.83/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.83/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.83/1.49  --sup_immed_bw_main                     []
% 7.83/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.83/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.83/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.83/1.49  --sup_input_bw                          []
% 7.83/1.49  
% 7.83/1.49  ------ Combination Options
% 7.83/1.49  
% 7.83/1.49  --comb_res_mult                         3
% 7.83/1.49  --comb_sup_mult                         2
% 7.83/1.49  --comb_inst_mult                        10
% 7.83/1.49  
% 7.83/1.49  ------ Debug Options
% 7.83/1.49  
% 7.83/1.49  --dbg_backtrace                         false
% 7.83/1.49  --dbg_dump_prop_clauses                 false
% 7.83/1.49  --dbg_dump_prop_clauses_file            -
% 7.83/1.49  --dbg_out_stat                          false
% 7.83/1.49  ------ Parsing...
% 7.83/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.83/1.49  
% 7.83/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.83/1.49  
% 7.83/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.83/1.49  
% 7.83/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.83/1.49  ------ Proving...
% 7.83/1.49  ------ Problem Properties 
% 7.83/1.49  
% 7.83/1.49  
% 7.83/1.49  clauses                                 42
% 7.83/1.49  conjectures                             11
% 7.83/1.49  EPR                                     7
% 7.83/1.49  Horn                                    38
% 7.83/1.49  unary                                   12
% 7.83/1.49  binary                                  3
% 7.83/1.49  lits                                    176
% 7.83/1.49  lits eq                                 35
% 7.83/1.49  fd_pure                                 0
% 7.83/1.49  fd_pseudo                               0
% 7.83/1.49  fd_cond                                 4
% 7.83/1.49  fd_pseudo_cond                          1
% 7.83/1.49  AC symbols                              0
% 7.83/1.49  
% 7.83/1.49  ------ Schedule dynamic 5 is on 
% 7.83/1.49  
% 7.83/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.83/1.49  
% 7.83/1.49  
% 7.83/1.49  ------ 
% 7.83/1.49  Current options:
% 7.83/1.49  ------ 
% 7.83/1.49  
% 7.83/1.49  ------ Input Options
% 7.83/1.49  
% 7.83/1.49  --out_options                           all
% 7.83/1.49  --tptp_safe_out                         true
% 7.83/1.49  --problem_path                          ""
% 7.83/1.49  --include_path                          ""
% 7.83/1.49  --clausifier                            res/vclausify_rel
% 7.83/1.49  --clausifier_options                    ""
% 7.83/1.49  --stdin                                 false
% 7.83/1.49  --stats_out                             all
% 7.83/1.49  
% 7.83/1.49  ------ General Options
% 7.83/1.49  
% 7.83/1.49  --fof                                   false
% 7.83/1.49  --time_out_real                         305.
% 7.83/1.49  --time_out_virtual                      -1.
% 7.83/1.49  --symbol_type_check                     false
% 7.83/1.49  --clausify_out                          false
% 7.83/1.49  --sig_cnt_out                           false
% 7.83/1.49  --trig_cnt_out                          false
% 7.83/1.49  --trig_cnt_out_tolerance                1.
% 7.83/1.49  --trig_cnt_out_sk_spl                   false
% 7.83/1.49  --abstr_cl_out                          false
% 7.83/1.49  
% 7.83/1.49  ------ Global Options
% 7.83/1.49  
% 7.83/1.49  --schedule                              default
% 7.83/1.49  --add_important_lit                     false
% 7.83/1.49  --prop_solver_per_cl                    1000
% 7.83/1.49  --min_unsat_core                        false
% 7.83/1.49  --soft_assumptions                      false
% 7.83/1.49  --soft_lemma_size                       3
% 7.83/1.49  --prop_impl_unit_size                   0
% 7.83/1.49  --prop_impl_unit                        []
% 7.83/1.49  --share_sel_clauses                     true
% 7.83/1.49  --reset_solvers                         false
% 7.83/1.49  --bc_imp_inh                            [conj_cone]
% 7.83/1.49  --conj_cone_tolerance                   3.
% 7.83/1.49  --extra_neg_conj                        none
% 7.83/1.49  --large_theory_mode                     true
% 7.83/1.49  --prolific_symb_bound                   200
% 7.83/1.49  --lt_threshold                          2000
% 7.83/1.49  --clause_weak_htbl                      true
% 7.83/1.49  --gc_record_bc_elim                     false
% 7.83/1.49  
% 7.83/1.49  ------ Preprocessing Options
% 7.83/1.49  
% 7.83/1.49  --preprocessing_flag                    true
% 7.83/1.49  --time_out_prep_mult                    0.1
% 7.83/1.49  --splitting_mode                        input
% 7.83/1.49  --splitting_grd                         true
% 7.83/1.49  --splitting_cvd                         false
% 7.83/1.49  --splitting_cvd_svl                     false
% 7.83/1.49  --splitting_nvd                         32
% 7.83/1.49  --sub_typing                            true
% 7.83/1.49  --prep_gs_sim                           true
% 7.83/1.49  --prep_unflatten                        true
% 7.83/1.49  --prep_res_sim                          true
% 7.83/1.49  --prep_upred                            true
% 7.83/1.49  --prep_sem_filter                       exhaustive
% 7.83/1.49  --prep_sem_filter_out                   false
% 7.83/1.49  --pred_elim                             true
% 7.83/1.49  --res_sim_input                         true
% 7.83/1.49  --eq_ax_congr_red                       true
% 7.83/1.49  --pure_diseq_elim                       true
% 7.83/1.49  --brand_transform                       false
% 7.83/1.49  --non_eq_to_eq                          false
% 7.83/1.49  --prep_def_merge                        true
% 7.83/1.49  --prep_def_merge_prop_impl              false
% 7.83/1.49  --prep_def_merge_mbd                    true
% 7.83/1.49  --prep_def_merge_tr_red                 false
% 7.83/1.49  --prep_def_merge_tr_cl                  false
% 7.83/1.49  --smt_preprocessing                     true
% 7.83/1.49  --smt_ac_axioms                         fast
% 7.83/1.49  --preprocessed_out                      false
% 7.83/1.49  --preprocessed_stats                    false
% 7.83/1.49  
% 7.83/1.49  ------ Abstraction refinement Options
% 7.83/1.49  
% 7.83/1.49  --abstr_ref                             []
% 7.83/1.49  --abstr_ref_prep                        false
% 7.83/1.49  --abstr_ref_until_sat                   false
% 7.83/1.49  --abstr_ref_sig_restrict                funpre
% 7.83/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.83/1.49  --abstr_ref_under                       []
% 7.83/1.49  
% 7.83/1.49  ------ SAT Options
% 7.83/1.49  
% 7.83/1.49  --sat_mode                              false
% 7.83/1.49  --sat_fm_restart_options                ""
% 7.83/1.49  --sat_gr_def                            false
% 7.83/1.49  --sat_epr_types                         true
% 7.83/1.49  --sat_non_cyclic_types                  false
% 7.83/1.49  --sat_finite_models                     false
% 7.83/1.49  --sat_fm_lemmas                         false
% 7.83/1.49  --sat_fm_prep                           false
% 7.83/1.49  --sat_fm_uc_incr                        true
% 7.83/1.49  --sat_out_model                         small
% 7.83/1.49  --sat_out_clauses                       false
% 7.83/1.49  
% 7.83/1.49  ------ QBF Options
% 7.83/1.49  
% 7.83/1.49  --qbf_mode                              false
% 7.83/1.49  --qbf_elim_univ                         false
% 7.83/1.49  --qbf_dom_inst                          none
% 7.83/1.49  --qbf_dom_pre_inst                      false
% 7.83/1.49  --qbf_sk_in                             false
% 7.83/1.49  --qbf_pred_elim                         true
% 7.83/1.49  --qbf_split                             512
% 7.83/1.49  
% 7.83/1.49  ------ BMC1 Options
% 7.83/1.49  
% 7.83/1.49  --bmc1_incremental                      false
% 7.83/1.49  --bmc1_axioms                           reachable_all
% 7.83/1.49  --bmc1_min_bound                        0
% 7.83/1.49  --bmc1_max_bound                        -1
% 7.83/1.49  --bmc1_max_bound_default                -1
% 7.83/1.49  --bmc1_symbol_reachability              true
% 7.83/1.49  --bmc1_property_lemmas                  false
% 7.83/1.49  --bmc1_k_induction                      false
% 7.83/1.49  --bmc1_non_equiv_states                 false
% 7.83/1.49  --bmc1_deadlock                         false
% 7.83/1.49  --bmc1_ucm                              false
% 7.83/1.49  --bmc1_add_unsat_core                   none
% 7.83/1.49  --bmc1_unsat_core_children              false
% 7.83/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.83/1.49  --bmc1_out_stat                         full
% 7.83/1.49  --bmc1_ground_init                      false
% 7.83/1.49  --bmc1_pre_inst_next_state              false
% 7.83/1.49  --bmc1_pre_inst_state                   false
% 7.83/1.49  --bmc1_pre_inst_reach_state             false
% 7.83/1.49  --bmc1_out_unsat_core                   false
% 7.83/1.49  --bmc1_aig_witness_out                  false
% 7.83/1.49  --bmc1_verbose                          false
% 7.83/1.49  --bmc1_dump_clauses_tptp                false
% 7.83/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.83/1.49  --bmc1_dump_file                        -
% 7.83/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.83/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.83/1.49  --bmc1_ucm_extend_mode                  1
% 7.83/1.49  --bmc1_ucm_init_mode                    2
% 7.83/1.49  --bmc1_ucm_cone_mode                    none
% 7.83/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.83/1.49  --bmc1_ucm_relax_model                  4
% 7.83/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.83/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.83/1.49  --bmc1_ucm_layered_model                none
% 7.83/1.49  --bmc1_ucm_max_lemma_size               10
% 7.83/1.49  
% 7.83/1.49  ------ AIG Options
% 7.83/1.49  
% 7.83/1.49  --aig_mode                              false
% 7.83/1.49  
% 7.83/1.49  ------ Instantiation Options
% 7.83/1.49  
% 7.83/1.49  --instantiation_flag                    true
% 7.83/1.49  --inst_sos_flag                         true
% 7.83/1.49  --inst_sos_phase                        true
% 7.83/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.83/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.83/1.49  --inst_lit_sel_side                     none
% 7.83/1.49  --inst_solver_per_active                1400
% 7.83/1.49  --inst_solver_calls_frac                1.
% 7.83/1.49  --inst_passive_queue_type               priority_queues
% 7.83/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.83/1.49  --inst_passive_queues_freq              [25;2]
% 7.83/1.49  --inst_dismatching                      true
% 7.83/1.49  --inst_eager_unprocessed_to_passive     true
% 7.83/1.49  --inst_prop_sim_given                   true
% 7.83/1.49  --inst_prop_sim_new                     false
% 7.83/1.49  --inst_subs_new                         false
% 7.83/1.49  --inst_eq_res_simp                      false
% 7.83/1.49  --inst_subs_given                       false
% 7.83/1.49  --inst_orphan_elimination               true
% 7.83/1.49  --inst_learning_loop_flag               true
% 7.83/1.49  --inst_learning_start                   3000
% 7.83/1.49  --inst_learning_factor                  2
% 7.83/1.49  --inst_start_prop_sim_after_learn       3
% 7.83/1.49  --inst_sel_renew                        solver
% 7.83/1.49  --inst_lit_activity_flag                true
% 7.83/1.49  --inst_restr_to_given                   false
% 7.83/1.49  --inst_activity_threshold               500
% 7.83/1.49  --inst_out_proof                        true
% 7.83/1.49  
% 7.83/1.49  ------ Resolution Options
% 7.83/1.49  
% 7.83/1.49  --resolution_flag                       false
% 7.83/1.49  --res_lit_sel                           adaptive
% 7.83/1.49  --res_lit_sel_side                      none
% 7.83/1.49  --res_ordering                          kbo
% 7.83/1.49  --res_to_prop_solver                    active
% 7.83/1.49  --res_prop_simpl_new                    false
% 7.83/1.49  --res_prop_simpl_given                  true
% 7.83/1.49  --res_passive_queue_type                priority_queues
% 7.83/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.83/1.49  --res_passive_queues_freq               [15;5]
% 7.83/1.49  --res_forward_subs                      full
% 7.83/1.49  --res_backward_subs                     full
% 7.83/1.49  --res_forward_subs_resolution           true
% 7.83/1.49  --res_backward_subs_resolution          true
% 7.83/1.49  --res_orphan_elimination                true
% 7.83/1.49  --res_time_limit                        2.
% 7.83/1.49  --res_out_proof                         true
% 7.83/1.49  
% 7.83/1.49  ------ Superposition Options
% 7.83/1.49  
% 7.83/1.49  --superposition_flag                    true
% 7.83/1.49  --sup_passive_queue_type                priority_queues
% 7.83/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.83/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.83/1.49  --demod_completeness_check              fast
% 7.83/1.49  --demod_use_ground                      true
% 7.83/1.49  --sup_to_prop_solver                    passive
% 7.83/1.49  --sup_prop_simpl_new                    true
% 7.83/1.49  --sup_prop_simpl_given                  true
% 7.83/1.49  --sup_fun_splitting                     true
% 7.83/1.49  --sup_smt_interval                      50000
% 7.83/1.49  
% 7.83/1.49  ------ Superposition Simplification Setup
% 7.83/1.49  
% 7.83/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.83/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.83/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.83/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.83/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.83/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.83/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.83/1.49  --sup_immed_triv                        [TrivRules]
% 7.83/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.83/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.83/1.49  --sup_immed_bw_main                     []
% 7.83/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.83/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.83/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.83/1.49  --sup_input_bw                          []
% 7.83/1.49  
% 7.83/1.49  ------ Combination Options
% 7.83/1.49  
% 7.83/1.49  --comb_res_mult                         3
% 7.83/1.49  --comb_sup_mult                         2
% 7.83/1.49  --comb_inst_mult                        10
% 7.83/1.49  
% 7.83/1.49  ------ Debug Options
% 7.83/1.49  
% 7.83/1.49  --dbg_backtrace                         false
% 7.83/1.49  --dbg_dump_prop_clauses                 false
% 7.83/1.49  --dbg_dump_prop_clauses_file            -
% 7.83/1.49  --dbg_out_stat                          false
% 7.83/1.49  
% 7.83/1.49  
% 7.83/1.49  
% 7.83/1.49  
% 7.83/1.49  ------ Proving...
% 7.83/1.49  
% 7.83/1.49  
% 7.83/1.49  % SZS status Theorem for theBenchmark.p
% 7.83/1.49  
% 7.83/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.83/1.49  
% 7.83/1.49  fof(f11,axiom,(
% 7.83/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 7.83/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.83/1.49  
% 7.83/1.49  fof(f41,plain,(
% 7.83/1.49    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 7.83/1.49    inference(ennf_transformation,[],[f11])).
% 7.83/1.49  
% 7.83/1.49  fof(f42,plain,(
% 7.83/1.49    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.83/1.49    inference(flattening,[],[f41])).
% 7.83/1.49  
% 7.83/1.49  fof(f57,plain,(
% 7.83/1.49    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.83/1.49    inference(nnf_transformation,[],[f42])).
% 7.83/1.49  
% 7.83/1.49  fof(f78,plain,(
% 7.83/1.49    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.83/1.49    inference(cnf_transformation,[],[f57])).
% 7.83/1.49  
% 7.83/1.49  fof(f20,conjecture,(
% 7.83/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 7.83/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.83/1.49  
% 7.83/1.49  fof(f21,negated_conjecture,(
% 7.83/1.49    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 7.83/1.49    inference(negated_conjecture,[],[f20])).
% 7.83/1.49  
% 7.83/1.49  fof(f55,plain,(
% 7.83/1.49    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 7.83/1.49    inference(ennf_transformation,[],[f21])).
% 7.83/1.49  
% 7.83/1.49  fof(f56,plain,(
% 7.83/1.49    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 7.83/1.49    inference(flattening,[],[f55])).
% 7.83/1.49  
% 7.83/1.49  fof(f59,plain,(
% 7.83/1.49    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 7.83/1.49    introduced(choice_axiom,[])).
% 7.83/1.49  
% 7.83/1.49  fof(f58,plain,(
% 7.83/1.49    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 7.83/1.49    introduced(choice_axiom,[])).
% 7.83/1.49  
% 7.83/1.49  fof(f60,plain,(
% 7.83/1.49    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 7.83/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f56,f59,f58])).
% 7.83/1.49  
% 7.83/1.49  fof(f102,plain,(
% 7.83/1.49    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 7.83/1.49    inference(cnf_transformation,[],[f60])).
% 7.83/1.49  
% 7.83/1.49  fof(f13,axiom,(
% 7.83/1.49    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 7.83/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.83/1.49  
% 7.83/1.49  fof(f22,plain,(
% 7.83/1.49    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 7.83/1.49    inference(pure_predicate_removal,[],[f13])).
% 7.83/1.49  
% 7.83/1.49  fof(f82,plain,(
% 7.83/1.49    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 7.83/1.49    inference(cnf_transformation,[],[f22])).
% 7.83/1.49  
% 7.83/1.49  fof(f95,plain,(
% 7.83/1.49    v1_funct_1(sK2)),
% 7.83/1.49    inference(cnf_transformation,[],[f60])).
% 7.83/1.49  
% 7.83/1.49  fof(f97,plain,(
% 7.83/1.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 7.83/1.49    inference(cnf_transformation,[],[f60])).
% 7.83/1.49  
% 7.83/1.49  fof(f98,plain,(
% 7.83/1.49    v1_funct_1(sK3)),
% 7.83/1.49    inference(cnf_transformation,[],[f60])).
% 7.83/1.49  
% 7.83/1.49  fof(f100,plain,(
% 7.83/1.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 7.83/1.49    inference(cnf_transformation,[],[f60])).
% 7.83/1.49  
% 7.83/1.49  fof(f12,axiom,(
% 7.83/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 7.83/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.83/1.49  
% 7.83/1.49  fof(f43,plain,(
% 7.83/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 7.83/1.49    inference(ennf_transformation,[],[f12])).
% 7.83/1.49  
% 7.83/1.49  fof(f44,plain,(
% 7.83/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 7.83/1.49    inference(flattening,[],[f43])).
% 7.83/1.49  
% 7.83/1.49  fof(f81,plain,(
% 7.83/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 7.83/1.49    inference(cnf_transformation,[],[f44])).
% 7.83/1.49  
% 7.83/1.49  fof(f16,axiom,(
% 7.83/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 7.83/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.83/1.49  
% 7.83/1.49  fof(f47,plain,(
% 7.83/1.49    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 7.83/1.49    inference(ennf_transformation,[],[f16])).
% 7.83/1.49  
% 7.83/1.49  fof(f48,plain,(
% 7.83/1.49    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.83/1.49    inference(flattening,[],[f47])).
% 7.83/1.49  
% 7.83/1.49  fof(f85,plain,(
% 7.83/1.49    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.83/1.49    inference(cnf_transformation,[],[f48])).
% 7.83/1.49  
% 7.83/1.49  fof(f96,plain,(
% 7.83/1.49    v1_funct_2(sK2,sK0,sK1)),
% 7.83/1.49    inference(cnf_transformation,[],[f60])).
% 7.83/1.49  
% 7.83/1.49  fof(f99,plain,(
% 7.83/1.49    v1_funct_2(sK3,sK1,sK0)),
% 7.83/1.49    inference(cnf_transformation,[],[f60])).
% 7.83/1.49  
% 7.83/1.49  fof(f19,axiom,(
% 7.83/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 7.83/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.83/1.49  
% 7.83/1.49  fof(f53,plain,(
% 7.83/1.49    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 7.83/1.49    inference(ennf_transformation,[],[f19])).
% 7.83/1.49  
% 7.83/1.49  fof(f54,plain,(
% 7.83/1.49    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.83/1.49    inference(flattening,[],[f53])).
% 7.83/1.49  
% 7.83/1.49  fof(f93,plain,(
% 7.83/1.49    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.83/1.49    inference(cnf_transformation,[],[f54])).
% 7.83/1.49  
% 7.83/1.49  fof(f103,plain,(
% 7.83/1.49    v2_funct_1(sK2)),
% 7.83/1.49    inference(cnf_transformation,[],[f60])).
% 7.83/1.49  
% 7.83/1.49  fof(f1,axiom,(
% 7.83/1.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 7.83/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.83/1.49  
% 7.83/1.49  fof(f23,plain,(
% 7.83/1.49    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.83/1.49    inference(ennf_transformation,[],[f1])).
% 7.83/1.49  
% 7.83/1.49  fof(f24,plain,(
% 7.83/1.49    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.83/1.49    inference(flattening,[],[f23])).
% 7.83/1.49  
% 7.83/1.49  fof(f62,plain,(
% 7.83/1.49    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.83/1.49    inference(cnf_transformation,[],[f24])).
% 7.83/1.49  
% 7.83/1.49  fof(f61,plain,(
% 7.83/1.49    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.83/1.49    inference(cnf_transformation,[],[f24])).
% 7.83/1.49  
% 7.83/1.49  fof(f2,axiom,(
% 7.83/1.49    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 7.83/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.83/1.49  
% 7.83/1.49  fof(f25,plain,(
% 7.83/1.49    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.83/1.49    inference(ennf_transformation,[],[f2])).
% 7.83/1.49  
% 7.83/1.49  fof(f26,plain,(
% 7.83/1.49    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.83/1.49    inference(flattening,[],[f25])).
% 7.83/1.49  
% 7.83/1.49  fof(f65,plain,(
% 7.83/1.49    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.83/1.49    inference(cnf_transformation,[],[f26])).
% 7.83/1.49  
% 7.83/1.49  fof(f104,plain,(
% 7.83/1.49    k1_xboole_0 != sK0),
% 7.83/1.49    inference(cnf_transformation,[],[f60])).
% 7.83/1.49  
% 7.83/1.49  fof(f101,plain,(
% 7.83/1.49    k2_relset_1(sK0,sK1,sK2) = sK1),
% 7.83/1.49    inference(cnf_transformation,[],[f60])).
% 7.83/1.49  
% 7.83/1.49  fof(f9,axiom,(
% 7.83/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.83/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.83/1.49  
% 7.83/1.49  fof(f39,plain,(
% 7.83/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.83/1.49    inference(ennf_transformation,[],[f9])).
% 7.83/1.49  
% 7.83/1.49  fof(f76,plain,(
% 7.83/1.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.83/1.49    inference(cnf_transformation,[],[f39])).
% 7.83/1.49  
% 7.83/1.49  fof(f17,axiom,(
% 7.83/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 7.83/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.83/1.49  
% 7.83/1.49  fof(f49,plain,(
% 7.83/1.49    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 7.83/1.49    inference(ennf_transformation,[],[f17])).
% 7.83/1.49  
% 7.83/1.49  fof(f50,plain,(
% 7.83/1.49    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 7.83/1.49    inference(flattening,[],[f49])).
% 7.83/1.49  
% 7.83/1.49  fof(f88,plain,(
% 7.83/1.49    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X4) | k1_xboole_0 = X2 | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 7.83/1.49    inference(cnf_transformation,[],[f50])).
% 7.83/1.49  
% 7.83/1.49  fof(f105,plain,(
% 7.83/1.49    k1_xboole_0 != sK1),
% 7.83/1.49    inference(cnf_transformation,[],[f60])).
% 7.83/1.49  
% 7.83/1.49  fof(f3,axiom,(
% 7.83/1.49    ! [X0,X1] : ((v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))))),
% 7.83/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.83/1.49  
% 7.83/1.49  fof(f27,plain,(
% 7.83/1.49    ! [X0,X1] : ((v2_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | (~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.83/1.49    inference(ennf_transformation,[],[f3])).
% 7.83/1.49  
% 7.83/1.49  fof(f28,plain,(
% 7.83/1.49    ! [X0,X1] : ((v2_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.83/1.49    inference(flattening,[],[f27])).
% 7.83/1.49  
% 7.83/1.49  fof(f67,plain,(
% 7.83/1.49    ( ! [X0,X1] : (v2_funct_1(k5_relat_1(X0,X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.83/1.49    inference(cnf_transformation,[],[f28])).
% 7.83/1.49  
% 7.83/1.49  fof(f18,axiom,(
% 7.83/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 7.83/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.83/1.49  
% 7.83/1.49  fof(f51,plain,(
% 7.83/1.49    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 7.83/1.49    inference(ennf_transformation,[],[f18])).
% 7.83/1.49  
% 7.83/1.49  fof(f52,plain,(
% 7.83/1.49    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.83/1.49    inference(flattening,[],[f51])).
% 7.83/1.49  
% 7.83/1.49  fof(f92,plain,(
% 7.83/1.49    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.83/1.49    inference(cnf_transformation,[],[f52])).
% 7.83/1.49  
% 7.83/1.49  fof(f14,axiom,(
% 7.83/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 7.83/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.83/1.49  
% 7.83/1.49  fof(f45,plain,(
% 7.83/1.49    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 7.83/1.49    inference(ennf_transformation,[],[f14])).
% 7.83/1.49  
% 7.83/1.49  fof(f46,plain,(
% 7.83/1.49    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 7.83/1.49    inference(flattening,[],[f45])).
% 7.83/1.49  
% 7.83/1.49  fof(f83,plain,(
% 7.83/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 7.83/1.49    inference(cnf_transformation,[],[f46])).
% 7.83/1.49  
% 7.83/1.49  fof(f90,plain,(
% 7.83/1.49    ( ! [X2,X0,X1] : (v1_funct_1(k2_funct_1(X2)) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.83/1.49    inference(cnf_transformation,[],[f52])).
% 7.83/1.49  
% 7.83/1.49  fof(f5,axiom,(
% 7.83/1.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 7.83/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.83/1.49  
% 7.83/1.49  fof(f31,plain,(
% 7.83/1.49    ! [X0] : (((k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.83/1.49    inference(ennf_transformation,[],[f5])).
% 7.83/1.49  
% 7.83/1.49  fof(f32,plain,(
% 7.83/1.49    ! [X0] : ((k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.83/1.49    inference(flattening,[],[f31])).
% 7.83/1.49  
% 7.83/1.49  fof(f70,plain,(
% 7.83/1.49    ( ! [X0] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.83/1.49    inference(cnf_transformation,[],[f32])).
% 7.83/1.49  
% 7.83/1.49  fof(f94,plain,(
% 7.83/1.49    ( ! [X2,X0,X1] : (k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.83/1.49    inference(cnf_transformation,[],[f54])).
% 7.83/1.49  
% 7.83/1.49  fof(f6,axiom,(
% 7.83/1.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)))))),
% 7.83/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.83/1.49  
% 7.83/1.49  fof(f33,plain,(
% 7.83/1.49    ! [X0] : (((k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.83/1.49    inference(ennf_transformation,[],[f6])).
% 7.83/1.49  
% 7.83/1.49  fof(f34,plain,(
% 7.83/1.49    ! [X0] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.83/1.49    inference(flattening,[],[f33])).
% 7.83/1.49  
% 7.83/1.49  fof(f72,plain,(
% 7.83/1.49    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.83/1.49    inference(cnf_transformation,[],[f34])).
% 7.83/1.49  
% 7.83/1.49  fof(f10,axiom,(
% 7.83/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 7.83/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.83/1.49  
% 7.83/1.49  fof(f40,plain,(
% 7.83/1.49    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.83/1.49    inference(ennf_transformation,[],[f10])).
% 7.83/1.49  
% 7.83/1.49  fof(f77,plain,(
% 7.83/1.49    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.83/1.49    inference(cnf_transformation,[],[f40])).
% 7.83/1.49  
% 7.83/1.49  fof(f7,axiom,(
% 7.83/1.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 7.83/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.83/1.49  
% 7.83/1.49  fof(f35,plain,(
% 7.83/1.49    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.83/1.49    inference(ennf_transformation,[],[f7])).
% 7.83/1.49  
% 7.83/1.49  fof(f36,plain,(
% 7.83/1.49    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.83/1.49    inference(flattening,[],[f35])).
% 7.83/1.49  
% 7.83/1.49  fof(f74,plain,(
% 7.83/1.49    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.83/1.49    inference(cnf_transformation,[],[f36])).
% 7.83/1.49  
% 7.83/1.49  fof(f15,axiom,(
% 7.83/1.49    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 7.83/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.83/1.49  
% 7.83/1.49  fof(f84,plain,(
% 7.83/1.49    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 7.83/1.49    inference(cnf_transformation,[],[f15])).
% 7.83/1.49  
% 7.83/1.49  fof(f107,plain,(
% 7.83/1.49    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.83/1.49    inference(definition_unfolding,[],[f74,f84])).
% 7.83/1.49  
% 7.83/1.49  fof(f4,axiom,(
% 7.83/1.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 7.83/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.83/1.49  
% 7.83/1.49  fof(f29,plain,(
% 7.83/1.49    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.83/1.49    inference(ennf_transformation,[],[f4])).
% 7.83/1.49  
% 7.83/1.49  fof(f30,plain,(
% 7.83/1.49    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.83/1.49    inference(flattening,[],[f29])).
% 7.83/1.49  
% 7.83/1.49  fof(f69,plain,(
% 7.83/1.49    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.83/1.49    inference(cnf_transformation,[],[f30])).
% 7.83/1.49  
% 7.83/1.49  fof(f91,plain,(
% 7.83/1.49    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.83/1.49    inference(cnf_transformation,[],[f52])).
% 7.83/1.49  
% 7.83/1.49  fof(f106,plain,(
% 7.83/1.49    k2_funct_1(sK2) != sK3),
% 7.83/1.49    inference(cnf_transformation,[],[f60])).
% 7.83/1.49  
% 7.83/1.49  cnf(c_18,plain,
% 7.83/1.49      ( ~ r2_relset_1(X0,X1,X2,X3)
% 7.83/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.83/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.83/1.49      | X3 = X2 ),
% 7.83/1.49      inference(cnf_transformation,[],[f78]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_37,negated_conjecture,
% 7.83/1.49      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 7.83/1.49      inference(cnf_transformation,[],[f102]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_499,plain,
% 7.83/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.83/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.83/1.49      | X3 = X0
% 7.83/1.49      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 7.83/1.49      | k6_partfun1(sK0) != X3
% 7.83/1.49      | sK0 != X2
% 7.83/1.49      | sK0 != X1 ),
% 7.83/1.49      inference(resolution_lifted,[status(thm)],[c_18,c_37]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_500,plain,
% 7.83/1.49      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.83/1.49      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.83/1.49      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.83/1.49      inference(unflattening,[status(thm)],[c_499]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_21,plain,
% 7.83/1.49      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 7.83/1.49      inference(cnf_transformation,[],[f82]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_508,plain,
% 7.83/1.49      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.83/1.49      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.83/1.49      inference(forward_subsumption_resolution,
% 7.83/1.49                [status(thm)],
% 7.83/1.49                [c_500,c_21]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_819,plain,
% 7.83/1.49      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.83/1.49      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.83/1.49      inference(subtyping,[status(esa)],[c_508]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_1551,plain,
% 7.83/1.49      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.83/1.49      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 7.83/1.49      inference(predicate_to_equality,[status(thm)],[c_819]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_44,negated_conjecture,
% 7.83/1.49      ( v1_funct_1(sK2) ),
% 7.83/1.49      inference(cnf_transformation,[],[f95]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_42,negated_conjecture,
% 7.83/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 7.83/1.49      inference(cnf_transformation,[],[f97]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_41,negated_conjecture,
% 7.83/1.49      ( v1_funct_1(sK3) ),
% 7.83/1.49      inference(cnf_transformation,[],[f98]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_39,negated_conjecture,
% 7.83/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 7.83/1.49      inference(cnf_transformation,[],[f100]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_19,plain,
% 7.83/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.83/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.83/1.49      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.83/1.49      | ~ v1_funct_1(X0)
% 7.83/1.49      | ~ v1_funct_1(X3) ),
% 7.83/1.49      inference(cnf_transformation,[],[f81]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_844,plain,
% 7.83/1.49      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 7.83/1.49      | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49)))
% 7.83/1.49      | m1_subset_1(k1_partfun1(X2_49,X3_49,X0_49,X1_49,X1_48,X0_48),k1_zfmisc_1(k2_zfmisc_1(X2_49,X1_49)))
% 7.83/1.49      | ~ v1_funct_1(X0_48)
% 7.83/1.49      | ~ v1_funct_1(X1_48) ),
% 7.83/1.49      inference(subtyping,[status(esa)],[c_19]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_1629,plain,
% 7.83/1.49      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.83/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 7.83/1.49      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.83/1.49      | ~ v1_funct_1(sK3)
% 7.83/1.49      | ~ v1_funct_1(sK2) ),
% 7.83/1.49      inference(instantiation,[status(thm)],[c_844]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_1938,plain,
% 7.83/1.49      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.83/1.49      inference(global_propositional_subsumption,
% 7.83/1.49                [status(thm)],
% 7.83/1.49                [c_1551,c_44,c_42,c_41,c_39,c_819,c_1629]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_23,plain,
% 7.83/1.49      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 7.83/1.49      | ~ v1_funct_2(X2,X0,X1)
% 7.83/1.49      | ~ v1_funct_2(X3,X1,X0)
% 7.83/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 7.83/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.83/1.49      | ~ v1_funct_1(X2)
% 7.83/1.49      | ~ v1_funct_1(X3)
% 7.83/1.49      | k2_relset_1(X1,X0,X3) = X0 ),
% 7.83/1.49      inference(cnf_transformation,[],[f85]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_512,plain,
% 7.83/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.83/1.49      | ~ v1_funct_2(X3,X2,X1)
% 7.83/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 7.83/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.83/1.49      | ~ v1_funct_1(X0)
% 7.83/1.49      | ~ v1_funct_1(X3)
% 7.83/1.49      | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.83/1.49      | k2_relset_1(X1,X2,X0) = X2
% 7.83/1.49      | k6_partfun1(X2) != k6_partfun1(sK0)
% 7.83/1.49      | sK0 != X2 ),
% 7.83/1.49      inference(resolution_lifted,[status(thm)],[c_23,c_37]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_513,plain,
% 7.83/1.49      ( ~ v1_funct_2(X0,X1,sK0)
% 7.83/1.49      | ~ v1_funct_2(X2,sK0,X1)
% 7.83/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 7.83/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 7.83/1.49      | ~ v1_funct_1(X0)
% 7.83/1.49      | ~ v1_funct_1(X2)
% 7.83/1.49      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.83/1.49      | k2_relset_1(X1,sK0,X0) = sK0
% 7.83/1.49      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 7.83/1.49      inference(unflattening,[status(thm)],[c_512]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_605,plain,
% 7.83/1.49      ( ~ v1_funct_2(X0,X1,sK0)
% 7.83/1.49      | ~ v1_funct_2(X2,sK0,X1)
% 7.83/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 7.83/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 7.83/1.49      | ~ v1_funct_1(X0)
% 7.83/1.49      | ~ v1_funct_1(X2)
% 7.83/1.49      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.83/1.49      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 7.83/1.49      inference(equality_resolution_simp,[status(thm)],[c_513]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_818,plain,
% 7.83/1.49      ( ~ v1_funct_2(X0_48,X0_49,sK0)
% 7.83/1.49      | ~ v1_funct_2(X1_48,sK0,X0_49)
% 7.83/1.49      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,sK0)))
% 7.83/1.49      | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_49)))
% 7.83/1.49      | ~ v1_funct_1(X0_48)
% 7.83/1.49      | ~ v1_funct_1(X1_48)
% 7.83/1.49      | k2_relset_1(X0_49,sK0,X0_48) = sK0
% 7.83/1.49      | k1_partfun1(sK0,X0_49,X0_49,sK0,X1_48,X0_48) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.83/1.49      inference(subtyping,[status(esa)],[c_605]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_1552,plain,
% 7.83/1.49      ( k2_relset_1(X0_49,sK0,X0_48) = sK0
% 7.83/1.49      | k1_partfun1(sK0,X0_49,X0_49,sK0,X1_48,X0_48) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.83/1.49      | v1_funct_2(X0_48,X0_49,sK0) != iProver_top
% 7.83/1.49      | v1_funct_2(X1_48,sK0,X0_49) != iProver_top
% 7.83/1.49      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,sK0))) != iProver_top
% 7.83/1.49      | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_49))) != iProver_top
% 7.83/1.49      | v1_funct_1(X1_48) != iProver_top
% 7.83/1.49      | v1_funct_1(X0_48) != iProver_top ),
% 7.83/1.49      inference(predicate_to_equality,[status(thm)],[c_818]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_1967,plain,
% 7.83/1.49      ( k2_relset_1(X0_49,sK0,X0_48) = sK0
% 7.83/1.49      | k1_partfun1(sK0,X0_49,X0_49,sK0,X1_48,X0_48) != k6_partfun1(sK0)
% 7.83/1.49      | v1_funct_2(X0_48,X0_49,sK0) != iProver_top
% 7.83/1.49      | v1_funct_2(X1_48,sK0,X0_49) != iProver_top
% 7.83/1.49      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,sK0))) != iProver_top
% 7.83/1.49      | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_49))) != iProver_top
% 7.83/1.49      | v1_funct_1(X1_48) != iProver_top
% 7.83/1.49      | v1_funct_1(X0_48) != iProver_top ),
% 7.83/1.49      inference(light_normalisation,[status(thm)],[c_1552,c_1938]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_1971,plain,
% 7.83/1.49      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 7.83/1.49      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 7.83/1.49      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 7.83/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.83/1.49      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.83/1.49      | v1_funct_1(sK3) != iProver_top
% 7.83/1.49      | v1_funct_1(sK2) != iProver_top ),
% 7.83/1.49      inference(superposition,[status(thm)],[c_1938,c_1967]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_43,negated_conjecture,
% 7.83/1.49      ( v1_funct_2(sK2,sK0,sK1) ),
% 7.83/1.49      inference(cnf_transformation,[],[f96]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_40,negated_conjecture,
% 7.83/1.49      ( v1_funct_2(sK3,sK1,sK0) ),
% 7.83/1.49      inference(cnf_transformation,[],[f99]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_1637,plain,
% 7.83/1.49      ( ~ v1_funct_2(X0_48,sK0,sK1)
% 7.83/1.49      | ~ v1_funct_2(sK3,sK1,sK0)
% 7.83/1.49      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.83/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 7.83/1.49      | ~ v1_funct_1(X0_48)
% 7.83/1.49      | ~ v1_funct_1(sK3)
% 7.83/1.49      | k2_relset_1(sK1,sK0,sK3) = sK0
% 7.83/1.49      | k1_partfun1(sK0,sK1,sK1,sK0,X0_48,sK3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.83/1.49      inference(instantiation,[status(thm)],[c_818]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_1639,plain,
% 7.83/1.49      ( ~ v1_funct_2(sK3,sK1,sK0)
% 7.83/1.49      | ~ v1_funct_2(sK2,sK0,sK1)
% 7.83/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 7.83/1.49      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.83/1.49      | ~ v1_funct_1(sK3)
% 7.83/1.49      | ~ v1_funct_1(sK2)
% 7.83/1.49      | k2_relset_1(sK1,sK0,sK3) = sK0
% 7.83/1.49      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.83/1.49      inference(instantiation,[status(thm)],[c_1637]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_861,plain,( X0_48 = X0_48 ),theory(equality) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_1776,plain,
% 7.83/1.49      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.83/1.49      inference(instantiation,[status(thm)],[c_861]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_1974,plain,
% 7.83/1.49      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 7.83/1.49      inference(global_propositional_subsumption,
% 7.83/1.49                [status(thm)],
% 7.83/1.49                [c_1971,c_44,c_43,c_42,c_41,c_40,c_39,c_1639,c_1776]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_32,plain,
% 7.83/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.83/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.83/1.49      | ~ v2_funct_1(X0)
% 7.83/1.49      | ~ v1_funct_1(X0)
% 7.83/1.49      | k2_relset_1(X1,X2,X0) != X2
% 7.83/1.49      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 7.83/1.49      | k1_xboole_0 = X2 ),
% 7.83/1.49      inference(cnf_transformation,[],[f93]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_833,plain,
% 7.83/1.49      ( ~ v1_funct_2(X0_48,X0_49,X1_49)
% 7.83/1.49      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 7.83/1.49      | ~ v2_funct_1(X0_48)
% 7.83/1.49      | ~ v1_funct_1(X0_48)
% 7.83/1.49      | k2_relset_1(X0_49,X1_49,X0_48) != X1_49
% 7.83/1.49      | k1_xboole_0 = X1_49
% 7.83/1.49      | k5_relat_1(X0_48,k2_funct_1(X0_48)) = k6_partfun1(X0_49) ),
% 7.83/1.49      inference(subtyping,[status(esa)],[c_32]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_1541,plain,
% 7.83/1.49      ( k2_relset_1(X0_49,X1_49,X0_48) != X1_49
% 7.83/1.49      | k1_xboole_0 = X1_49
% 7.83/1.49      | k5_relat_1(X0_48,k2_funct_1(X0_48)) = k6_partfun1(X0_49)
% 7.83/1.49      | v1_funct_2(X0_48,X0_49,X1_49) != iProver_top
% 7.83/1.49      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 7.83/1.49      | v2_funct_1(X0_48) != iProver_top
% 7.83/1.49      | v1_funct_1(X0_48) != iProver_top ),
% 7.83/1.49      inference(predicate_to_equality,[status(thm)],[c_833]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_4889,plain,
% 7.83/1.49      ( sK0 = k1_xboole_0
% 7.83/1.49      | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 7.83/1.49      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 7.83/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.83/1.49      | v2_funct_1(sK3) != iProver_top
% 7.83/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.83/1.49      inference(superposition,[status(thm)],[c_1974,c_1541]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_45,plain,
% 7.83/1.49      ( v1_funct_1(sK2) = iProver_top ),
% 7.83/1.49      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_46,plain,
% 7.83/1.49      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 7.83/1.49      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_47,plain,
% 7.83/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.83/1.49      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_48,plain,
% 7.83/1.49      ( v1_funct_1(sK3) = iProver_top ),
% 7.83/1.49      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_49,plain,
% 7.83/1.49      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 7.83/1.49      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_50,plain,
% 7.83/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 7.83/1.49      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_36,negated_conjecture,
% 7.83/1.49      ( v2_funct_1(sK2) ),
% 7.83/1.49      inference(cnf_transformation,[],[f103]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_52,plain,
% 7.83/1.49      ( v2_funct_1(sK2) = iProver_top ),
% 7.83/1.49      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_862,plain,( X0_49 = X0_49 ),theory(equality) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_897,plain,
% 7.83/1.49      ( k1_xboole_0 = k1_xboole_0 ),
% 7.83/1.49      inference(instantiation,[status(thm)],[c_862]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_0,plain,
% 7.83/1.49      ( ~ v1_relat_1(X0)
% 7.83/1.49      | ~ v1_funct_1(X0)
% 7.83/1.49      | v1_funct_1(k2_funct_1(X0)) ),
% 7.83/1.49      inference(cnf_transformation,[],[f62]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_859,plain,
% 7.83/1.49      ( ~ v1_relat_1(X0_48)
% 7.83/1.49      | ~ v1_funct_1(X0_48)
% 7.83/1.49      | v1_funct_1(k2_funct_1(X0_48)) ),
% 7.83/1.49      inference(subtyping,[status(esa)],[c_0]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_900,plain,
% 7.83/1.49      ( v1_relat_1(X0_48) != iProver_top
% 7.83/1.49      | v1_funct_1(X0_48) != iProver_top
% 7.83/1.49      | v1_funct_1(k2_funct_1(X0_48)) = iProver_top ),
% 7.83/1.49      inference(predicate_to_equality,[status(thm)],[c_859]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_902,plain,
% 7.83/1.49      ( v1_relat_1(sK2) != iProver_top
% 7.83/1.49      | v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 7.83/1.49      | v1_funct_1(sK2) != iProver_top ),
% 7.83/1.49      inference(instantiation,[status(thm)],[c_900]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_1,plain,
% 7.83/1.49      ( ~ v1_relat_1(X0)
% 7.83/1.49      | v1_relat_1(k2_funct_1(X0))
% 7.83/1.49      | ~ v1_funct_1(X0) ),
% 7.83/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_858,plain,
% 7.83/1.49      ( ~ v1_relat_1(X0_48)
% 7.83/1.49      | v1_relat_1(k2_funct_1(X0_48))
% 7.83/1.49      | ~ v1_funct_1(X0_48) ),
% 7.83/1.49      inference(subtyping,[status(esa)],[c_1]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_903,plain,
% 7.83/1.49      ( v1_relat_1(X0_48) != iProver_top
% 7.83/1.49      | v1_relat_1(k2_funct_1(X0_48)) = iProver_top
% 7.83/1.49      | v1_funct_1(X0_48) != iProver_top ),
% 7.83/1.49      inference(predicate_to_equality,[status(thm)],[c_858]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_905,plain,
% 7.83/1.49      ( v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 7.83/1.49      | v1_relat_1(sK2) != iProver_top
% 7.83/1.49      | v1_funct_1(sK2) != iProver_top ),
% 7.83/1.49      inference(instantiation,[status(thm)],[c_903]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_2,plain,
% 7.83/1.49      ( ~ v2_funct_1(X0)
% 7.83/1.49      | v2_funct_1(k2_funct_1(X0))
% 7.83/1.49      | ~ v1_relat_1(X0)
% 7.83/1.49      | ~ v1_funct_1(X0) ),
% 7.83/1.49      inference(cnf_transformation,[],[f65]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_857,plain,
% 7.83/1.49      ( ~ v2_funct_1(X0_48)
% 7.83/1.49      | v2_funct_1(k2_funct_1(X0_48))
% 7.83/1.49      | ~ v1_relat_1(X0_48)
% 7.83/1.49      | ~ v1_funct_1(X0_48) ),
% 7.83/1.49      inference(subtyping,[status(esa)],[c_2]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_906,plain,
% 7.83/1.49      ( v2_funct_1(X0_48) != iProver_top
% 7.83/1.49      | v2_funct_1(k2_funct_1(X0_48)) = iProver_top
% 7.83/1.49      | v1_relat_1(X0_48) != iProver_top
% 7.83/1.49      | v1_funct_1(X0_48) != iProver_top ),
% 7.83/1.49      inference(predicate_to_equality,[status(thm)],[c_857]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_908,plain,
% 7.83/1.49      ( v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 7.83/1.49      | v2_funct_1(sK2) != iProver_top
% 7.83/1.49      | v1_relat_1(sK2) != iProver_top
% 7.83/1.49      | v1_funct_1(sK2) != iProver_top ),
% 7.83/1.49      inference(instantiation,[status(thm)],[c_906]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_35,negated_conjecture,
% 7.83/1.49      ( k1_xboole_0 != sK0 ),
% 7.83/1.49      inference(cnf_transformation,[],[f104]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_830,negated_conjecture,
% 7.83/1.49      ( k1_xboole_0 != sK0 ),
% 7.83/1.49      inference(subtyping,[status(esa)],[c_35]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_38,negated_conjecture,
% 7.83/1.49      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 7.83/1.49      inference(cnf_transformation,[],[f101]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_828,negated_conjecture,
% 7.83/1.49      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 7.83/1.49      inference(subtyping,[status(esa)],[c_38]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_866,plain,
% 7.83/1.49      ( X0_49 != X1_49 | X2_49 != X1_49 | X2_49 = X0_49 ),
% 7.83/1.49      theory(equality) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_1610,plain,
% 7.83/1.49      ( sK0 != X0_49 | k1_xboole_0 != X0_49 | k1_xboole_0 = sK0 ),
% 7.83/1.49      inference(instantiation,[status(thm)],[c_866]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_1611,plain,
% 7.83/1.49      ( sK0 != k1_xboole_0
% 7.83/1.49      | k1_xboole_0 = sK0
% 7.83/1.49      | k1_xboole_0 != k1_xboole_0 ),
% 7.83/1.49      inference(instantiation,[status(thm)],[c_1610]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_15,plain,
% 7.83/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.83/1.49      | v1_relat_1(X0) ),
% 7.83/1.49      inference(cnf_transformation,[],[f76]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_846,plain,
% 7.83/1.49      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 7.83/1.49      | v1_relat_1(X0_48) ),
% 7.83/1.49      inference(subtyping,[status(esa)],[c_15]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_1652,plain,
% 7.83/1.49      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 7.83/1.49      | v1_relat_1(sK2) ),
% 7.83/1.49      inference(instantiation,[status(thm)],[c_846]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_1713,plain,
% 7.83/1.49      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.83/1.49      | v1_relat_1(sK2) ),
% 7.83/1.49      inference(instantiation,[status(thm)],[c_1652]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_1714,plain,
% 7.83/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.83/1.49      | v1_relat_1(sK2) = iProver_top ),
% 7.83/1.49      inference(predicate_to_equality,[status(thm)],[c_1713]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_25,plain,
% 7.83/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.83/1.49      | ~ v1_funct_2(X3,X4,X1)
% 7.83/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 7.83/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.83/1.49      | v2_funct_1(X0)
% 7.83/1.49      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 7.83/1.49      | ~ v1_funct_1(X0)
% 7.83/1.49      | ~ v1_funct_1(X3)
% 7.83/1.49      | k2_relset_1(X4,X1,X3) != X1
% 7.83/1.49      | k1_xboole_0 = X2 ),
% 7.83/1.49      inference(cnf_transformation,[],[f88]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_839,plain,
% 7.83/1.49      ( ~ v1_funct_2(X0_48,X0_49,X1_49)
% 7.83/1.49      | ~ v1_funct_2(X1_48,X2_49,X0_49)
% 7.83/1.49      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 7.83/1.49      | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X0_49)))
% 7.83/1.49      | v2_funct_1(X0_48)
% 7.83/1.49      | ~ v2_funct_1(k1_partfun1(X2_49,X0_49,X0_49,X1_49,X1_48,X0_48))
% 7.83/1.49      | ~ v1_funct_1(X0_48)
% 7.83/1.49      | ~ v1_funct_1(X1_48)
% 7.83/1.49      | k2_relset_1(X2_49,X0_49,X1_48) != X0_49
% 7.83/1.49      | k1_xboole_0 = X1_49 ),
% 7.83/1.49      inference(subtyping,[status(esa)],[c_25]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_1750,plain,
% 7.83/1.49      ( ~ v1_funct_2(X0_48,X0_49,X1_49)
% 7.83/1.49      | ~ v1_funct_2(sK3,X1_49,X2_49)
% 7.83/1.49      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 7.83/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)))
% 7.83/1.49      | ~ v2_funct_1(k1_partfun1(X0_49,X1_49,X1_49,X2_49,X0_48,sK3))
% 7.83/1.49      | v2_funct_1(sK3)
% 7.83/1.49      | ~ v1_funct_1(X0_48)
% 7.83/1.49      | ~ v1_funct_1(sK3)
% 7.83/1.49      | k2_relset_1(X0_49,X1_49,X0_48) != X1_49
% 7.83/1.49      | k1_xboole_0 = X2_49 ),
% 7.83/1.49      inference(instantiation,[status(thm)],[c_839]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_1836,plain,
% 7.83/1.49      ( ~ v1_funct_2(X0_48,X0_49,X1_49)
% 7.83/1.49      | ~ v1_funct_2(sK3,X1_49,sK0)
% 7.83/1.49      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 7.83/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1_49,sK0)))
% 7.83/1.49      | ~ v2_funct_1(k1_partfun1(X0_49,X1_49,X1_49,sK0,X0_48,sK3))
% 7.83/1.49      | v2_funct_1(sK3)
% 7.83/1.49      | ~ v1_funct_1(X0_48)
% 7.83/1.49      | ~ v1_funct_1(sK3)
% 7.83/1.49      | k2_relset_1(X0_49,X1_49,X0_48) != X1_49
% 7.83/1.49      | k1_xboole_0 = sK0 ),
% 7.83/1.49      inference(instantiation,[status(thm)],[c_1750]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_1940,plain,
% 7.83/1.49      ( ~ v1_funct_2(X0_48,X0_49,sK1)
% 7.83/1.49      | ~ v1_funct_2(sK3,sK1,sK0)
% 7.83/1.49      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,sK1)))
% 7.83/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 7.83/1.49      | ~ v2_funct_1(k1_partfun1(X0_49,sK1,sK1,sK0,X0_48,sK3))
% 7.83/1.49      | v2_funct_1(sK3)
% 7.83/1.49      | ~ v1_funct_1(X0_48)
% 7.83/1.49      | ~ v1_funct_1(sK3)
% 7.83/1.49      | k2_relset_1(X0_49,sK1,X0_48) != sK1
% 7.83/1.49      | k1_xboole_0 = sK0 ),
% 7.83/1.49      inference(instantiation,[status(thm)],[c_1836]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_2166,plain,
% 7.83/1.49      ( ~ v1_funct_2(sK3,sK1,sK0)
% 7.83/1.49      | ~ v1_funct_2(sK2,sK0,sK1)
% 7.83/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 7.83/1.49      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.83/1.49      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
% 7.83/1.49      | v2_funct_1(sK3)
% 7.83/1.49      | ~ v1_funct_1(sK3)
% 7.83/1.49      | ~ v1_funct_1(sK2)
% 7.83/1.49      | k2_relset_1(sK0,sK1,sK2) != sK1
% 7.83/1.49      | k1_xboole_0 = sK0 ),
% 7.83/1.49      inference(instantiation,[status(thm)],[c_1940]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_2167,plain,
% 7.83/1.49      ( k2_relset_1(sK0,sK1,sK2) != sK1
% 7.83/1.49      | k1_xboole_0 = sK0
% 7.83/1.49      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 7.83/1.49      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 7.83/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.83/1.49      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.83/1.49      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) != iProver_top
% 7.83/1.49      | v2_funct_1(sK3) = iProver_top
% 7.83/1.49      | v1_funct_1(sK3) != iProver_top
% 7.83/1.49      | v1_funct_1(sK2) != iProver_top ),
% 7.83/1.49      inference(predicate_to_equality,[status(thm)],[c_2166]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_865,plain,
% 7.83/1.49      ( X0_48 != X1_48 | X2_48 != X1_48 | X2_48 = X0_48 ),
% 7.83/1.49      theory(equality) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_1794,plain,
% 7.83/1.49      ( X0_48 != X1_48
% 7.83/1.49      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X1_48
% 7.83/1.49      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = X0_48 ),
% 7.83/1.49      inference(instantiation,[status(thm)],[c_865]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_2023,plain,
% 7.83/1.49      ( X0_48 != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.83/1.49      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = X0_48
% 7.83/1.49      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.83/1.49      inference(instantiation,[status(thm)],[c_1794]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_2239,plain,
% 7.83/1.49      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.83/1.49      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
% 7.83/1.49      | k6_partfun1(sK0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.83/1.49      inference(instantiation,[status(thm)],[c_2023]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_870,plain,
% 7.83/1.49      ( ~ v2_funct_1(X0_48) | v2_funct_1(X1_48) | X1_48 != X0_48 ),
% 7.83/1.49      theory(equality) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_2450,plain,
% 7.83/1.49      ( ~ v2_funct_1(X0_48)
% 7.83/1.49      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
% 7.83/1.49      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0_48 ),
% 7.83/1.49      inference(instantiation,[status(thm)],[c_870]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_3135,plain,
% 7.83/1.49      ( v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
% 7.83/1.49      | ~ v2_funct_1(k6_partfun1(sK0))
% 7.83/1.49      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != k6_partfun1(sK0) ),
% 7.83/1.49      inference(instantiation,[status(thm)],[c_2450]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_3136,plain,
% 7.83/1.49      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != k6_partfun1(sK0)
% 7.83/1.49      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) = iProver_top
% 7.83/1.49      | v2_funct_1(k6_partfun1(sK0)) != iProver_top ),
% 7.83/1.49      inference(predicate_to_equality,[status(thm)],[c_3135]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_4888,plain,
% 7.83/1.49      ( sK1 = k1_xboole_0
% 7.83/1.49      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
% 7.83/1.49      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 7.83/1.49      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.83/1.49      | v2_funct_1(sK2) != iProver_top
% 7.83/1.49      | v1_funct_1(sK2) != iProver_top ),
% 7.83/1.49      inference(superposition,[status(thm)],[c_828,c_1541]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_34,negated_conjecture,
% 7.83/1.49      ( k1_xboole_0 != sK1 ),
% 7.83/1.49      inference(cnf_transformation,[],[f105]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_831,negated_conjecture,
% 7.83/1.49      ( k1_xboole_0 != sK1 ),
% 7.83/1.49      inference(subtyping,[status(esa)],[c_34]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_1612,plain,
% 7.83/1.49      ( ~ v1_funct_2(X0_48,X0_49,sK1)
% 7.83/1.49      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,sK1)))
% 7.83/1.49      | ~ v2_funct_1(X0_48)
% 7.83/1.49      | ~ v1_funct_1(X0_48)
% 7.83/1.49      | k2_relset_1(X0_49,sK1,X0_48) != sK1
% 7.83/1.49      | k1_xboole_0 = sK1
% 7.83/1.49      | k5_relat_1(X0_48,k2_funct_1(X0_48)) = k6_partfun1(X0_49) ),
% 7.83/1.49      inference(instantiation,[status(thm)],[c_833]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_1704,plain,
% 7.83/1.49      ( ~ v1_funct_2(sK2,sK0,sK1)
% 7.83/1.49      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.83/1.49      | ~ v2_funct_1(sK2)
% 7.83/1.49      | ~ v1_funct_1(sK2)
% 7.83/1.49      | k2_relset_1(sK0,sK1,sK2) != sK1
% 7.83/1.49      | k1_xboole_0 = sK1
% 7.83/1.49      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
% 7.83/1.49      inference(instantiation,[status(thm)],[c_1612]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_4895,plain,
% 7.83/1.49      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
% 7.83/1.49      inference(global_propositional_subsumption,
% 7.83/1.49                [status(thm)],
% 7.83/1.49                [c_4888,c_44,c_43,c_42,c_36,c_831,c_828,c_1704]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_5,plain,
% 7.83/1.49      ( ~ v2_funct_1(X0)
% 7.83/1.49      | ~ v2_funct_1(X1)
% 7.83/1.49      | v2_funct_1(k5_relat_1(X0,X1))
% 7.83/1.49      | ~ v1_relat_1(X0)
% 7.83/1.49      | ~ v1_relat_1(X1)
% 7.83/1.49      | ~ v1_funct_1(X0)
% 7.83/1.49      | ~ v1_funct_1(X1) ),
% 7.83/1.49      inference(cnf_transformation,[],[f67]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_856,plain,
% 7.83/1.49      ( ~ v2_funct_1(X0_48)
% 7.83/1.49      | ~ v2_funct_1(X1_48)
% 7.83/1.49      | v2_funct_1(k5_relat_1(X0_48,X1_48))
% 7.83/1.49      | ~ v1_relat_1(X0_48)
% 7.83/1.49      | ~ v1_relat_1(X1_48)
% 7.83/1.49      | ~ v1_funct_1(X0_48)
% 7.83/1.49      | ~ v1_funct_1(X1_48) ),
% 7.83/1.49      inference(subtyping,[status(esa)],[c_5]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_1518,plain,
% 7.83/1.49      ( v2_funct_1(X0_48) != iProver_top
% 7.83/1.49      | v2_funct_1(X1_48) != iProver_top
% 7.83/1.49      | v2_funct_1(k5_relat_1(X1_48,X0_48)) = iProver_top
% 7.83/1.49      | v1_relat_1(X1_48) != iProver_top
% 7.83/1.49      | v1_relat_1(X0_48) != iProver_top
% 7.83/1.49      | v1_funct_1(X0_48) != iProver_top
% 7.83/1.49      | v1_funct_1(X1_48) != iProver_top ),
% 7.83/1.49      inference(predicate_to_equality,[status(thm)],[c_856]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_4901,plain,
% 7.83/1.49      ( v2_funct_1(k6_partfun1(sK0)) = iProver_top
% 7.83/1.49      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 7.83/1.49      | v2_funct_1(sK2) != iProver_top
% 7.83/1.49      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 7.83/1.49      | v1_relat_1(sK2) != iProver_top
% 7.83/1.49      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 7.83/1.49      | v1_funct_1(sK2) != iProver_top ),
% 7.83/1.49      inference(superposition,[status(thm)],[c_4895,c_1518]) ).
% 7.83/1.49  
% 7.83/1.49  cnf(c_15509,plain,
% 7.83/1.49      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
% 7.83/1.49      inference(global_propositional_subsumption,
% 7.83/1.49                [status(thm)],
% 7.83/1.49                [c_4889,c_44,c_45,c_46,c_42,c_47,c_41,c_48,c_49,c_39,
% 7.83/1.49                 c_50,c_52,c_897,c_902,c_905,c_908,c_830,c_828,c_819,
% 7.83/1.49                 c_1611,c_1629,c_1714,c_1776,c_2167,c_2239,c_3136,c_4901]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_827,negated_conjecture,
% 7.83/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 7.83/1.50      inference(subtyping,[status(esa)],[c_39]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_1543,plain,
% 7.83/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 7.83/1.50      inference(predicate_to_equality,[status(thm)],[c_827]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_28,plain,
% 7.83/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.83/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.83/1.50      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 7.83/1.50      | ~ v2_funct_1(X0)
% 7.83/1.50      | ~ v1_funct_1(X0)
% 7.83/1.50      | k2_relset_1(X1,X2,X0) != X2 ),
% 7.83/1.50      inference(cnf_transformation,[],[f92]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_836,plain,
% 7.83/1.50      ( ~ v1_funct_2(X0_48,X0_49,X1_49)
% 7.83/1.50      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 7.83/1.50      | m1_subset_1(k2_funct_1(X0_48),k1_zfmisc_1(k2_zfmisc_1(X1_49,X0_49)))
% 7.83/1.50      | ~ v2_funct_1(X0_48)
% 7.83/1.50      | ~ v1_funct_1(X0_48)
% 7.83/1.50      | k2_relset_1(X0_49,X1_49,X0_48) != X1_49 ),
% 7.83/1.50      inference(subtyping,[status(esa)],[c_28]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_1538,plain,
% 7.83/1.50      ( k2_relset_1(X0_49,X1_49,X0_48) != X1_49
% 7.83/1.50      | v1_funct_2(X0_48,X0_49,X1_49) != iProver_top
% 7.83/1.50      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 7.83/1.50      | m1_subset_1(k2_funct_1(X0_48),k1_zfmisc_1(k2_zfmisc_1(X1_49,X0_49))) = iProver_top
% 7.83/1.50      | v2_funct_1(X0_48) != iProver_top
% 7.83/1.50      | v1_funct_1(X0_48) != iProver_top ),
% 7.83/1.50      inference(predicate_to_equality,[status(thm)],[c_836]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_4359,plain,
% 7.83/1.50      ( v1_funct_2(sK3,sK1,sK0) != iProver_top
% 7.83/1.50      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 7.83/1.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.83/1.50      | v2_funct_1(sK3) != iProver_top
% 7.83/1.50      | v1_funct_1(sK3) != iProver_top ),
% 7.83/1.50      inference(superposition,[status(thm)],[c_1974,c_1538]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_9317,plain,
% 7.83/1.50      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.83/1.50      inference(global_propositional_subsumption,
% 7.83/1.50                [status(thm)],
% 7.83/1.50                [c_4359,c_44,c_45,c_46,c_42,c_47,c_41,c_48,c_49,c_39,
% 7.83/1.50                 c_50,c_52,c_902,c_905,c_908,c_830,c_828,c_819,c_1629,
% 7.83/1.50                 c_1714,c_1776,c_2167,c_2239,c_3136,c_4901]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_22,plain,
% 7.83/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.83/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.83/1.50      | ~ v1_funct_1(X0)
% 7.83/1.50      | ~ v1_funct_1(X3)
% 7.83/1.50      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 7.83/1.50      inference(cnf_transformation,[],[f83]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_841,plain,
% 7.83/1.50      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 7.83/1.50      | ~ m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49)))
% 7.83/1.50      | ~ v1_funct_1(X0_48)
% 7.83/1.50      | ~ v1_funct_1(X1_48)
% 7.83/1.50      | k1_partfun1(X2_49,X3_49,X0_49,X1_49,X1_48,X0_48) = k5_relat_1(X1_48,X0_48) ),
% 7.83/1.50      inference(subtyping,[status(esa)],[c_22]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_1533,plain,
% 7.83/1.50      ( k1_partfun1(X0_49,X1_49,X2_49,X3_49,X0_48,X1_48) = k5_relat_1(X0_48,X1_48)
% 7.83/1.50      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 7.83/1.50      | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X2_49,X3_49))) != iProver_top
% 7.83/1.50      | v1_funct_1(X0_48) != iProver_top
% 7.83/1.50      | v1_funct_1(X1_48) != iProver_top ),
% 7.83/1.50      inference(predicate_to_equality,[status(thm)],[c_841]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_9328,plain,
% 7.83/1.50      ( k1_partfun1(X0_49,X1_49,sK0,sK1,X0_48,k2_funct_1(sK3)) = k5_relat_1(X0_48,k2_funct_1(sK3))
% 7.83/1.50      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 7.83/1.50      | v1_funct_1(X0_48) != iProver_top
% 7.83/1.50      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 7.83/1.50      inference(superposition,[status(thm)],[c_9317,c_1533]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_30,plain,
% 7.83/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.83/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.83/1.50      | ~ v2_funct_1(X0)
% 7.83/1.50      | ~ v1_funct_1(X0)
% 7.83/1.50      | v1_funct_1(k2_funct_1(X0))
% 7.83/1.50      | k2_relset_1(X1,X2,X0) != X2 ),
% 7.83/1.50      inference(cnf_transformation,[],[f90]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_241,plain,
% 7.83/1.50      ( v1_funct_1(k2_funct_1(X0))
% 7.83/1.50      | ~ v1_funct_1(X0)
% 7.83/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.83/1.50      inference(global_propositional_subsumption,
% 7.83/1.50                [status(thm)],
% 7.83/1.50                [c_30,c_15,c_0]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_242,plain,
% 7.83/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.83/1.50      | ~ v1_funct_1(X0)
% 7.83/1.50      | v1_funct_1(k2_funct_1(X0)) ),
% 7.83/1.50      inference(renaming,[status(thm)],[c_241]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_821,plain,
% 7.83/1.50      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 7.83/1.50      | ~ v1_funct_1(X0_48)
% 7.83/1.50      | v1_funct_1(k2_funct_1(X0_48)) ),
% 7.83/1.50      inference(subtyping,[status(esa)],[c_242]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_1549,plain,
% 7.83/1.50      ( m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 7.83/1.50      | v1_funct_1(X0_48) != iProver_top
% 7.83/1.50      | v1_funct_1(k2_funct_1(X0_48)) = iProver_top ),
% 7.83/1.50      inference(predicate_to_equality,[status(thm)],[c_821]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_2600,plain,
% 7.83/1.50      ( v1_funct_1(k2_funct_1(sK3)) = iProver_top
% 7.83/1.50      | v1_funct_1(sK3) != iProver_top ),
% 7.83/1.50      inference(superposition,[status(thm)],[c_1543,c_1549]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_10327,plain,
% 7.83/1.50      ( v1_funct_1(X0_48) != iProver_top
% 7.83/1.50      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 7.83/1.50      | k1_partfun1(X0_49,X1_49,sK0,sK1,X0_48,k2_funct_1(sK3)) = k5_relat_1(X0_48,k2_funct_1(sK3)) ),
% 7.83/1.50      inference(global_propositional_subsumption,
% 7.83/1.50                [status(thm)],
% 7.83/1.50                [c_9328,c_48,c_2600]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_10328,plain,
% 7.83/1.50      ( k1_partfun1(X0_49,X1_49,sK0,sK1,X0_48,k2_funct_1(sK3)) = k5_relat_1(X0_48,k2_funct_1(sK3))
% 7.83/1.50      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 7.83/1.50      | v1_funct_1(X0_48) != iProver_top ),
% 7.83/1.50      inference(renaming,[status(thm)],[c_10327]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_10333,plain,
% 7.83/1.50      ( k1_partfun1(sK1,sK0,sK0,sK1,sK3,k2_funct_1(sK3)) = k5_relat_1(sK3,k2_funct_1(sK3))
% 7.83/1.50      | v1_funct_1(sK3) != iProver_top ),
% 7.83/1.50      inference(superposition,[status(thm)],[c_1543,c_10328]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_10358,plain,
% 7.83/1.50      ( k1_partfun1(sK1,sK0,sK0,sK1,sK3,k2_funct_1(sK3)) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
% 7.83/1.50      inference(global_propositional_subsumption,
% 7.83/1.50                [status(thm)],
% 7.83/1.50                [c_10333,c_48]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_15512,plain,
% 7.83/1.50      ( k1_partfun1(sK1,sK0,sK0,sK1,sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
% 7.83/1.50      inference(demodulation,[status(thm)],[c_15509,c_10358]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_824,negated_conjecture,
% 7.83/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 7.83/1.50      inference(subtyping,[status(esa)],[c_42]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_1546,plain,
% 7.83/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.83/1.50      inference(predicate_to_equality,[status(thm)],[c_824]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_3642,plain,
% 7.83/1.50      ( k1_partfun1(X0_49,X1_49,sK0,sK1,X0_48,sK2) = k5_relat_1(X0_48,sK2)
% 7.83/1.50      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 7.83/1.50      | v1_funct_1(X0_48) != iProver_top
% 7.83/1.50      | v1_funct_1(sK2) != iProver_top ),
% 7.83/1.50      inference(superposition,[status(thm)],[c_1546,c_1533]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_4082,plain,
% 7.83/1.50      ( v1_funct_1(X0_48) != iProver_top
% 7.83/1.50      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 7.83/1.50      | k1_partfun1(X0_49,X1_49,sK0,sK1,X0_48,sK2) = k5_relat_1(X0_48,sK2) ),
% 7.83/1.50      inference(global_propositional_subsumption,
% 7.83/1.50                [status(thm)],
% 7.83/1.50                [c_3642,c_45]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_4083,plain,
% 7.83/1.50      ( k1_partfun1(X0_49,X1_49,sK0,sK1,X0_48,sK2) = k5_relat_1(X0_48,sK2)
% 7.83/1.50      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 7.83/1.50      | v1_funct_1(X0_48) != iProver_top ),
% 7.83/1.50      inference(renaming,[status(thm)],[c_4082]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_4086,plain,
% 7.83/1.50      ( k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) = k5_relat_1(sK3,sK2)
% 7.83/1.50      | v1_funct_1(sK3) != iProver_top ),
% 7.83/1.50      inference(superposition,[status(thm)],[c_1543,c_4083]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_4095,plain,
% 7.83/1.50      ( k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) = k5_relat_1(sK3,sK2) ),
% 7.83/1.50      inference(global_propositional_subsumption,
% 7.83/1.50                [status(thm)],
% 7.83/1.50                [c_4086,c_48]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_1535,plain,
% 7.83/1.50      ( k2_relset_1(X0_49,X1_49,X0_48) != X1_49
% 7.83/1.50      | k1_xboole_0 = X2_49
% 7.83/1.50      | v1_funct_2(X1_48,X1_49,X2_49) != iProver_top
% 7.83/1.50      | v1_funct_2(X0_48,X0_49,X1_49) != iProver_top
% 7.83/1.50      | m1_subset_1(X1_48,k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49))) != iProver_top
% 7.83/1.50      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 7.83/1.50      | v2_funct_1(X1_48) = iProver_top
% 7.83/1.50      | v2_funct_1(k1_partfun1(X0_49,X1_49,X1_49,X2_49,X0_48,X1_48)) != iProver_top
% 7.83/1.50      | v1_funct_1(X0_48) != iProver_top
% 7.83/1.50      | v1_funct_1(X1_48) != iProver_top ),
% 7.83/1.50      inference(predicate_to_equality,[status(thm)],[c_839]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_4963,plain,
% 7.83/1.50      ( k1_xboole_0 = X0_49
% 7.83/1.50      | v1_funct_2(X0_48,sK1,X0_49) != iProver_top
% 7.83/1.50      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 7.83/1.50      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(sK1,X0_49))) != iProver_top
% 7.83/1.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.83/1.50      | v2_funct_1(X0_48) = iProver_top
% 7.83/1.50      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0_49,sK2,X0_48)) != iProver_top
% 7.83/1.50      | v1_funct_1(X0_48) != iProver_top
% 7.83/1.50      | v1_funct_1(sK2) != iProver_top ),
% 7.83/1.50      inference(superposition,[status(thm)],[c_828,c_1535]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_5087,plain,
% 7.83/1.50      ( v1_funct_1(X0_48) != iProver_top
% 7.83/1.50      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0_49,sK2,X0_48)) != iProver_top
% 7.83/1.50      | v2_funct_1(X0_48) = iProver_top
% 7.83/1.50      | v1_funct_2(X0_48,sK1,X0_49) != iProver_top
% 7.83/1.50      | k1_xboole_0 = X0_49
% 7.83/1.50      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(sK1,X0_49))) != iProver_top ),
% 7.83/1.50      inference(global_propositional_subsumption,
% 7.83/1.50                [status(thm)],
% 7.83/1.50                [c_4963,c_45,c_46,c_47]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_5088,plain,
% 7.83/1.50      ( k1_xboole_0 = X0_49
% 7.83/1.50      | v1_funct_2(X0_48,sK1,X0_49) != iProver_top
% 7.83/1.50      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(sK1,X0_49))) != iProver_top
% 7.83/1.50      | v2_funct_1(X0_48) = iProver_top
% 7.83/1.50      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0_49,sK2,X0_48)) != iProver_top
% 7.83/1.50      | v1_funct_1(X0_48) != iProver_top ),
% 7.83/1.50      inference(renaming,[status(thm)],[c_5087]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_5091,plain,
% 7.83/1.50      ( sK0 = k1_xboole_0
% 7.83/1.50      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 7.83/1.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.83/1.50      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 7.83/1.50      | v2_funct_1(sK3) = iProver_top
% 7.83/1.50      | v1_funct_1(sK3) != iProver_top ),
% 7.83/1.50      inference(superposition,[status(thm)],[c_1938,c_5088]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_5420,plain,
% 7.83/1.50      ( v2_funct_1(sK3) = iProver_top ),
% 7.83/1.50      inference(global_propositional_subsumption,
% 7.83/1.50                [status(thm)],
% 7.83/1.50                [c_5091,c_44,c_45,c_46,c_42,c_47,c_41,c_48,c_49,c_39,
% 7.83/1.50                 c_50,c_52,c_902,c_905,c_908,c_830,c_828,c_819,c_1629,
% 7.83/1.50                 c_1714,c_1776,c_2167,c_2239,c_3136,c_4901]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_10,plain,
% 7.83/1.50      ( ~ v2_funct_1(X0)
% 7.83/1.50      | ~ v1_relat_1(X0)
% 7.83/1.50      | ~ v1_funct_1(X0)
% 7.83/1.50      | k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ),
% 7.83/1.50      inference(cnf_transformation,[],[f70]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_851,plain,
% 7.83/1.50      ( ~ v2_funct_1(X0_48)
% 7.83/1.50      | ~ v1_relat_1(X0_48)
% 7.83/1.50      | ~ v1_funct_1(X0_48)
% 7.83/1.50      | k1_relat_1(k5_relat_1(X0_48,k2_funct_1(X0_48))) = k1_relat_1(X0_48) ),
% 7.83/1.50      inference(subtyping,[status(esa)],[c_10]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_1523,plain,
% 7.83/1.50      ( k1_relat_1(k5_relat_1(X0_48,k2_funct_1(X0_48))) = k1_relat_1(X0_48)
% 7.83/1.50      | v2_funct_1(X0_48) != iProver_top
% 7.83/1.50      | v1_relat_1(X0_48) != iProver_top
% 7.83/1.50      | v1_funct_1(X0_48) != iProver_top ),
% 7.83/1.50      inference(predicate_to_equality,[status(thm)],[c_851]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_5428,plain,
% 7.83/1.50      ( k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) = k1_relat_1(sK3)
% 7.83/1.50      | v1_relat_1(sK3) != iProver_top
% 7.83/1.50      | v1_funct_1(sK3) != iProver_top ),
% 7.83/1.50      inference(superposition,[status(thm)],[c_5420,c_1523]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_1851,plain,
% 7.83/1.50      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 7.83/1.50      | v1_relat_1(sK3) ),
% 7.83/1.50      inference(instantiation,[status(thm)],[c_846]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_1949,plain,
% 7.83/1.50      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 7.83/1.50      | v1_relat_1(sK3) ),
% 7.83/1.50      inference(instantiation,[status(thm)],[c_1851]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_1950,plain,
% 7.83/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.83/1.50      | v1_relat_1(sK3) = iProver_top ),
% 7.83/1.50      inference(predicate_to_equality,[status(thm)],[c_1949]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_5647,plain,
% 7.83/1.50      ( k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) = k1_relat_1(sK3) ),
% 7.83/1.50      inference(global_propositional_subsumption,
% 7.83/1.50                [status(thm)],
% 7.83/1.50                [c_5428,c_48,c_50,c_1950]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_15514,plain,
% 7.83/1.50      ( k1_relat_1(k6_partfun1(sK1)) = k1_relat_1(sK3) ),
% 7.83/1.50      inference(demodulation,[status(thm)],[c_15509,c_5647]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_31,plain,
% 7.83/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.83/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.83/1.50      | ~ v2_funct_1(X0)
% 7.83/1.50      | ~ v1_funct_1(X0)
% 7.83/1.50      | k2_relset_1(X1,X2,X0) != X2
% 7.83/1.50      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
% 7.83/1.50      | k1_xboole_0 = X2 ),
% 7.83/1.50      inference(cnf_transformation,[],[f94]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_834,plain,
% 7.83/1.50      ( ~ v1_funct_2(X0_48,X0_49,X1_49)
% 7.83/1.50      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 7.83/1.50      | ~ v2_funct_1(X0_48)
% 7.83/1.50      | ~ v1_funct_1(X0_48)
% 7.83/1.50      | k2_relset_1(X0_49,X1_49,X0_48) != X1_49
% 7.83/1.50      | k1_xboole_0 = X1_49
% 7.83/1.50      | k5_relat_1(k2_funct_1(X0_48),X0_48) = k6_partfun1(X1_49) ),
% 7.83/1.50      inference(subtyping,[status(esa)],[c_31]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_1540,plain,
% 7.83/1.50      ( k2_relset_1(X0_49,X1_49,X0_48) != X1_49
% 7.83/1.50      | k1_xboole_0 = X1_49
% 7.83/1.50      | k5_relat_1(k2_funct_1(X0_48),X0_48) = k6_partfun1(X1_49)
% 7.83/1.50      | v1_funct_2(X0_48,X0_49,X1_49) != iProver_top
% 7.83/1.50      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 7.83/1.50      | v2_funct_1(X0_48) != iProver_top
% 7.83/1.50      | v1_funct_1(X0_48) != iProver_top ),
% 7.83/1.50      inference(predicate_to_equality,[status(thm)],[c_834]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_4468,plain,
% 7.83/1.50      ( sK1 = k1_xboole_0
% 7.83/1.50      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 7.83/1.50      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 7.83/1.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.83/1.50      | v2_funct_1(sK2) != iProver_top
% 7.83/1.50      | v1_funct_1(sK2) != iProver_top ),
% 7.83/1.50      inference(superposition,[status(thm)],[c_828,c_1540]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_1613,plain,
% 7.83/1.50      ( ~ v1_funct_2(X0_48,X0_49,sK1)
% 7.83/1.50      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,sK1)))
% 7.83/1.50      | ~ v2_funct_1(X0_48)
% 7.83/1.50      | ~ v1_funct_1(X0_48)
% 7.83/1.50      | k2_relset_1(X0_49,sK1,X0_48) != sK1
% 7.83/1.50      | k1_xboole_0 = sK1
% 7.83/1.50      | k5_relat_1(k2_funct_1(X0_48),X0_48) = k6_partfun1(sK1) ),
% 7.83/1.50      inference(instantiation,[status(thm)],[c_834]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_1682,plain,
% 7.83/1.50      ( ~ v1_funct_2(sK2,sK0,sK1)
% 7.83/1.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.83/1.50      | ~ v2_funct_1(sK2)
% 7.83/1.50      | ~ v1_funct_1(sK2)
% 7.83/1.50      | k2_relset_1(sK0,sK1,sK2) != sK1
% 7.83/1.50      | k1_xboole_0 = sK1
% 7.83/1.50      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
% 7.83/1.50      inference(instantiation,[status(thm)],[c_1613]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_4475,plain,
% 7.83/1.50      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
% 7.83/1.50      inference(global_propositional_subsumption,
% 7.83/1.50                [status(thm)],
% 7.83/1.50                [c_4468,c_44,c_43,c_42,c_36,c_831,c_828,c_1682]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_829,negated_conjecture,
% 7.83/1.50      ( v2_funct_1(sK2) ),
% 7.83/1.50      inference(subtyping,[status(esa)],[c_36]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_1542,plain,
% 7.83/1.50      ( v2_funct_1(sK2) = iProver_top ),
% 7.83/1.50      inference(predicate_to_equality,[status(thm)],[c_829]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_12,plain,
% 7.83/1.50      ( ~ v2_funct_1(X0)
% 7.83/1.50      | ~ v1_relat_1(X0)
% 7.83/1.50      | ~ v1_funct_1(X0)
% 7.83/1.50      | k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) ),
% 7.83/1.50      inference(cnf_transformation,[],[f72]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_849,plain,
% 7.83/1.50      ( ~ v2_funct_1(X0_48)
% 7.83/1.50      | ~ v1_relat_1(X0_48)
% 7.83/1.50      | ~ v1_funct_1(X0_48)
% 7.83/1.50      | k1_relat_1(k5_relat_1(k2_funct_1(X0_48),X0_48)) = k2_relat_1(X0_48) ),
% 7.83/1.50      inference(subtyping,[status(esa)],[c_12]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_1525,plain,
% 7.83/1.50      ( k1_relat_1(k5_relat_1(k2_funct_1(X0_48),X0_48)) = k2_relat_1(X0_48)
% 7.83/1.50      | v2_funct_1(X0_48) != iProver_top
% 7.83/1.50      | v1_relat_1(X0_48) != iProver_top
% 7.83/1.50      | v1_funct_1(X0_48) != iProver_top ),
% 7.83/1.50      inference(predicate_to_equality,[status(thm)],[c_849]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_3351,plain,
% 7.83/1.50      ( k1_relat_1(k5_relat_1(k2_funct_1(sK2),sK2)) = k2_relat_1(sK2)
% 7.83/1.50      | v1_relat_1(sK2) != iProver_top
% 7.83/1.50      | v1_funct_1(sK2) != iProver_top ),
% 7.83/1.50      inference(superposition,[status(thm)],[c_1542,c_1525]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_16,plain,
% 7.83/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.83/1.50      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 7.83/1.50      inference(cnf_transformation,[],[f77]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_845,plain,
% 7.83/1.50      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 7.83/1.50      | k2_relset_1(X0_49,X1_49,X0_48) = k2_relat_1(X0_48) ),
% 7.83/1.50      inference(subtyping,[status(esa)],[c_16]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_1529,plain,
% 7.83/1.50      ( k2_relset_1(X0_49,X1_49,X0_48) = k2_relat_1(X0_48)
% 7.83/1.50      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top ),
% 7.83/1.50      inference(predicate_to_equality,[status(thm)],[c_845]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_2280,plain,
% 7.83/1.50      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 7.83/1.50      inference(superposition,[status(thm)],[c_1546,c_1529]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_2282,plain,
% 7.83/1.50      ( k2_relat_1(sK2) = sK1 ),
% 7.83/1.50      inference(light_normalisation,[status(thm)],[c_2280,c_828]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_3354,plain,
% 7.83/1.50      ( k1_relat_1(k5_relat_1(k2_funct_1(sK2),sK2)) = sK1
% 7.83/1.50      | v1_relat_1(sK2) != iProver_top
% 7.83/1.50      | v1_funct_1(sK2) != iProver_top ),
% 7.83/1.50      inference(light_normalisation,[status(thm)],[c_3351,c_2282]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_3429,plain,
% 7.83/1.50      ( k1_relat_1(k5_relat_1(k2_funct_1(sK2),sK2)) = sK1 ),
% 7.83/1.50      inference(global_propositional_subsumption,
% 7.83/1.50                [status(thm)],
% 7.83/1.50                [c_3354,c_45,c_47,c_1714]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_4477,plain,
% 7.83/1.50      ( k1_relat_1(k6_partfun1(sK1)) = sK1 ),
% 7.83/1.50      inference(demodulation,[status(thm)],[c_4475,c_3429]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_15515,plain,
% 7.83/1.50      ( k1_relat_1(sK3) = sK1 ),
% 7.83/1.50      inference(light_normalisation,[status(thm)],[c_15514,c_4477]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_3641,plain,
% 7.83/1.50      ( k1_partfun1(X0_49,X1_49,sK1,sK0,X0_48,sK3) = k5_relat_1(X0_48,sK3)
% 7.83/1.50      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 7.83/1.50      | v1_funct_1(X0_48) != iProver_top
% 7.83/1.50      | v1_funct_1(sK3) != iProver_top ),
% 7.83/1.50      inference(superposition,[status(thm)],[c_1543,c_1533]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_3891,plain,
% 7.83/1.50      ( v1_funct_1(X0_48) != iProver_top
% 7.83/1.50      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 7.83/1.50      | k1_partfun1(X0_49,X1_49,sK1,sK0,X0_48,sK3) = k5_relat_1(X0_48,sK3) ),
% 7.83/1.50      inference(global_propositional_subsumption,
% 7.83/1.50                [status(thm)],
% 7.83/1.50                [c_3641,c_48]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_3892,plain,
% 7.83/1.50      ( k1_partfun1(X0_49,X1_49,sK1,sK0,X0_48,sK3) = k5_relat_1(X0_48,sK3)
% 7.83/1.50      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 7.83/1.50      | v1_funct_1(X0_48) != iProver_top ),
% 7.83/1.50      inference(renaming,[status(thm)],[c_3891]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_3898,plain,
% 7.83/1.50      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 7.83/1.50      | v1_funct_1(sK2) != iProver_top ),
% 7.83/1.50      inference(superposition,[status(thm)],[c_1546,c_3892]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_3900,plain,
% 7.83/1.50      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 7.83/1.50      | v1_funct_1(sK2) != iProver_top ),
% 7.83/1.50      inference(light_normalisation,[status(thm)],[c_3898,c_1938]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_4188,plain,
% 7.83/1.50      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 7.83/1.50      inference(global_propositional_subsumption,
% 7.83/1.50                [status(thm)],
% 7.83/1.50                [c_3900,c_45]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_13,plain,
% 7.83/1.50      ( ~ v2_funct_1(X0)
% 7.83/1.50      | ~ v1_relat_1(X0)
% 7.83/1.50      | ~ v1_relat_1(X1)
% 7.83/1.50      | ~ v1_funct_1(X0)
% 7.83/1.50      | ~ v1_funct_1(X1)
% 7.83/1.50      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
% 7.83/1.50      | k1_relat_1(X0) != k2_relat_1(X1)
% 7.83/1.50      | k2_funct_1(X0) = X1 ),
% 7.83/1.50      inference(cnf_transformation,[],[f107]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_848,plain,
% 7.83/1.50      ( ~ v2_funct_1(X0_48)
% 7.83/1.50      | ~ v1_relat_1(X0_48)
% 7.83/1.50      | ~ v1_relat_1(X1_48)
% 7.83/1.50      | ~ v1_funct_1(X0_48)
% 7.83/1.50      | ~ v1_funct_1(X1_48)
% 7.83/1.50      | k1_relat_1(X0_48) != k2_relat_1(X1_48)
% 7.83/1.50      | k5_relat_1(X1_48,X0_48) != k6_partfun1(k2_relat_1(X0_48))
% 7.83/1.50      | k2_funct_1(X0_48) = X1_48 ),
% 7.83/1.50      inference(subtyping,[status(esa)],[c_13]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_1526,plain,
% 7.83/1.50      ( k1_relat_1(X0_48) != k2_relat_1(X1_48)
% 7.83/1.50      | k5_relat_1(X1_48,X0_48) != k6_partfun1(k2_relat_1(X0_48))
% 7.83/1.50      | k2_funct_1(X0_48) = X1_48
% 7.83/1.50      | v2_funct_1(X0_48) != iProver_top
% 7.83/1.50      | v1_relat_1(X0_48) != iProver_top
% 7.83/1.50      | v1_relat_1(X1_48) != iProver_top
% 7.83/1.50      | v1_funct_1(X1_48) != iProver_top
% 7.83/1.50      | v1_funct_1(X0_48) != iProver_top ),
% 7.83/1.50      inference(predicate_to_equality,[status(thm)],[c_848]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_4274,plain,
% 7.83/1.50      ( k1_relat_1(sK3) != k2_relat_1(sK2)
% 7.83/1.50      | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
% 7.83/1.50      | k2_funct_1(sK3) = sK2
% 7.83/1.50      | v2_funct_1(sK3) != iProver_top
% 7.83/1.50      | v1_relat_1(sK3) != iProver_top
% 7.83/1.50      | v1_relat_1(sK2) != iProver_top
% 7.83/1.50      | v1_funct_1(sK3) != iProver_top
% 7.83/1.50      | v1_funct_1(sK2) != iProver_top ),
% 7.83/1.50      inference(superposition,[status(thm)],[c_4188,c_1526]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_2279,plain,
% 7.83/1.50      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 7.83/1.50      inference(superposition,[status(thm)],[c_1543,c_1529]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_2283,plain,
% 7.83/1.50      ( k2_relat_1(sK3) = sK0 ),
% 7.83/1.50      inference(light_normalisation,[status(thm)],[c_2279,c_1974]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_4275,plain,
% 7.83/1.50      ( k1_relat_1(sK3) != sK1
% 7.83/1.50      | k6_partfun1(sK0) != k6_partfun1(sK0)
% 7.83/1.50      | k2_funct_1(sK3) = sK2
% 7.83/1.50      | v2_funct_1(sK3) != iProver_top
% 7.83/1.50      | v1_relat_1(sK3) != iProver_top
% 7.83/1.50      | v1_relat_1(sK2) != iProver_top
% 7.83/1.50      | v1_funct_1(sK3) != iProver_top
% 7.83/1.50      | v1_funct_1(sK2) != iProver_top ),
% 7.83/1.50      inference(light_normalisation,[status(thm)],[c_4274,c_2282,c_2283]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_4276,plain,
% 7.83/1.50      ( k1_relat_1(sK3) != sK1
% 7.83/1.50      | k2_funct_1(sK3) = sK2
% 7.83/1.50      | v2_funct_1(sK3) != iProver_top
% 7.83/1.50      | v1_relat_1(sK3) != iProver_top
% 7.83/1.50      | v1_relat_1(sK2) != iProver_top
% 7.83/1.50      | v1_funct_1(sK3) != iProver_top
% 7.83/1.50      | v1_funct_1(sK2) != iProver_top ),
% 7.83/1.50      inference(equality_resolution_simp,[status(thm)],[c_4275]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_901,plain,
% 7.83/1.50      ( ~ v1_relat_1(sK2)
% 7.83/1.50      | v1_funct_1(k2_funct_1(sK2))
% 7.83/1.50      | ~ v1_funct_1(sK2) ),
% 7.83/1.50      inference(instantiation,[status(thm)],[c_859]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_904,plain,
% 7.83/1.50      ( v1_relat_1(k2_funct_1(sK2))
% 7.83/1.50      | ~ v1_relat_1(sK2)
% 7.83/1.50      | ~ v1_funct_1(sK2) ),
% 7.83/1.50      inference(instantiation,[status(thm)],[c_858]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_907,plain,
% 7.83/1.50      ( v2_funct_1(k2_funct_1(sK2))
% 7.83/1.50      | ~ v2_funct_1(sK2)
% 7.83/1.50      | ~ v1_relat_1(sK2)
% 7.83/1.50      | ~ v1_funct_1(sK2) ),
% 7.83/1.50      inference(instantiation,[status(thm)],[c_857]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_4277,plain,
% 7.83/1.50      ( ~ v2_funct_1(sK3)
% 7.83/1.50      | ~ v1_relat_1(sK3)
% 7.83/1.50      | ~ v1_relat_1(sK2)
% 7.83/1.50      | ~ v1_funct_1(sK3)
% 7.83/1.50      | ~ v1_funct_1(sK2)
% 7.83/1.50      | k1_relat_1(sK3) != sK1
% 7.83/1.50      | k2_funct_1(sK3) = sK2 ),
% 7.83/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_4276]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_4902,plain,
% 7.83/1.50      ( v2_funct_1(k6_partfun1(sK0))
% 7.83/1.50      | ~ v2_funct_1(k2_funct_1(sK2))
% 7.83/1.50      | ~ v2_funct_1(sK2)
% 7.83/1.50      | ~ v1_relat_1(k2_funct_1(sK2))
% 7.83/1.50      | ~ v1_relat_1(sK2)
% 7.83/1.50      | ~ v1_funct_1(k2_funct_1(sK2))
% 7.83/1.50      | ~ v1_funct_1(sK2) ),
% 7.83/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_4901]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_9717,plain,
% 7.83/1.50      ( k2_funct_1(sK3) = sK2 | k1_relat_1(sK3) != sK1 ),
% 7.83/1.50      inference(global_propositional_subsumption,
% 7.83/1.50                [status(thm)],
% 7.83/1.50                [c_4276,c_44,c_43,c_42,c_41,c_40,c_39,c_36,c_901,c_904,
% 7.83/1.50                 c_907,c_830,c_828,c_819,c_1629,c_1713,c_1776,c_1949,
% 7.83/1.50                 c_2166,c_2239,c_3135,c_4277,c_4902]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_9718,plain,
% 7.83/1.50      ( k1_relat_1(sK3) != sK1 | k2_funct_1(sK3) = sK2 ),
% 7.83/1.50      inference(renaming,[status(thm)],[c_9717]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_15570,plain,
% 7.83/1.50      ( sK1 != sK1 | k2_funct_1(sK3) = sK2 ),
% 7.83/1.50      inference(demodulation,[status(thm)],[c_15515,c_9718]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_15572,plain,
% 7.83/1.50      ( k2_funct_1(sK3) = sK2 ),
% 7.83/1.50      inference(equality_resolution_simp,[status(thm)],[c_15570]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_15574,plain,
% 7.83/1.50      ( k5_relat_1(sK3,sK2) = k6_partfun1(sK1) ),
% 7.83/1.50      inference(light_normalisation,
% 7.83/1.50                [status(thm)],
% 7.83/1.50                [c_15512,c_4095,c_15512,c_15572]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_15611,plain,
% 7.83/1.50      ( k1_relat_1(sK2) != k2_relat_1(sK3)
% 7.83/1.50      | k6_partfun1(k2_relat_1(sK2)) != k6_partfun1(sK1)
% 7.83/1.50      | k2_funct_1(sK2) = sK3
% 7.83/1.50      | v2_funct_1(sK2) != iProver_top
% 7.83/1.50      | v1_relat_1(sK3) != iProver_top
% 7.83/1.50      | v1_relat_1(sK2) != iProver_top
% 7.83/1.50      | v1_funct_1(sK3) != iProver_top
% 7.83/1.50      | v1_funct_1(sK2) != iProver_top ),
% 7.83/1.50      inference(superposition,[status(thm)],[c_15574,c_1526]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_15614,plain,
% 7.83/1.50      ( k1_relat_1(sK2) != sK0
% 7.83/1.50      | k6_partfun1(sK1) != k6_partfun1(sK1)
% 7.83/1.50      | k2_funct_1(sK2) = sK3
% 7.83/1.50      | v2_funct_1(sK2) != iProver_top
% 7.83/1.50      | v1_relat_1(sK3) != iProver_top
% 7.83/1.50      | v1_relat_1(sK2) != iProver_top
% 7.83/1.50      | v1_funct_1(sK3) != iProver_top
% 7.83/1.50      | v1_funct_1(sK2) != iProver_top ),
% 7.83/1.50      inference(light_normalisation,
% 7.83/1.50                [status(thm)],
% 7.83/1.50                [c_15611,c_2282,c_2283]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_15615,plain,
% 7.83/1.50      ( k1_relat_1(sK2) != sK0
% 7.83/1.50      | k2_funct_1(sK2) = sK3
% 7.83/1.50      | v2_funct_1(sK2) != iProver_top
% 7.83/1.50      | v1_relat_1(sK3) != iProver_top
% 7.83/1.50      | v1_relat_1(sK2) != iProver_top
% 7.83/1.50      | v1_funct_1(sK3) != iProver_top
% 7.83/1.50      | v1_funct_1(sK2) != iProver_top ),
% 7.83/1.50      inference(equality_resolution_simp,[status(thm)],[c_15614]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_4358,plain,
% 7.83/1.50      ( v1_funct_2(sK2,sK0,sK1) != iProver_top
% 7.83/1.50      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
% 7.83/1.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.83/1.50      | v2_funct_1(sK2) != iProver_top
% 7.83/1.50      | v1_funct_1(sK2) != iProver_top ),
% 7.83/1.50      inference(superposition,[status(thm)],[c_828,c_1538]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_2161,plain,
% 7.83/1.50      ( ~ v1_funct_2(X0_48,sK0,sK1)
% 7.83/1.50      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.83/1.50      | m1_subset_1(k2_funct_1(X0_48),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 7.83/1.50      | ~ v2_funct_1(X0_48)
% 7.83/1.50      | ~ v1_funct_1(X0_48)
% 7.83/1.50      | k2_relset_1(sK0,sK1,X0_48) != sK1 ),
% 7.83/1.50      inference(instantiation,[status(thm)],[c_836]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_2162,plain,
% 7.83/1.50      ( k2_relset_1(sK0,sK1,X0_48) != sK1
% 7.83/1.50      | v1_funct_2(X0_48,sK0,sK1) != iProver_top
% 7.83/1.50      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.83/1.50      | m1_subset_1(k2_funct_1(X0_48),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
% 7.83/1.50      | v2_funct_1(X0_48) != iProver_top
% 7.83/1.50      | v1_funct_1(X0_48) != iProver_top ),
% 7.83/1.50      inference(predicate_to_equality,[status(thm)],[c_2161]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_2164,plain,
% 7.83/1.50      ( k2_relset_1(sK0,sK1,sK2) != sK1
% 7.83/1.50      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 7.83/1.50      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
% 7.83/1.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.83/1.50      | v2_funct_1(sK2) != iProver_top
% 7.83/1.50      | v1_funct_1(sK2) != iProver_top ),
% 7.83/1.50      inference(instantiation,[status(thm)],[c_2162]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_4367,plain,
% 7.83/1.50      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 7.83/1.50      inference(global_propositional_subsumption,
% 7.83/1.50                [status(thm)],
% 7.83/1.50                [c_4358,c_45,c_46,c_47,c_52,c_828,c_2164]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_4376,plain,
% 7.83/1.50      ( k1_partfun1(X0_49,X1_49,sK1,sK0,X0_48,k2_funct_1(sK2)) = k5_relat_1(X0_48,k2_funct_1(sK2))
% 7.83/1.50      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 7.83/1.50      | v1_funct_1(X0_48) != iProver_top
% 7.83/1.50      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 7.83/1.50      inference(superposition,[status(thm)],[c_4367,c_1533]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_4682,plain,
% 7.83/1.50      ( v1_funct_1(X0_48) != iProver_top
% 7.83/1.50      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 7.83/1.50      | k1_partfun1(X0_49,X1_49,sK1,sK0,X0_48,k2_funct_1(sK2)) = k5_relat_1(X0_48,k2_funct_1(sK2)) ),
% 7.83/1.50      inference(global_propositional_subsumption,
% 7.83/1.50                [status(thm)],
% 7.83/1.50                [c_4376,c_45,c_47,c_902,c_1714]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_4683,plain,
% 7.83/1.50      ( k1_partfun1(X0_49,X1_49,sK1,sK0,X0_48,k2_funct_1(sK2)) = k5_relat_1(X0_48,k2_funct_1(sK2))
% 7.83/1.50      | m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))) != iProver_top
% 7.83/1.50      | v1_funct_1(X0_48) != iProver_top ),
% 7.83/1.50      inference(renaming,[status(thm)],[c_4682]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_4689,plain,
% 7.83/1.50      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2))
% 7.83/1.50      | v1_funct_1(sK2) != iProver_top ),
% 7.83/1.50      inference(superposition,[status(thm)],[c_1546,c_4683]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_5158,plain,
% 7.83/1.50      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
% 7.83/1.50      inference(global_propositional_subsumption,
% 7.83/1.50                [status(thm)],
% 7.83/1.50                [c_4689,c_45]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_5160,plain,
% 7.83/1.50      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
% 7.83/1.50      inference(light_normalisation,[status(thm)],[c_5158,c_4895]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_5161,plain,
% 7.83/1.50      ( k2_relset_1(sK1,sK0,k2_funct_1(sK2)) = sK0
% 7.83/1.50      | v1_funct_2(k2_funct_1(sK2),sK1,sK0) != iProver_top
% 7.83/1.50      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 7.83/1.50      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.83/1.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.83/1.50      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 7.83/1.50      | v1_funct_1(sK2) != iProver_top ),
% 7.83/1.50      inference(superposition,[status(thm)],[c_5160,c_1967]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_4374,plain,
% 7.83/1.50      ( k2_relset_1(sK1,sK0,k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 7.83/1.50      inference(superposition,[status(thm)],[c_4367,c_1529]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_7,plain,
% 7.83/1.50      ( ~ v2_funct_1(X0)
% 7.83/1.50      | ~ v1_relat_1(X0)
% 7.83/1.50      | ~ v1_funct_1(X0)
% 7.83/1.50      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 7.83/1.50      inference(cnf_transformation,[],[f69]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_854,plain,
% 7.83/1.50      ( ~ v2_funct_1(X0_48)
% 7.83/1.50      | ~ v1_relat_1(X0_48)
% 7.83/1.50      | ~ v1_funct_1(X0_48)
% 7.83/1.50      | k2_relat_1(k2_funct_1(X0_48)) = k1_relat_1(X0_48) ),
% 7.83/1.50      inference(subtyping,[status(esa)],[c_7]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_1520,plain,
% 7.83/1.50      ( k2_relat_1(k2_funct_1(X0_48)) = k1_relat_1(X0_48)
% 7.83/1.50      | v2_funct_1(X0_48) != iProver_top
% 7.83/1.50      | v1_relat_1(X0_48) != iProver_top
% 7.83/1.50      | v1_funct_1(X0_48) != iProver_top ),
% 7.83/1.50      inference(predicate_to_equality,[status(thm)],[c_854]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_2345,plain,
% 7.83/1.50      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 7.83/1.50      | v1_relat_1(sK2) != iProver_top
% 7.83/1.50      | v1_funct_1(sK2) != iProver_top ),
% 7.83/1.50      inference(superposition,[status(thm)],[c_1542,c_1520]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_916,plain,
% 7.83/1.50      ( ~ v2_funct_1(sK2)
% 7.83/1.50      | ~ v1_relat_1(sK2)
% 7.83/1.50      | ~ v1_funct_1(sK2)
% 7.83/1.50      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 7.83/1.50      inference(instantiation,[status(thm)],[c_854]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_2468,plain,
% 7.83/1.50      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 7.83/1.50      inference(global_propositional_subsumption,
% 7.83/1.50                [status(thm)],
% 7.83/1.50                [c_2345,c_44,c_42,c_36,c_916,c_1713]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_4377,plain,
% 7.83/1.50      ( k2_relset_1(sK1,sK0,k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 7.83/1.50      inference(light_normalisation,[status(thm)],[c_4374,c_2468]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_5165,plain,
% 7.83/1.50      ( k1_relat_1(sK2) = sK0
% 7.83/1.50      | v1_funct_2(k2_funct_1(sK2),sK1,sK0) != iProver_top
% 7.83/1.50      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 7.83/1.50      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.83/1.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.83/1.50      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 7.83/1.50      | v1_funct_1(sK2) != iProver_top ),
% 7.83/1.50      inference(demodulation,[status(thm)],[c_5161,c_4377]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_29,plain,
% 7.83/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.83/1.50      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 7.83/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.83/1.50      | ~ v2_funct_1(X0)
% 7.83/1.50      | ~ v1_funct_1(X0)
% 7.83/1.50      | k2_relset_1(X1,X2,X0) != X2 ),
% 7.83/1.50      inference(cnf_transformation,[],[f91]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_835,plain,
% 7.83/1.50      ( ~ v1_funct_2(X0_48,X0_49,X1_49)
% 7.83/1.50      | v1_funct_2(k2_funct_1(X0_48),X1_49,X0_49)
% 7.83/1.50      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49)))
% 7.83/1.50      | ~ v2_funct_1(X0_48)
% 7.83/1.50      | ~ v1_funct_1(X0_48)
% 7.83/1.50      | k2_relset_1(X0_49,X1_49,X0_48) != X1_49 ),
% 7.83/1.50      inference(subtyping,[status(esa)],[c_29]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_1796,plain,
% 7.83/1.50      ( ~ v1_funct_2(X0_48,sK0,X0_49)
% 7.83/1.50      | v1_funct_2(k2_funct_1(X0_48),X0_49,sK0)
% 7.83/1.50      | ~ m1_subset_1(X0_48,k1_zfmisc_1(k2_zfmisc_1(sK0,X0_49)))
% 7.83/1.50      | ~ v2_funct_1(X0_48)
% 7.83/1.50      | ~ v1_funct_1(X0_48)
% 7.83/1.50      | k2_relset_1(sK0,X0_49,X0_48) != X0_49 ),
% 7.83/1.50      inference(instantiation,[status(thm)],[c_835]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_2041,plain,
% 7.83/1.50      ( v1_funct_2(k2_funct_1(sK2),sK1,sK0)
% 7.83/1.50      | ~ v1_funct_2(sK2,sK0,sK1)
% 7.83/1.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.83/1.50      | ~ v2_funct_1(sK2)
% 7.83/1.50      | ~ v1_funct_1(sK2)
% 7.83/1.50      | k2_relset_1(sK0,sK1,sK2) != sK1 ),
% 7.83/1.50      inference(instantiation,[status(thm)],[c_1796]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_2042,plain,
% 7.83/1.50      ( k2_relset_1(sK0,sK1,sK2) != sK1
% 7.83/1.50      | v1_funct_2(k2_funct_1(sK2),sK1,sK0) = iProver_top
% 7.83/1.50      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 7.83/1.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.83/1.50      | v2_funct_1(sK2) != iProver_top
% 7.83/1.50      | v1_funct_1(sK2) != iProver_top ),
% 7.83/1.50      inference(predicate_to_equality,[status(thm)],[c_2041]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_33,negated_conjecture,
% 7.83/1.50      ( k2_funct_1(sK2) != sK3 ),
% 7.83/1.50      inference(cnf_transformation,[],[f106]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(c_832,negated_conjecture,
% 7.83/1.50      ( k2_funct_1(sK2) != sK3 ),
% 7.83/1.50      inference(subtyping,[status(esa)],[c_33]) ).
% 7.83/1.50  
% 7.83/1.50  cnf(contradiction,plain,
% 7.83/1.50      ( $false ),
% 7.83/1.50      inference(minisat,
% 7.83/1.50                [status(thm)],
% 7.83/1.50                [c_15615,c_5165,c_2164,c_2042,c_1950,c_1714,c_828,c_832,
% 7.83/1.50                 c_902,c_52,c_50,c_48,c_47,c_46,c_45]) ).
% 7.83/1.50  
% 7.83/1.50  
% 7.83/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.83/1.50  
% 7.83/1.50  ------                               Statistics
% 7.83/1.50  
% 7.83/1.50  ------ General
% 7.83/1.50  
% 7.83/1.50  abstr_ref_over_cycles:                  0
% 7.83/1.50  abstr_ref_under_cycles:                 0
% 7.83/1.50  gc_basic_clause_elim:                   0
% 7.83/1.50  forced_gc_time:                         0
% 7.83/1.50  parsing_time:                           0.011
% 7.83/1.50  unif_index_cands_time:                  0.
% 7.83/1.50  unif_index_add_time:                    0.
% 7.83/1.50  orderings_time:                         0.
% 7.83/1.50  out_proof_time:                         0.02
% 7.83/1.50  total_time:                             0.63
% 7.83/1.50  num_of_symbols:                         55
% 7.83/1.50  num_of_terms:                           20241
% 7.83/1.50  
% 7.83/1.50  ------ Preprocessing
% 7.83/1.50  
% 7.83/1.50  num_of_splits:                          0
% 7.83/1.50  num_of_split_atoms:                     0
% 7.83/1.50  num_of_reused_defs:                     0
% 7.83/1.50  num_eq_ax_congr_red:                    0
% 7.83/1.50  num_of_sem_filtered_clauses:            1
% 7.83/1.50  num_of_subtypes:                        4
% 7.83/1.50  monotx_restored_types:                  1
% 7.83/1.50  sat_num_of_epr_types:                   0
% 7.83/1.50  sat_num_of_non_cyclic_types:            0
% 7.83/1.50  sat_guarded_non_collapsed_types:        1
% 7.83/1.50  num_pure_diseq_elim:                    0
% 7.83/1.50  simp_replaced_by:                       0
% 7.83/1.50  res_preprocessed:                       210
% 7.83/1.50  prep_upred:                             0
% 7.83/1.50  prep_unflattend:                        12
% 7.83/1.50  smt_new_axioms:                         0
% 7.83/1.50  pred_elim_cands:                        5
% 7.83/1.50  pred_elim:                              1
% 7.83/1.50  pred_elim_cl:                           1
% 7.83/1.50  pred_elim_cycles:                       3
% 7.83/1.50  merged_defs:                            0
% 7.83/1.50  merged_defs_ncl:                        0
% 7.83/1.50  bin_hyper_res:                          0
% 7.83/1.50  prep_cycles:                            4
% 7.83/1.50  pred_elim_time:                         0.005
% 7.83/1.50  splitting_time:                         0.
% 7.83/1.50  sem_filter_time:                        0.
% 7.83/1.50  monotx_time:                            0.001
% 7.83/1.50  subtype_inf_time:                       0.003
% 7.83/1.50  
% 7.83/1.50  ------ Problem properties
% 7.83/1.50  
% 7.83/1.50  clauses:                                42
% 7.83/1.50  conjectures:                            11
% 7.83/1.50  epr:                                    7
% 7.83/1.50  horn:                                   38
% 7.83/1.50  ground:                                 12
% 7.83/1.50  unary:                                  12
% 7.83/1.50  binary:                                 3
% 7.83/1.50  lits:                                   176
% 7.83/1.50  lits_eq:                                35
% 7.83/1.50  fd_pure:                                0
% 7.83/1.50  fd_pseudo:                              0
% 7.83/1.50  fd_cond:                                4
% 7.83/1.50  fd_pseudo_cond:                         1
% 7.83/1.50  ac_symbols:                             0
% 7.83/1.50  
% 7.83/1.50  ------ Propositional Solver
% 7.83/1.50  
% 7.83/1.50  prop_solver_calls:                      34
% 7.83/1.50  prop_fast_solver_calls:                 2676
% 7.83/1.50  smt_solver_calls:                       0
% 7.83/1.50  smt_fast_solver_calls:                  0
% 7.83/1.50  prop_num_of_clauses:                    7023
% 7.83/1.50  prop_preprocess_simplified:             14481
% 7.83/1.50  prop_fo_subsumed:                       302
% 7.83/1.50  prop_solver_time:                       0.
% 7.83/1.50  smt_solver_time:                        0.
% 7.83/1.50  smt_fast_solver_time:                   0.
% 7.83/1.50  prop_fast_solver_time:                  0.
% 7.83/1.50  prop_unsat_core_time:                   0.001
% 7.83/1.50  
% 7.83/1.50  ------ QBF
% 7.83/1.50  
% 7.83/1.50  qbf_q_res:                              0
% 7.83/1.50  qbf_num_tautologies:                    0
% 7.83/1.50  qbf_prep_cycles:                        0
% 7.83/1.50  
% 7.83/1.50  ------ BMC1
% 7.83/1.50  
% 7.83/1.50  bmc1_current_bound:                     -1
% 7.83/1.50  bmc1_last_solved_bound:                 -1
% 7.83/1.50  bmc1_unsat_core_size:                   -1
% 7.83/1.50  bmc1_unsat_core_parents_size:           -1
% 7.83/1.50  bmc1_merge_next_fun:                    0
% 7.83/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.83/1.50  
% 7.83/1.50  ------ Instantiation
% 7.83/1.50  
% 7.83/1.50  inst_num_of_clauses:                    2214
% 7.83/1.50  inst_num_in_passive:                    887
% 7.83/1.50  inst_num_in_active:                     1056
% 7.83/1.50  inst_num_in_unprocessed:                271
% 7.83/1.50  inst_num_of_loops:                      1120
% 7.83/1.50  inst_num_of_learning_restarts:          0
% 7.83/1.50  inst_num_moves_active_passive:          57
% 7.83/1.50  inst_lit_activity:                      0
% 7.83/1.50  inst_lit_activity_moves:                0
% 7.83/1.50  inst_num_tautologies:                   0
% 7.83/1.50  inst_num_prop_implied:                  0
% 7.83/1.50  inst_num_existing_simplified:           0
% 7.83/1.50  inst_num_eq_res_simplified:             0
% 7.83/1.50  inst_num_child_elim:                    0
% 7.83/1.50  inst_num_of_dismatching_blockings:      1028
% 7.83/1.50  inst_num_of_non_proper_insts:           2434
% 7.83/1.50  inst_num_of_duplicates:                 0
% 7.83/1.50  inst_inst_num_from_inst_to_res:         0
% 7.83/1.50  inst_dismatching_checking_time:         0.
% 7.83/1.50  
% 7.83/1.50  ------ Resolution
% 7.83/1.50  
% 7.83/1.50  res_num_of_clauses:                     0
% 7.83/1.50  res_num_in_passive:                     0
% 7.83/1.50  res_num_in_active:                      0
% 7.83/1.50  res_num_of_loops:                       214
% 7.83/1.50  res_forward_subset_subsumed:            381
% 7.83/1.50  res_backward_subset_subsumed:           2
% 7.83/1.50  res_forward_subsumed:                   0
% 7.83/1.50  res_backward_subsumed:                  0
% 7.83/1.50  res_forward_subsumption_resolution:     2
% 7.83/1.50  res_backward_subsumption_resolution:    0
% 7.83/1.50  res_clause_to_clause_subsumption:       1053
% 7.83/1.50  res_orphan_elimination:                 0
% 7.83/1.50  res_tautology_del:                      212
% 7.83/1.50  res_num_eq_res_simplified:              1
% 7.83/1.50  res_num_sel_changes:                    0
% 7.83/1.50  res_moves_from_active_to_pass:          0
% 7.83/1.50  
% 7.83/1.50  ------ Superposition
% 7.83/1.50  
% 7.83/1.50  sup_time_total:                         0.
% 7.83/1.50  sup_time_generating:                    0.
% 7.83/1.50  sup_time_sim_full:                      0.
% 7.83/1.50  sup_time_sim_immed:                     0.
% 7.83/1.50  
% 7.83/1.50  sup_num_of_clauses:                     428
% 7.83/1.50  sup_num_in_active:                      171
% 7.83/1.50  sup_num_in_passive:                     257
% 7.83/1.50  sup_num_of_loops:                       223
% 7.83/1.50  sup_fw_superposition:                   236
% 7.83/1.50  sup_bw_superposition:                   314
% 7.83/1.50  sup_immediate_simplified:               158
% 7.83/1.50  sup_given_eliminated:                   6
% 7.83/1.50  comparisons_done:                       0
% 7.83/1.50  comparisons_avoided:                    0
% 7.83/1.50  
% 7.83/1.50  ------ Simplifications
% 7.83/1.50  
% 7.83/1.50  
% 7.83/1.50  sim_fw_subset_subsumed:                 28
% 7.83/1.50  sim_bw_subset_subsumed:                 34
% 7.83/1.50  sim_fw_subsumed:                        16
% 7.83/1.50  sim_bw_subsumed:                        11
% 7.83/1.50  sim_fw_subsumption_res:                 0
% 7.83/1.50  sim_bw_subsumption_res:                 0
% 7.83/1.50  sim_tautology_del:                      0
% 7.83/1.50  sim_eq_tautology_del:                   91
% 7.83/1.50  sim_eq_res_simp:                        3
% 7.83/1.50  sim_fw_demodulated:                     9
% 7.83/1.50  sim_bw_demodulated:                     34
% 7.83/1.50  sim_light_normalised:                   128
% 7.83/1.50  sim_joinable_taut:                      0
% 7.83/1.50  sim_joinable_simp:                      0
% 7.83/1.50  sim_ac_normalised:                      0
% 7.83/1.50  sim_smt_subsumption:                    0
% 7.83/1.50  
%------------------------------------------------------------------------------
