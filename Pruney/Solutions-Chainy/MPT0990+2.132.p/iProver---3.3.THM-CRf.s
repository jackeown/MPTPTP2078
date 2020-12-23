%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:25 EST 2020

% Result     : Theorem 27.97s
% Output     : CNFRefutation 27.97s
% Verified   : 
% Statistics : Number of formulae       :  217 (1869 expanded)
%              Number of clauses        :  124 ( 579 expanded)
%              Number of leaves         :   25 ( 470 expanded)
%              Depth                    :   24
%              Number of atoms          :  829 (15225 expanded)
%              Number of equality atoms :  401 (5665 expanded)
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

fof(f51,plain,(
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
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f51])).

fof(f57,plain,(
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

fof(f56,plain,
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

fof(f58,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f52,f57,f56])).

fof(f95,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f58])).

fof(f98,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f58])).

fof(f17,axiom,(
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
    inference(ennf_transformation,[],[f17])).

fof(f46,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f45])).

fof(f87,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f96,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f58])).

fof(f93,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f58])).

fof(f100,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f58])).

fof(f15,axiom,(
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
    inference(ennf_transformation,[],[f15])).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f43])).

fof(f85,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f37])).

fof(f53,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f16,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f86,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
              & k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f18,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f88,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f109,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f71,f88])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f41])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f19,axiom,(
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

fof(f47,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_funct_2(X3,X0)
      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f94,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f58])).

fof(f97,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
          & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f32,plain,(
    ! [X0] :
      ( ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f69,plain,(
    ! [X0] :
      ( k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f28,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f64,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f101,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f58])).

fof(f99,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f58])).

fof(f20,axiom,(
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

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

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
    inference(flattening,[],[f49])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f103,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f58])).

fof(f4,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f106,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f62,f88])).

fof(f13,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f54,plain,(
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
    inference(nnf_transformation,[],[f40])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f102,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f58])).

fof(f6,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f107,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f66,f88])).

fof(f7,axiom,(
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

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f7])).

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
    inference(flattening,[],[f29])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X0)
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f61,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f104,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_42,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1748,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_39,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1751,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1757,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_5501,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1751,c_1757])).

cnf(c_41,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_48,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_6060,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5501,c_48])).

cnf(c_6061,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_6060])).

cnf(c_6068,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1748,c_6061])).

cnf(c_44,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_45,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_6133,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6068,c_45])).

cnf(c_37,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1752,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_6135,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6133,c_1752])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1760,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_6172,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_6133,c_1760])).

cnf(c_47,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_50,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_8830,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6172,c_45,c_47,c_48,c_50])).

cnf(c_16,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1767,plain,
    ( X0 = X1
    | r2_relset_1(X2,X3,X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_8841,plain,
    ( k5_relat_1(sK2,sK3) = X0
    | r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8830,c_1767])).

cnf(c_10702,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6135,c_8841])).

cnf(c_27,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2182,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_2183,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2182])).

cnf(c_10753,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10702,c_2183])).

cnf(c_12,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
    | k2_funct_1(X0) = X1
    | k1_relat_1(X0) != k2_relat_1(X1) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1770,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k1_relat_1(X1) != k2_relat_1(X0)
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_10770,plain,
    ( k2_funct_1(sK3) = sK2
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_10753,c_1770])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1780,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3064,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1751,c_1780])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_3141,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3142,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3141])).

cnf(c_3367,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3064,c_3142])).

cnf(c_24,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_29,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | v2_funct_2(X3,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_484,plain,
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
    inference(resolution_lifted,[status(thm)],[c_24,c_29])).

cnf(c_485,plain,
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
    inference(unflattening,[status(thm)],[c_484])).

cnf(c_13,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_509,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X3)
    | k2_relat_1(X3) = X0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_485,c_13])).

cnf(c_1745,plain,
    ( k2_relat_1(X0) = X1
    | r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X0),k6_partfun1(X1)) != iProver_top
    | v1_funct_2(X3,X1,X2) != iProver_top
    | v1_funct_2(X0,X2,X1) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_509])).

cnf(c_2745,plain,
    ( k2_relat_1(sK3) = sK0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1752,c_1745])).

cnf(c_43,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_46,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_40,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_49,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_2748,plain,
    ( k2_relat_1(sK3) = sK0
    | v1_relat_1(sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2745,c_45,c_46,c_47,c_48,c_49,c_50])).

cnf(c_3372,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(superposition,[status(thm)],[c_3367,c_2748])).

cnf(c_1746,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_11,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1771,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4406,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1(sK2),sK2)) = k2_relat_1(sK2)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1746,c_1771])).

cnf(c_5,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1777,plain,
    ( k2_funct_1(X0) = k4_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3544,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1746,c_1777])).

cnf(c_36,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_52,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_1779,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3065,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1748,c_1780])).

cnf(c_3429,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1779,c_3065])).

cnf(c_3680,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3544,c_52,c_3429])).

cnf(c_38,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_31,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1755,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_3477,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_38,c_1755])).

cnf(c_34,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1846,plain,
    ( ~ v1_funct_2(X0,X1,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,sK1,X0) != sK1
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_2040,plain,
    ( ~ v1_funct_2(sK2,X0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(X0,sK1,sK2) != sK1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1846])).

cnf(c_2124,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(sK0,sK1,sK2) != sK1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_2040])).

cnf(c_3605,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3477,c_44,c_43,c_42,c_38,c_36,c_34,c_2124])).

cnf(c_3682,plain,
    ( k5_relat_1(k4_relat_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(demodulation,[status(thm)],[c_3680,c_3605])).

cnf(c_4407,plain,
    ( k1_relat_1(k6_partfun1(sK1)) = k2_relat_1(sK2)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4406,c_3680,c_3682])).

cnf(c_4,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f106])).

cnf(c_4408,plain,
    ( k2_relat_1(sK2) = sK1
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4407,c_4])).

cnf(c_4544,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4408,c_52,c_3429])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1761,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_5514,plain,
    ( k1_relset_1(sK1,sK0,sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1751,c_1761])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1769,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2921,plain,
    ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1751,c_1769])).

cnf(c_5517,plain,
    ( k1_relat_1(sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5514,c_2921])).

cnf(c_35,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1153,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1190,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1153])).

cnf(c_1154,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1899,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1154])).

cnf(c_1900,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1899])).

cnf(c_10261,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5517,c_49,c_35,c_1190,c_1900])).

cnf(c_10771,plain,
    ( k2_funct_1(sK3) = sK2
    | k6_partfun1(sK0) != k6_partfun1(sK0)
    | sK1 != sK1
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10770,c_3372,c_4544,c_10261])).

cnf(c_10772,plain,
    ( k2_funct_1(sK3) = sK2
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_10771])).

cnf(c_6,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_8910,plain,
    ( v2_funct_1(k6_partfun1(sK0)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_8911,plain,
    ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8910])).

cnf(c_8,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | v2_funct_1(X0)
    | ~ v2_funct_1(k5_relat_1(X1,X0))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_relat_1(X0) != k2_relat_1(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1774,plain,
    ( k1_relat_1(X0) != k2_relat_1(X1)
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k5_relat_1(X1,X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_10265,plain,
    ( k2_relat_1(X0) != sK1
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_10261,c_1774])).

cnf(c_57153,plain,
    ( v1_relat_1(X0) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
    | k2_relat_1(X0) != sK1
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10265,c_48,c_3064,c_3142])).

cnf(c_57154,plain,
    ( k2_relat_1(X0) != sK1
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_57153])).

cnf(c_57160,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4544,c_57154])).

cnf(c_57163,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_57160,c_10753])).

cnf(c_87476,plain,
    ( k2_funct_1(sK3) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10772,c_45,c_48,c_3064,c_3142,c_3429,c_8911,c_57163])).

cnf(c_57171,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_57163,c_45,c_3429,c_8911])).

cnf(c_1749,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_3543,plain,
    ( k2_funct_1(sK3) = k4_relat_1(sK3)
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1749,c_1777])).

cnf(c_3675,plain,
    ( v2_funct_1(sK3) != iProver_top
    | k2_funct_1(sK3) = k4_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3543,c_3064,c_3142])).

cnf(c_3676,plain,
    ( k2_funct_1(sK3) = k4_relat_1(sK3)
    | v2_funct_1(sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_3675])).

cnf(c_57177,plain,
    ( k2_funct_1(sK3) = k4_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_57171,c_3676])).

cnf(c_87478,plain,
    ( k4_relat_1(sK3) = sK2 ),
    inference(demodulation,[status(thm)],[c_87476,c_57177])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | k4_relat_1(k4_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1778,plain,
    ( k4_relat_1(k4_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3371,plain,
    ( k4_relat_1(k4_relat_1(sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_3367,c_1778])).

cnf(c_87556,plain,
    ( k4_relat_1(sK2) = sK3 ),
    inference(demodulation,[status(thm)],[c_87478,c_3371])).

cnf(c_33,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_3684,plain,
    ( k4_relat_1(sK2) != sK3 ),
    inference(demodulation,[status(thm)],[c_3680,c_33])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_87556,c_3684])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:21:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 27.97/4.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.97/4.00  
% 27.97/4.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.97/4.00  
% 27.97/4.00  ------  iProver source info
% 27.97/4.00  
% 27.97/4.00  git: date: 2020-06-30 10:37:57 +0100
% 27.97/4.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.97/4.00  git: non_committed_changes: false
% 27.97/4.00  git: last_make_outside_of_git: false
% 27.97/4.00  
% 27.97/4.00  ------ 
% 27.97/4.00  
% 27.97/4.00  ------ Input Options
% 27.97/4.00  
% 27.97/4.00  --out_options                           all
% 27.97/4.00  --tptp_safe_out                         true
% 27.97/4.00  --problem_path                          ""
% 27.97/4.00  --include_path                          ""
% 27.97/4.00  --clausifier                            res/vclausify_rel
% 27.97/4.00  --clausifier_options                    ""
% 27.97/4.00  --stdin                                 false
% 27.97/4.00  --stats_out                             all
% 27.97/4.00  
% 27.97/4.00  ------ General Options
% 27.97/4.00  
% 27.97/4.00  --fof                                   false
% 27.97/4.00  --time_out_real                         305.
% 27.97/4.00  --time_out_virtual                      -1.
% 27.97/4.00  --symbol_type_check                     false
% 27.97/4.00  --clausify_out                          false
% 27.97/4.00  --sig_cnt_out                           false
% 27.97/4.00  --trig_cnt_out                          false
% 27.97/4.00  --trig_cnt_out_tolerance                1.
% 27.97/4.00  --trig_cnt_out_sk_spl                   false
% 27.97/4.00  --abstr_cl_out                          false
% 27.97/4.00  
% 27.97/4.00  ------ Global Options
% 27.97/4.00  
% 27.97/4.00  --schedule                              default
% 27.97/4.00  --add_important_lit                     false
% 27.97/4.00  --prop_solver_per_cl                    1000
% 27.97/4.00  --min_unsat_core                        false
% 27.97/4.00  --soft_assumptions                      false
% 27.97/4.00  --soft_lemma_size                       3
% 27.97/4.00  --prop_impl_unit_size                   0
% 27.97/4.00  --prop_impl_unit                        []
% 27.97/4.00  --share_sel_clauses                     true
% 27.97/4.00  --reset_solvers                         false
% 27.97/4.00  --bc_imp_inh                            [conj_cone]
% 27.97/4.00  --conj_cone_tolerance                   3.
% 27.97/4.00  --extra_neg_conj                        none
% 27.97/4.00  --large_theory_mode                     true
% 27.97/4.00  --prolific_symb_bound                   200
% 27.97/4.00  --lt_threshold                          2000
% 27.97/4.00  --clause_weak_htbl                      true
% 27.97/4.00  --gc_record_bc_elim                     false
% 27.97/4.00  
% 27.97/4.00  ------ Preprocessing Options
% 27.97/4.00  
% 27.97/4.00  --preprocessing_flag                    true
% 27.97/4.00  --time_out_prep_mult                    0.1
% 27.97/4.00  --splitting_mode                        input
% 27.97/4.00  --splitting_grd                         true
% 27.97/4.00  --splitting_cvd                         false
% 27.97/4.00  --splitting_cvd_svl                     false
% 27.97/4.00  --splitting_nvd                         32
% 27.97/4.00  --sub_typing                            true
% 27.97/4.00  --prep_gs_sim                           true
% 27.97/4.00  --prep_unflatten                        true
% 27.97/4.00  --prep_res_sim                          true
% 27.97/4.00  --prep_upred                            true
% 27.97/4.00  --prep_sem_filter                       exhaustive
% 27.97/4.00  --prep_sem_filter_out                   false
% 27.97/4.00  --pred_elim                             true
% 27.97/4.00  --res_sim_input                         true
% 27.97/4.00  --eq_ax_congr_red                       true
% 27.97/4.00  --pure_diseq_elim                       true
% 27.97/4.00  --brand_transform                       false
% 27.97/4.00  --non_eq_to_eq                          false
% 27.97/4.00  --prep_def_merge                        true
% 27.97/4.00  --prep_def_merge_prop_impl              false
% 27.97/4.00  --prep_def_merge_mbd                    true
% 27.97/4.00  --prep_def_merge_tr_red                 false
% 27.97/4.00  --prep_def_merge_tr_cl                  false
% 27.97/4.00  --smt_preprocessing                     true
% 27.97/4.00  --smt_ac_axioms                         fast
% 27.97/4.00  --preprocessed_out                      false
% 27.97/4.00  --preprocessed_stats                    false
% 27.97/4.00  
% 27.97/4.00  ------ Abstraction refinement Options
% 27.97/4.00  
% 27.97/4.00  --abstr_ref                             []
% 27.97/4.00  --abstr_ref_prep                        false
% 27.97/4.00  --abstr_ref_until_sat                   false
% 27.97/4.00  --abstr_ref_sig_restrict                funpre
% 27.97/4.00  --abstr_ref_af_restrict_to_split_sk     false
% 27.97/4.00  --abstr_ref_under                       []
% 27.97/4.00  
% 27.97/4.00  ------ SAT Options
% 27.97/4.00  
% 27.97/4.00  --sat_mode                              false
% 27.97/4.00  --sat_fm_restart_options                ""
% 27.97/4.00  --sat_gr_def                            false
% 27.97/4.00  --sat_epr_types                         true
% 27.97/4.00  --sat_non_cyclic_types                  false
% 27.97/4.00  --sat_finite_models                     false
% 27.97/4.00  --sat_fm_lemmas                         false
% 27.97/4.00  --sat_fm_prep                           false
% 27.97/4.00  --sat_fm_uc_incr                        true
% 27.97/4.00  --sat_out_model                         small
% 27.97/4.00  --sat_out_clauses                       false
% 27.97/4.00  
% 27.97/4.00  ------ QBF Options
% 27.97/4.00  
% 27.97/4.00  --qbf_mode                              false
% 27.97/4.00  --qbf_elim_univ                         false
% 27.97/4.00  --qbf_dom_inst                          none
% 27.97/4.00  --qbf_dom_pre_inst                      false
% 27.97/4.00  --qbf_sk_in                             false
% 27.97/4.00  --qbf_pred_elim                         true
% 27.97/4.00  --qbf_split                             512
% 27.97/4.00  
% 27.97/4.00  ------ BMC1 Options
% 27.97/4.00  
% 27.97/4.00  --bmc1_incremental                      false
% 27.97/4.00  --bmc1_axioms                           reachable_all
% 27.97/4.00  --bmc1_min_bound                        0
% 27.97/4.00  --bmc1_max_bound                        -1
% 27.97/4.00  --bmc1_max_bound_default                -1
% 27.97/4.00  --bmc1_symbol_reachability              true
% 27.97/4.00  --bmc1_property_lemmas                  false
% 27.97/4.00  --bmc1_k_induction                      false
% 27.97/4.00  --bmc1_non_equiv_states                 false
% 27.97/4.00  --bmc1_deadlock                         false
% 27.97/4.00  --bmc1_ucm                              false
% 27.97/4.00  --bmc1_add_unsat_core                   none
% 27.97/4.00  --bmc1_unsat_core_children              false
% 27.97/4.00  --bmc1_unsat_core_extrapolate_axioms    false
% 27.97/4.00  --bmc1_out_stat                         full
% 27.97/4.00  --bmc1_ground_init                      false
% 27.97/4.00  --bmc1_pre_inst_next_state              false
% 27.97/4.00  --bmc1_pre_inst_state                   false
% 27.97/4.00  --bmc1_pre_inst_reach_state             false
% 27.97/4.00  --bmc1_out_unsat_core                   false
% 27.97/4.00  --bmc1_aig_witness_out                  false
% 27.97/4.00  --bmc1_verbose                          false
% 27.97/4.00  --bmc1_dump_clauses_tptp                false
% 27.97/4.00  --bmc1_dump_unsat_core_tptp             false
% 27.97/4.00  --bmc1_dump_file                        -
% 27.97/4.00  --bmc1_ucm_expand_uc_limit              128
% 27.97/4.00  --bmc1_ucm_n_expand_iterations          6
% 27.97/4.00  --bmc1_ucm_extend_mode                  1
% 27.97/4.00  --bmc1_ucm_init_mode                    2
% 27.97/4.00  --bmc1_ucm_cone_mode                    none
% 27.97/4.00  --bmc1_ucm_reduced_relation_type        0
% 27.97/4.00  --bmc1_ucm_relax_model                  4
% 27.97/4.00  --bmc1_ucm_full_tr_after_sat            true
% 27.97/4.00  --bmc1_ucm_expand_neg_assumptions       false
% 27.97/4.00  --bmc1_ucm_layered_model                none
% 27.97/4.00  --bmc1_ucm_max_lemma_size               10
% 27.97/4.00  
% 27.97/4.00  ------ AIG Options
% 27.97/4.00  
% 27.97/4.00  --aig_mode                              false
% 27.97/4.00  
% 27.97/4.00  ------ Instantiation Options
% 27.97/4.00  
% 27.97/4.00  --instantiation_flag                    true
% 27.97/4.00  --inst_sos_flag                         true
% 27.97/4.00  --inst_sos_phase                        true
% 27.97/4.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.97/4.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.97/4.00  --inst_lit_sel_side                     num_symb
% 27.97/4.00  --inst_solver_per_active                1400
% 27.97/4.00  --inst_solver_calls_frac                1.
% 27.97/4.00  --inst_passive_queue_type               priority_queues
% 27.97/4.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.97/4.00  --inst_passive_queues_freq              [25;2]
% 27.97/4.00  --inst_dismatching                      true
% 27.97/4.00  --inst_eager_unprocessed_to_passive     true
% 27.97/4.00  --inst_prop_sim_given                   true
% 27.97/4.00  --inst_prop_sim_new                     false
% 27.97/4.00  --inst_subs_new                         false
% 27.97/4.00  --inst_eq_res_simp                      false
% 27.97/4.00  --inst_subs_given                       false
% 27.97/4.00  --inst_orphan_elimination               true
% 27.97/4.00  --inst_learning_loop_flag               true
% 27.97/4.00  --inst_learning_start                   3000
% 27.97/4.00  --inst_learning_factor                  2
% 27.97/4.00  --inst_start_prop_sim_after_learn       3
% 27.97/4.00  --inst_sel_renew                        solver
% 27.97/4.00  --inst_lit_activity_flag                true
% 27.97/4.00  --inst_restr_to_given                   false
% 27.97/4.00  --inst_activity_threshold               500
% 27.97/4.00  --inst_out_proof                        true
% 27.97/4.00  
% 27.97/4.00  ------ Resolution Options
% 27.97/4.00  
% 27.97/4.00  --resolution_flag                       true
% 27.97/4.00  --res_lit_sel                           adaptive
% 27.97/4.00  --res_lit_sel_side                      none
% 27.97/4.00  --res_ordering                          kbo
% 27.97/4.00  --res_to_prop_solver                    active
% 27.97/4.00  --res_prop_simpl_new                    false
% 27.97/4.00  --res_prop_simpl_given                  true
% 27.97/4.00  --res_passive_queue_type                priority_queues
% 27.97/4.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.97/4.00  --res_passive_queues_freq               [15;5]
% 27.97/4.00  --res_forward_subs                      full
% 27.97/4.00  --res_backward_subs                     full
% 27.97/4.00  --res_forward_subs_resolution           true
% 27.97/4.00  --res_backward_subs_resolution          true
% 27.97/4.00  --res_orphan_elimination                true
% 27.97/4.00  --res_time_limit                        2.
% 27.97/4.00  --res_out_proof                         true
% 27.97/4.00  
% 27.97/4.00  ------ Superposition Options
% 27.97/4.00  
% 27.97/4.00  --superposition_flag                    true
% 27.97/4.00  --sup_passive_queue_type                priority_queues
% 27.97/4.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.97/4.00  --sup_passive_queues_freq               [8;1;4]
% 27.97/4.00  --demod_completeness_check              fast
% 27.97/4.00  --demod_use_ground                      true
% 27.97/4.00  --sup_to_prop_solver                    passive
% 27.97/4.00  --sup_prop_simpl_new                    true
% 27.97/4.00  --sup_prop_simpl_given                  true
% 27.97/4.00  --sup_fun_splitting                     true
% 27.97/4.00  --sup_smt_interval                      50000
% 27.97/4.00  
% 27.97/4.00  ------ Superposition Simplification Setup
% 27.97/4.00  
% 27.97/4.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 27.97/4.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 27.97/4.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 27.97/4.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 27.97/4.00  --sup_full_triv                         [TrivRules;PropSubs]
% 27.97/4.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 27.97/4.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 27.97/4.00  --sup_immed_triv                        [TrivRules]
% 27.97/4.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.97/4.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.97/4.00  --sup_immed_bw_main                     []
% 27.97/4.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 27.97/4.00  --sup_input_triv                        [Unflattening;TrivRules]
% 27.97/4.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.97/4.00  --sup_input_bw                          []
% 27.97/4.00  
% 27.97/4.00  ------ Combination Options
% 27.97/4.00  
% 27.97/4.00  --comb_res_mult                         3
% 27.97/4.00  --comb_sup_mult                         2
% 27.97/4.00  --comb_inst_mult                        10
% 27.97/4.00  
% 27.97/4.00  ------ Debug Options
% 27.97/4.00  
% 27.97/4.00  --dbg_backtrace                         false
% 27.97/4.00  --dbg_dump_prop_clauses                 false
% 27.97/4.00  --dbg_dump_prop_clauses_file            -
% 27.97/4.00  --dbg_out_stat                          false
% 27.97/4.00  ------ Parsing...
% 27.97/4.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.97/4.00  
% 27.97/4.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 27.97/4.00  
% 27.97/4.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.97/4.00  
% 27.97/4.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.97/4.00  ------ Proving...
% 27.97/4.00  ------ Problem Properties 
% 27.97/4.00  
% 27.97/4.00  
% 27.97/4.00  clauses                                 42
% 27.97/4.00  conjectures                             12
% 27.97/4.00  EPR                                     7
% 27.97/4.00  Horn                                    36
% 27.97/4.00  unary                                   18
% 27.97/4.00  binary                                  3
% 27.97/4.00  lits                                    132
% 27.97/4.00  lits eq                                 34
% 27.97/4.00  fd_pure                                 0
% 27.97/4.00  fd_pseudo                               0
% 27.97/4.00  fd_cond                                 5
% 27.97/4.00  fd_pseudo_cond                          3
% 27.97/4.00  AC symbols                              0
% 27.97/4.00  
% 27.97/4.00  ------ Schedule dynamic 5 is on 
% 27.97/4.00  
% 27.97/4.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 27.97/4.00  
% 27.97/4.00  
% 27.97/4.00  ------ 
% 27.97/4.00  Current options:
% 27.97/4.00  ------ 
% 27.97/4.00  
% 27.97/4.00  ------ Input Options
% 27.97/4.00  
% 27.97/4.00  --out_options                           all
% 27.97/4.00  --tptp_safe_out                         true
% 27.97/4.00  --problem_path                          ""
% 27.97/4.00  --include_path                          ""
% 27.97/4.00  --clausifier                            res/vclausify_rel
% 27.97/4.00  --clausifier_options                    ""
% 27.97/4.00  --stdin                                 false
% 27.97/4.00  --stats_out                             all
% 27.97/4.00  
% 27.97/4.00  ------ General Options
% 27.97/4.00  
% 27.97/4.00  --fof                                   false
% 27.97/4.00  --time_out_real                         305.
% 27.97/4.00  --time_out_virtual                      -1.
% 27.97/4.00  --symbol_type_check                     false
% 27.97/4.00  --clausify_out                          false
% 27.97/4.00  --sig_cnt_out                           false
% 27.97/4.00  --trig_cnt_out                          false
% 27.97/4.00  --trig_cnt_out_tolerance                1.
% 27.97/4.00  --trig_cnt_out_sk_spl                   false
% 27.97/4.00  --abstr_cl_out                          false
% 27.97/4.00  
% 27.97/4.00  ------ Global Options
% 27.97/4.00  
% 27.97/4.00  --schedule                              default
% 27.97/4.00  --add_important_lit                     false
% 27.97/4.00  --prop_solver_per_cl                    1000
% 27.97/4.00  --min_unsat_core                        false
% 27.97/4.00  --soft_assumptions                      false
% 27.97/4.00  --soft_lemma_size                       3
% 27.97/4.00  --prop_impl_unit_size                   0
% 27.97/4.00  --prop_impl_unit                        []
% 27.97/4.00  --share_sel_clauses                     true
% 27.97/4.00  --reset_solvers                         false
% 27.97/4.00  --bc_imp_inh                            [conj_cone]
% 27.97/4.00  --conj_cone_tolerance                   3.
% 27.97/4.00  --extra_neg_conj                        none
% 27.97/4.00  --large_theory_mode                     true
% 27.97/4.00  --prolific_symb_bound                   200
% 27.97/4.00  --lt_threshold                          2000
% 27.97/4.00  --clause_weak_htbl                      true
% 27.97/4.00  --gc_record_bc_elim                     false
% 27.97/4.00  
% 27.97/4.00  ------ Preprocessing Options
% 27.97/4.00  
% 27.97/4.00  --preprocessing_flag                    true
% 27.97/4.00  --time_out_prep_mult                    0.1
% 27.97/4.00  --splitting_mode                        input
% 27.97/4.00  --splitting_grd                         true
% 27.97/4.00  --splitting_cvd                         false
% 27.97/4.00  --splitting_cvd_svl                     false
% 27.97/4.00  --splitting_nvd                         32
% 27.97/4.00  --sub_typing                            true
% 27.97/4.00  --prep_gs_sim                           true
% 27.97/4.00  --prep_unflatten                        true
% 27.97/4.00  --prep_res_sim                          true
% 27.97/4.00  --prep_upred                            true
% 27.97/4.00  --prep_sem_filter                       exhaustive
% 27.97/4.00  --prep_sem_filter_out                   false
% 27.97/4.00  --pred_elim                             true
% 27.97/4.00  --res_sim_input                         true
% 27.97/4.00  --eq_ax_congr_red                       true
% 27.97/4.00  --pure_diseq_elim                       true
% 27.97/4.00  --brand_transform                       false
% 27.97/4.00  --non_eq_to_eq                          false
% 27.97/4.00  --prep_def_merge                        true
% 27.97/4.00  --prep_def_merge_prop_impl              false
% 27.97/4.00  --prep_def_merge_mbd                    true
% 27.97/4.00  --prep_def_merge_tr_red                 false
% 27.97/4.00  --prep_def_merge_tr_cl                  false
% 27.97/4.00  --smt_preprocessing                     true
% 27.97/4.00  --smt_ac_axioms                         fast
% 27.97/4.00  --preprocessed_out                      false
% 27.97/4.00  --preprocessed_stats                    false
% 27.97/4.00  
% 27.97/4.00  ------ Abstraction refinement Options
% 27.97/4.00  
% 27.97/4.00  --abstr_ref                             []
% 27.97/4.00  --abstr_ref_prep                        false
% 27.97/4.00  --abstr_ref_until_sat                   false
% 27.97/4.00  --abstr_ref_sig_restrict                funpre
% 27.97/4.00  --abstr_ref_af_restrict_to_split_sk     false
% 27.97/4.00  --abstr_ref_under                       []
% 27.97/4.00  
% 27.97/4.00  ------ SAT Options
% 27.97/4.00  
% 27.97/4.00  --sat_mode                              false
% 27.97/4.00  --sat_fm_restart_options                ""
% 27.97/4.00  --sat_gr_def                            false
% 27.97/4.00  --sat_epr_types                         true
% 27.97/4.00  --sat_non_cyclic_types                  false
% 27.97/4.00  --sat_finite_models                     false
% 27.97/4.00  --sat_fm_lemmas                         false
% 27.97/4.00  --sat_fm_prep                           false
% 27.97/4.00  --sat_fm_uc_incr                        true
% 27.97/4.00  --sat_out_model                         small
% 27.97/4.00  --sat_out_clauses                       false
% 27.97/4.00  
% 27.97/4.00  ------ QBF Options
% 27.97/4.00  
% 27.97/4.00  --qbf_mode                              false
% 27.97/4.00  --qbf_elim_univ                         false
% 27.97/4.00  --qbf_dom_inst                          none
% 27.97/4.00  --qbf_dom_pre_inst                      false
% 27.97/4.00  --qbf_sk_in                             false
% 27.97/4.00  --qbf_pred_elim                         true
% 27.97/4.00  --qbf_split                             512
% 27.97/4.00  
% 27.97/4.00  ------ BMC1 Options
% 27.97/4.00  
% 27.97/4.00  --bmc1_incremental                      false
% 27.97/4.00  --bmc1_axioms                           reachable_all
% 27.97/4.00  --bmc1_min_bound                        0
% 27.97/4.00  --bmc1_max_bound                        -1
% 27.97/4.00  --bmc1_max_bound_default                -1
% 27.97/4.00  --bmc1_symbol_reachability              true
% 27.97/4.00  --bmc1_property_lemmas                  false
% 27.97/4.00  --bmc1_k_induction                      false
% 27.97/4.00  --bmc1_non_equiv_states                 false
% 27.97/4.00  --bmc1_deadlock                         false
% 27.97/4.00  --bmc1_ucm                              false
% 27.97/4.00  --bmc1_add_unsat_core                   none
% 27.97/4.00  --bmc1_unsat_core_children              false
% 27.97/4.00  --bmc1_unsat_core_extrapolate_axioms    false
% 27.97/4.00  --bmc1_out_stat                         full
% 27.97/4.00  --bmc1_ground_init                      false
% 27.97/4.00  --bmc1_pre_inst_next_state              false
% 27.97/4.00  --bmc1_pre_inst_state                   false
% 27.97/4.00  --bmc1_pre_inst_reach_state             false
% 27.97/4.00  --bmc1_out_unsat_core                   false
% 27.97/4.00  --bmc1_aig_witness_out                  false
% 27.97/4.00  --bmc1_verbose                          false
% 27.97/4.00  --bmc1_dump_clauses_tptp                false
% 27.97/4.00  --bmc1_dump_unsat_core_tptp             false
% 27.97/4.00  --bmc1_dump_file                        -
% 27.97/4.00  --bmc1_ucm_expand_uc_limit              128
% 27.97/4.00  --bmc1_ucm_n_expand_iterations          6
% 27.97/4.00  --bmc1_ucm_extend_mode                  1
% 27.97/4.00  --bmc1_ucm_init_mode                    2
% 27.97/4.00  --bmc1_ucm_cone_mode                    none
% 27.97/4.00  --bmc1_ucm_reduced_relation_type        0
% 27.97/4.00  --bmc1_ucm_relax_model                  4
% 27.97/4.00  --bmc1_ucm_full_tr_after_sat            true
% 27.97/4.00  --bmc1_ucm_expand_neg_assumptions       false
% 27.97/4.00  --bmc1_ucm_layered_model                none
% 27.97/4.00  --bmc1_ucm_max_lemma_size               10
% 27.97/4.00  
% 27.97/4.00  ------ AIG Options
% 27.97/4.00  
% 27.97/4.00  --aig_mode                              false
% 27.97/4.00  
% 27.97/4.00  ------ Instantiation Options
% 27.97/4.00  
% 27.97/4.00  --instantiation_flag                    true
% 27.97/4.00  --inst_sos_flag                         true
% 27.97/4.00  --inst_sos_phase                        true
% 27.97/4.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.97/4.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.97/4.00  --inst_lit_sel_side                     none
% 27.97/4.00  --inst_solver_per_active                1400
% 27.97/4.00  --inst_solver_calls_frac                1.
% 27.97/4.00  --inst_passive_queue_type               priority_queues
% 27.97/4.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.97/4.00  --inst_passive_queues_freq              [25;2]
% 27.97/4.00  --inst_dismatching                      true
% 27.97/4.00  --inst_eager_unprocessed_to_passive     true
% 27.97/4.00  --inst_prop_sim_given                   true
% 27.97/4.00  --inst_prop_sim_new                     false
% 27.97/4.00  --inst_subs_new                         false
% 27.97/4.00  --inst_eq_res_simp                      false
% 27.97/4.00  --inst_subs_given                       false
% 27.97/4.00  --inst_orphan_elimination               true
% 27.97/4.00  --inst_learning_loop_flag               true
% 27.97/4.00  --inst_learning_start                   3000
% 27.97/4.00  --inst_learning_factor                  2
% 27.97/4.00  --inst_start_prop_sim_after_learn       3
% 27.97/4.00  --inst_sel_renew                        solver
% 27.97/4.00  --inst_lit_activity_flag                true
% 27.97/4.00  --inst_restr_to_given                   false
% 27.97/4.00  --inst_activity_threshold               500
% 27.97/4.00  --inst_out_proof                        true
% 27.97/4.00  
% 27.97/4.00  ------ Resolution Options
% 27.97/4.00  
% 27.97/4.00  --resolution_flag                       false
% 27.97/4.00  --res_lit_sel                           adaptive
% 27.97/4.00  --res_lit_sel_side                      none
% 27.97/4.00  --res_ordering                          kbo
% 27.97/4.00  --res_to_prop_solver                    active
% 27.97/4.00  --res_prop_simpl_new                    false
% 27.97/4.00  --res_prop_simpl_given                  true
% 27.97/4.00  --res_passive_queue_type                priority_queues
% 27.97/4.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.97/4.00  --res_passive_queues_freq               [15;5]
% 27.97/4.00  --res_forward_subs                      full
% 27.97/4.00  --res_backward_subs                     full
% 27.97/4.00  --res_forward_subs_resolution           true
% 27.97/4.00  --res_backward_subs_resolution          true
% 27.97/4.00  --res_orphan_elimination                true
% 27.97/4.00  --res_time_limit                        2.
% 27.97/4.00  --res_out_proof                         true
% 27.97/4.00  
% 27.97/4.00  ------ Superposition Options
% 27.97/4.00  
% 27.97/4.00  --superposition_flag                    true
% 27.97/4.00  --sup_passive_queue_type                priority_queues
% 27.97/4.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.97/4.00  --sup_passive_queues_freq               [8;1;4]
% 27.97/4.00  --demod_completeness_check              fast
% 27.97/4.00  --demod_use_ground                      true
% 27.97/4.00  --sup_to_prop_solver                    passive
% 27.97/4.00  --sup_prop_simpl_new                    true
% 27.97/4.00  --sup_prop_simpl_given                  true
% 27.97/4.00  --sup_fun_splitting                     true
% 27.97/4.00  --sup_smt_interval                      50000
% 27.97/4.00  
% 27.97/4.00  ------ Superposition Simplification Setup
% 27.97/4.00  
% 27.97/4.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 27.97/4.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 27.97/4.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 27.97/4.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 27.97/4.00  --sup_full_triv                         [TrivRules;PropSubs]
% 27.97/4.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 27.97/4.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 27.97/4.00  --sup_immed_triv                        [TrivRules]
% 27.97/4.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.97/4.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.97/4.00  --sup_immed_bw_main                     []
% 27.97/4.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 27.97/4.00  --sup_input_triv                        [Unflattening;TrivRules]
% 27.97/4.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.97/4.00  --sup_input_bw                          []
% 27.97/4.00  
% 27.97/4.00  ------ Combination Options
% 27.97/4.00  
% 27.97/4.00  --comb_res_mult                         3
% 27.97/4.00  --comb_sup_mult                         2
% 27.97/4.00  --comb_inst_mult                        10
% 27.97/4.00  
% 27.97/4.00  ------ Debug Options
% 27.97/4.00  
% 27.97/4.00  --dbg_backtrace                         false
% 27.97/4.00  --dbg_dump_prop_clauses                 false
% 27.97/4.00  --dbg_dump_prop_clauses_file            -
% 27.97/4.00  --dbg_out_stat                          false
% 27.97/4.00  
% 27.97/4.00  
% 27.97/4.00  
% 27.97/4.00  
% 27.97/4.00  ------ Proving...
% 27.97/4.00  
% 27.97/4.00  
% 27.97/4.00  % SZS status Theorem for theBenchmark.p
% 27.97/4.00  
% 27.97/4.00  % SZS output start CNFRefutation for theBenchmark.p
% 27.97/4.00  
% 27.97/4.00  fof(f21,conjecture,(
% 27.97/4.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 27.97/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.97/4.00  
% 27.97/4.00  fof(f22,negated_conjecture,(
% 27.97/4.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 27.97/4.00    inference(negated_conjecture,[],[f21])).
% 27.97/4.00  
% 27.97/4.00  fof(f51,plain,(
% 27.97/4.00    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 27.97/4.00    inference(ennf_transformation,[],[f22])).
% 27.97/4.00  
% 27.97/4.00  fof(f52,plain,(
% 27.97/4.00    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 27.97/4.00    inference(flattening,[],[f51])).
% 27.97/4.00  
% 27.97/4.00  fof(f57,plain,(
% 27.97/4.00    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 27.97/4.00    introduced(choice_axiom,[])).
% 27.97/4.00  
% 27.97/4.00  fof(f56,plain,(
% 27.97/4.00    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 27.97/4.00    introduced(choice_axiom,[])).
% 27.97/4.00  
% 27.97/4.00  fof(f58,plain,(
% 27.97/4.00    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 27.97/4.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f52,f57,f56])).
% 27.97/4.00  
% 27.97/4.00  fof(f95,plain,(
% 27.97/4.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 27.97/4.00    inference(cnf_transformation,[],[f58])).
% 27.97/4.00  
% 27.97/4.00  fof(f98,plain,(
% 27.97/4.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 27.97/4.00    inference(cnf_transformation,[],[f58])).
% 27.97/4.00  
% 27.97/4.00  fof(f17,axiom,(
% 27.97/4.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 27.97/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.97/4.00  
% 27.97/4.00  fof(f45,plain,(
% 27.97/4.00    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 27.97/4.00    inference(ennf_transformation,[],[f17])).
% 27.97/4.00  
% 27.97/4.00  fof(f46,plain,(
% 27.97/4.00    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 27.97/4.00    inference(flattening,[],[f45])).
% 27.97/4.00  
% 27.97/4.00  fof(f87,plain,(
% 27.97/4.00    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 27.97/4.00    inference(cnf_transformation,[],[f46])).
% 27.97/4.00  
% 27.97/4.00  fof(f96,plain,(
% 27.97/4.00    v1_funct_1(sK3)),
% 27.97/4.00    inference(cnf_transformation,[],[f58])).
% 27.97/4.00  
% 27.97/4.00  fof(f93,plain,(
% 27.97/4.00    v1_funct_1(sK2)),
% 27.97/4.00    inference(cnf_transformation,[],[f58])).
% 27.97/4.00  
% 27.97/4.00  fof(f100,plain,(
% 27.97/4.00    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 27.97/4.00    inference(cnf_transformation,[],[f58])).
% 27.97/4.00  
% 27.97/4.00  fof(f15,axiom,(
% 27.97/4.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 27.97/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.97/4.00  
% 27.97/4.00  fof(f43,plain,(
% 27.97/4.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 27.97/4.00    inference(ennf_transformation,[],[f15])).
% 27.97/4.00  
% 27.97/4.00  fof(f44,plain,(
% 27.97/4.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 27.97/4.00    inference(flattening,[],[f43])).
% 27.97/4.00  
% 27.97/4.00  fof(f85,plain,(
% 27.97/4.00    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 27.97/4.00    inference(cnf_transformation,[],[f44])).
% 27.97/4.00  
% 27.97/4.00  fof(f12,axiom,(
% 27.97/4.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 27.97/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.97/4.00  
% 27.97/4.00  fof(f37,plain,(
% 27.97/4.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 27.97/4.00    inference(ennf_transformation,[],[f12])).
% 27.97/4.00  
% 27.97/4.00  fof(f38,plain,(
% 27.97/4.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 27.97/4.00    inference(flattening,[],[f37])).
% 27.97/4.00  
% 27.97/4.00  fof(f53,plain,(
% 27.97/4.00    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 27.97/4.00    inference(nnf_transformation,[],[f38])).
% 27.97/4.00  
% 27.97/4.00  fof(f74,plain,(
% 27.97/4.00    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 27.97/4.00    inference(cnf_transformation,[],[f53])).
% 27.97/4.00  
% 27.97/4.00  fof(f16,axiom,(
% 27.97/4.00    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 27.97/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.97/4.00  
% 27.97/4.00  fof(f23,plain,(
% 27.97/4.00    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 27.97/4.00    inference(pure_predicate_removal,[],[f16])).
% 27.97/4.00  
% 27.97/4.00  fof(f86,plain,(
% 27.97/4.00    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 27.97/4.00    inference(cnf_transformation,[],[f23])).
% 27.97/4.00  
% 27.97/4.00  fof(f9,axiom,(
% 27.97/4.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 27.97/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.97/4.00  
% 27.97/4.00  fof(f33,plain,(
% 27.97/4.00    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 27.97/4.00    inference(ennf_transformation,[],[f9])).
% 27.97/4.00  
% 27.97/4.00  fof(f34,plain,(
% 27.97/4.00    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 27.97/4.00    inference(flattening,[],[f33])).
% 27.97/4.00  
% 27.97/4.00  fof(f71,plain,(
% 27.97/4.00    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 27.97/4.00    inference(cnf_transformation,[],[f34])).
% 27.97/4.00  
% 27.97/4.00  fof(f18,axiom,(
% 27.97/4.00    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 27.97/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.97/4.00  
% 27.97/4.00  fof(f88,plain,(
% 27.97/4.00    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 27.97/4.00    inference(cnf_transformation,[],[f18])).
% 27.97/4.00  
% 27.97/4.00  fof(f109,plain,(
% 27.97/4.00    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 27.97/4.00    inference(definition_unfolding,[],[f71,f88])).
% 27.97/4.00  
% 27.97/4.00  fof(f1,axiom,(
% 27.97/4.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 27.97/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.97/4.00  
% 27.97/4.00  fof(f25,plain,(
% 27.97/4.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 27.97/4.00    inference(ennf_transformation,[],[f1])).
% 27.97/4.00  
% 27.97/4.00  fof(f59,plain,(
% 27.97/4.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 27.97/4.00    inference(cnf_transformation,[],[f25])).
% 27.97/4.00  
% 27.97/4.00  fof(f2,axiom,(
% 27.97/4.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 27.97/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.97/4.00  
% 27.97/4.00  fof(f60,plain,(
% 27.97/4.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 27.97/4.00    inference(cnf_transformation,[],[f2])).
% 27.97/4.00  
% 27.97/4.00  fof(f14,axiom,(
% 27.97/4.00    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 27.97/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.97/4.00  
% 27.97/4.00  fof(f41,plain,(
% 27.97/4.00    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 27.97/4.00    inference(ennf_transformation,[],[f14])).
% 27.97/4.00  
% 27.97/4.00  fof(f42,plain,(
% 27.97/4.00    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 27.97/4.00    inference(flattening,[],[f41])).
% 27.97/4.00  
% 27.97/4.00  fof(f55,plain,(
% 27.97/4.00    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 27.97/4.00    inference(nnf_transformation,[],[f42])).
% 27.97/4.00  
% 27.97/4.00  fof(f82,plain,(
% 27.97/4.00    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 27.97/4.00    inference(cnf_transformation,[],[f55])).
% 27.97/4.00  
% 27.97/4.00  fof(f19,axiom,(
% 27.97/4.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 27.97/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.97/4.00  
% 27.97/4.00  fof(f47,plain,(
% 27.97/4.00    ! [X0,X1,X2] : (! [X3] : (((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 27.97/4.00    inference(ennf_transformation,[],[f19])).
% 27.97/4.00  
% 27.97/4.00  fof(f48,plain,(
% 27.97/4.00    ! [X0,X1,X2] : (! [X3] : ((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 27.97/4.00    inference(flattening,[],[f47])).
% 27.97/4.00  
% 27.97/4.00  fof(f90,plain,(
% 27.97/4.00    ( ! [X2,X0,X3,X1] : (v2_funct_2(X3,X0) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 27.97/4.00    inference(cnf_transformation,[],[f48])).
% 27.97/4.00  
% 27.97/4.00  fof(f10,axiom,(
% 27.97/4.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 27.97/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.97/4.00  
% 27.97/4.00  fof(f24,plain,(
% 27.97/4.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 27.97/4.00    inference(pure_predicate_removal,[],[f10])).
% 27.97/4.00  
% 27.97/4.00  fof(f35,plain,(
% 27.97/4.00    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 27.97/4.00    inference(ennf_transformation,[],[f24])).
% 27.97/4.00  
% 27.97/4.00  fof(f72,plain,(
% 27.97/4.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 27.97/4.00    inference(cnf_transformation,[],[f35])).
% 27.97/4.00  
% 27.97/4.00  fof(f94,plain,(
% 27.97/4.00    v1_funct_2(sK2,sK0,sK1)),
% 27.97/4.00    inference(cnf_transformation,[],[f58])).
% 27.97/4.00  
% 27.97/4.00  fof(f97,plain,(
% 27.97/4.00    v1_funct_2(sK3,sK1,sK0)),
% 27.97/4.00    inference(cnf_transformation,[],[f58])).
% 27.97/4.00  
% 27.97/4.00  fof(f8,axiom,(
% 27.97/4.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0))))),
% 27.97/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.97/4.00  
% 27.97/4.00  fof(f31,plain,(
% 27.97/4.00    ! [X0] : (((k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 27.97/4.00    inference(ennf_transformation,[],[f8])).
% 27.97/4.00  
% 27.97/4.00  fof(f32,plain,(
% 27.97/4.00    ! [X0] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 27.97/4.00    inference(flattening,[],[f31])).
% 27.97/4.00  
% 27.97/4.00  fof(f69,plain,(
% 27.97/4.00    ( ! [X0] : (k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 27.97/4.00    inference(cnf_transformation,[],[f32])).
% 27.97/4.00  
% 27.97/4.00  fof(f5,axiom,(
% 27.97/4.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 27.97/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.97/4.00  
% 27.97/4.00  fof(f27,plain,(
% 27.97/4.00    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 27.97/4.00    inference(ennf_transformation,[],[f5])).
% 27.97/4.00  
% 27.97/4.00  fof(f28,plain,(
% 27.97/4.00    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 27.97/4.00    inference(flattening,[],[f27])).
% 27.97/4.00  
% 27.97/4.00  fof(f64,plain,(
% 27.97/4.00    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 27.97/4.00    inference(cnf_transformation,[],[f28])).
% 27.97/4.00  
% 27.97/4.00  fof(f101,plain,(
% 27.97/4.00    v2_funct_1(sK2)),
% 27.97/4.00    inference(cnf_transformation,[],[f58])).
% 27.97/4.00  
% 27.97/4.00  fof(f99,plain,(
% 27.97/4.00    k2_relset_1(sK0,sK1,sK2) = sK1),
% 27.97/4.00    inference(cnf_transformation,[],[f58])).
% 27.97/4.00  
% 27.97/4.00  fof(f20,axiom,(
% 27.97/4.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 27.97/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.97/4.00  
% 27.97/4.00  fof(f49,plain,(
% 27.97/4.00    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 27.97/4.00    inference(ennf_transformation,[],[f20])).
% 27.97/4.00  
% 27.97/4.00  fof(f50,plain,(
% 27.97/4.00    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 27.97/4.00    inference(flattening,[],[f49])).
% 27.97/4.00  
% 27.97/4.00  fof(f92,plain,(
% 27.97/4.00    ( ! [X2,X0,X1] : (k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 27.97/4.00    inference(cnf_transformation,[],[f50])).
% 27.97/4.00  
% 27.97/4.00  fof(f103,plain,(
% 27.97/4.00    k1_xboole_0 != sK1),
% 27.97/4.00    inference(cnf_transformation,[],[f58])).
% 27.97/4.00  
% 27.97/4.00  fof(f4,axiom,(
% 27.97/4.00    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 27.97/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.97/4.00  
% 27.97/4.00  fof(f62,plain,(
% 27.97/4.00    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 27.97/4.00    inference(cnf_transformation,[],[f4])).
% 27.97/4.00  
% 27.97/4.00  fof(f106,plain,(
% 27.97/4.00    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 27.97/4.00    inference(definition_unfolding,[],[f62,f88])).
% 27.97/4.00  
% 27.97/4.00  fof(f13,axiom,(
% 27.97/4.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 27.97/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.97/4.00  
% 27.97/4.00  fof(f39,plain,(
% 27.97/4.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 27.97/4.00    inference(ennf_transformation,[],[f13])).
% 27.97/4.00  
% 27.97/4.00  fof(f40,plain,(
% 27.97/4.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 27.97/4.00    inference(flattening,[],[f39])).
% 27.97/4.00  
% 27.97/4.00  fof(f54,plain,(
% 27.97/4.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 27.97/4.00    inference(nnf_transformation,[],[f40])).
% 27.97/4.00  
% 27.97/4.00  fof(f76,plain,(
% 27.97/4.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 27.97/4.00    inference(cnf_transformation,[],[f54])).
% 27.97/4.00  
% 27.97/4.00  fof(f11,axiom,(
% 27.97/4.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 27.97/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.97/4.00  
% 27.97/4.00  fof(f36,plain,(
% 27.97/4.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 27.97/4.00    inference(ennf_transformation,[],[f11])).
% 27.97/4.00  
% 27.97/4.00  fof(f73,plain,(
% 27.97/4.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 27.97/4.00    inference(cnf_transformation,[],[f36])).
% 27.97/4.00  
% 27.97/4.00  fof(f102,plain,(
% 27.97/4.00    k1_xboole_0 != sK0),
% 27.97/4.00    inference(cnf_transformation,[],[f58])).
% 27.97/4.00  
% 27.97/4.00  fof(f6,axiom,(
% 27.97/4.00    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 27.97/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.97/4.00  
% 27.97/4.00  fof(f66,plain,(
% 27.97/4.00    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 27.97/4.00    inference(cnf_transformation,[],[f6])).
% 27.97/4.00  
% 27.97/4.00  fof(f107,plain,(
% 27.97/4.00    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 27.97/4.00    inference(definition_unfolding,[],[f66,f88])).
% 27.97/4.00  
% 27.97/4.00  fof(f7,axiom,(
% 27.97/4.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 27.97/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.97/4.00  
% 27.97/4.00  fof(f29,plain,(
% 27.97/4.00    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 27.97/4.00    inference(ennf_transformation,[],[f7])).
% 27.97/4.00  
% 27.97/4.00  fof(f30,plain,(
% 27.97/4.00    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 27.97/4.00    inference(flattening,[],[f29])).
% 27.97/4.00  
% 27.97/4.00  fof(f68,plain,(
% 27.97/4.00    ( ! [X0,X1] : (v2_funct_1(X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 27.97/4.00    inference(cnf_transformation,[],[f30])).
% 27.97/4.00  
% 27.97/4.00  fof(f3,axiom,(
% 27.97/4.00    ! [X0] : (v1_relat_1(X0) => k4_relat_1(k4_relat_1(X0)) = X0)),
% 27.97/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.97/4.00  
% 27.97/4.00  fof(f26,plain,(
% 27.97/4.00    ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 27.97/4.00    inference(ennf_transformation,[],[f3])).
% 27.97/4.00  
% 27.97/4.00  fof(f61,plain,(
% 27.97/4.00    ( ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 27.97/4.00    inference(cnf_transformation,[],[f26])).
% 27.97/4.00  
% 27.97/4.00  fof(f104,plain,(
% 27.97/4.00    k2_funct_1(sK2) != sK3),
% 27.97/4.00    inference(cnf_transformation,[],[f58])).
% 27.97/4.00  
% 27.97/4.00  cnf(c_42,negated_conjecture,
% 27.97/4.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 27.97/4.00      inference(cnf_transformation,[],[f95]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_1748,plain,
% 27.97/4.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 27.97/4.00      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_39,negated_conjecture,
% 27.97/4.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 27.97/4.00      inference(cnf_transformation,[],[f98]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_1751,plain,
% 27.97/4.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 27.97/4.00      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_28,plain,
% 27.97/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.97/4.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 27.97/4.00      | ~ v1_funct_1(X0)
% 27.97/4.00      | ~ v1_funct_1(X3)
% 27.97/4.00      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 27.97/4.00      inference(cnf_transformation,[],[f87]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_1757,plain,
% 27.97/4.00      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 27.97/4.00      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 27.97/4.00      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 27.97/4.00      | v1_funct_1(X5) != iProver_top
% 27.97/4.00      | v1_funct_1(X4) != iProver_top ),
% 27.97/4.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_5501,plain,
% 27.97/4.00      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 27.97/4.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 27.97/4.00      | v1_funct_1(X2) != iProver_top
% 27.97/4.00      | v1_funct_1(sK3) != iProver_top ),
% 27.97/4.00      inference(superposition,[status(thm)],[c_1751,c_1757]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_41,negated_conjecture,
% 27.97/4.00      ( v1_funct_1(sK3) ),
% 27.97/4.00      inference(cnf_transformation,[],[f96]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_48,plain,
% 27.97/4.00      ( v1_funct_1(sK3) = iProver_top ),
% 27.97/4.00      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_6060,plain,
% 27.97/4.00      ( v1_funct_1(X2) != iProver_top
% 27.97/4.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 27.97/4.00      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 27.97/4.00      inference(global_propositional_subsumption,
% 27.97/4.00                [status(thm)],
% 27.97/4.00                [c_5501,c_48]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_6061,plain,
% 27.97/4.00      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 27.97/4.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 27.97/4.00      | v1_funct_1(X2) != iProver_top ),
% 27.97/4.00      inference(renaming,[status(thm)],[c_6060]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_6068,plain,
% 27.97/4.00      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 27.97/4.00      | v1_funct_1(sK2) != iProver_top ),
% 27.97/4.00      inference(superposition,[status(thm)],[c_1748,c_6061]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_44,negated_conjecture,
% 27.97/4.00      ( v1_funct_1(sK2) ),
% 27.97/4.00      inference(cnf_transformation,[],[f93]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_45,plain,
% 27.97/4.00      ( v1_funct_1(sK2) = iProver_top ),
% 27.97/4.00      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_6133,plain,
% 27.97/4.00      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 27.97/4.00      inference(global_propositional_subsumption,
% 27.97/4.00                [status(thm)],
% 27.97/4.00                [c_6068,c_45]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_37,negated_conjecture,
% 27.97/4.00      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 27.97/4.00      inference(cnf_transformation,[],[f100]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_1752,plain,
% 27.97/4.00      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) = iProver_top ),
% 27.97/4.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_6135,plain,
% 27.97/4.00      ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) = iProver_top ),
% 27.97/4.00      inference(demodulation,[status(thm)],[c_6133,c_1752]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_25,plain,
% 27.97/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.97/4.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 27.97/4.00      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 27.97/4.00      | ~ v1_funct_1(X0)
% 27.97/4.00      | ~ v1_funct_1(X3) ),
% 27.97/4.00      inference(cnf_transformation,[],[f85]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_1760,plain,
% 27.97/4.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 27.97/4.00      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 27.97/4.00      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 27.97/4.00      | v1_funct_1(X0) != iProver_top
% 27.97/4.00      | v1_funct_1(X3) != iProver_top ),
% 27.97/4.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_6172,plain,
% 27.97/4.00      ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 27.97/4.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 27.97/4.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 27.97/4.00      | v1_funct_1(sK3) != iProver_top
% 27.97/4.00      | v1_funct_1(sK2) != iProver_top ),
% 27.97/4.00      inference(superposition,[status(thm)],[c_6133,c_1760]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_47,plain,
% 27.97/4.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 27.97/4.00      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_50,plain,
% 27.97/4.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 27.97/4.00      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_8830,plain,
% 27.97/4.00      ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 27.97/4.00      inference(global_propositional_subsumption,
% 27.97/4.00                [status(thm)],
% 27.97/4.00                [c_6172,c_45,c_47,c_48,c_50]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_16,plain,
% 27.97/4.00      ( ~ r2_relset_1(X0,X1,X2,X3)
% 27.97/4.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 27.97/4.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 27.97/4.00      | X3 = X2 ),
% 27.97/4.00      inference(cnf_transformation,[],[f74]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_1767,plain,
% 27.97/4.00      ( X0 = X1
% 27.97/4.00      | r2_relset_1(X2,X3,X1,X0) != iProver_top
% 27.97/4.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 27.97/4.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top ),
% 27.97/4.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_8841,plain,
% 27.97/4.00      ( k5_relat_1(sK2,sK3) = X0
% 27.97/4.00      | r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),X0) != iProver_top
% 27.97/4.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 27.97/4.00      inference(superposition,[status(thm)],[c_8830,c_1767]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_10702,plain,
% 27.97/4.00      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 27.97/4.00      | m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 27.97/4.00      inference(superposition,[status(thm)],[c_6135,c_8841]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_27,plain,
% 27.97/4.00      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 27.97/4.00      inference(cnf_transformation,[],[f86]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_2182,plain,
% 27.97/4.00      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 27.97/4.00      inference(instantiation,[status(thm)],[c_27]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_2183,plain,
% 27.97/4.00      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 27.97/4.00      inference(predicate_to_equality,[status(thm)],[c_2182]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_10753,plain,
% 27.97/4.00      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 27.97/4.00      inference(global_propositional_subsumption,
% 27.97/4.00                [status(thm)],
% 27.97/4.00                [c_10702,c_2183]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_12,plain,
% 27.97/4.00      ( ~ v1_funct_1(X0)
% 27.97/4.00      | ~ v1_funct_1(X1)
% 27.97/4.00      | ~ v2_funct_1(X0)
% 27.97/4.00      | ~ v1_relat_1(X0)
% 27.97/4.00      | ~ v1_relat_1(X1)
% 27.97/4.00      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
% 27.97/4.00      | k2_funct_1(X0) = X1
% 27.97/4.00      | k1_relat_1(X0) != k2_relat_1(X1) ),
% 27.97/4.00      inference(cnf_transformation,[],[f109]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_1770,plain,
% 27.97/4.00      ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 27.97/4.00      | k2_funct_1(X1) = X0
% 27.97/4.00      | k1_relat_1(X1) != k2_relat_1(X0)
% 27.97/4.00      | v1_funct_1(X1) != iProver_top
% 27.97/4.00      | v1_funct_1(X0) != iProver_top
% 27.97/4.00      | v2_funct_1(X1) != iProver_top
% 27.97/4.00      | v1_relat_1(X1) != iProver_top
% 27.97/4.00      | v1_relat_1(X0) != iProver_top ),
% 27.97/4.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_10770,plain,
% 27.97/4.00      ( k2_funct_1(sK3) = sK2
% 27.97/4.00      | k1_relat_1(sK3) != k2_relat_1(sK2)
% 27.97/4.00      | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
% 27.97/4.00      | v1_funct_1(sK3) != iProver_top
% 27.97/4.00      | v1_funct_1(sK2) != iProver_top
% 27.97/4.00      | v2_funct_1(sK3) != iProver_top
% 27.97/4.00      | v1_relat_1(sK3) != iProver_top
% 27.97/4.00      | v1_relat_1(sK2) != iProver_top ),
% 27.97/4.00      inference(superposition,[status(thm)],[c_10753,c_1770]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_0,plain,
% 27.97/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 27.97/4.00      | ~ v1_relat_1(X1)
% 27.97/4.00      | v1_relat_1(X0) ),
% 27.97/4.00      inference(cnf_transformation,[],[f59]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_1780,plain,
% 27.97/4.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 27.97/4.00      | v1_relat_1(X1) != iProver_top
% 27.97/4.00      | v1_relat_1(X0) = iProver_top ),
% 27.97/4.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_3064,plain,
% 27.97/4.00      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 27.97/4.00      | v1_relat_1(sK3) = iProver_top ),
% 27.97/4.00      inference(superposition,[status(thm)],[c_1751,c_1780]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_1,plain,
% 27.97/4.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 27.97/4.00      inference(cnf_transformation,[],[f60]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_3141,plain,
% 27.97/4.00      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
% 27.97/4.00      inference(instantiation,[status(thm)],[c_1]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_3142,plain,
% 27.97/4.00      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
% 27.97/4.00      inference(predicate_to_equality,[status(thm)],[c_3141]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_3367,plain,
% 27.97/4.00      ( v1_relat_1(sK3) = iProver_top ),
% 27.97/4.00      inference(global_propositional_subsumption,
% 27.97/4.00                [status(thm)],
% 27.97/4.00                [c_3064,c_3142]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_24,plain,
% 27.97/4.00      ( ~ v2_funct_2(X0,X1)
% 27.97/4.00      | ~ v5_relat_1(X0,X1)
% 27.97/4.00      | ~ v1_relat_1(X0)
% 27.97/4.00      | k2_relat_1(X0) = X1 ),
% 27.97/4.00      inference(cnf_transformation,[],[f82]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_29,plain,
% 27.97/4.00      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 27.97/4.00      | ~ v1_funct_2(X2,X0,X1)
% 27.97/4.00      | ~ v1_funct_2(X3,X1,X0)
% 27.97/4.00      | v2_funct_2(X3,X0)
% 27.97/4.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 27.97/4.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 27.97/4.00      | ~ v1_funct_1(X3)
% 27.97/4.00      | ~ v1_funct_1(X2) ),
% 27.97/4.00      inference(cnf_transformation,[],[f90]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_484,plain,
% 27.97/4.00      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 27.97/4.00      | ~ v1_funct_2(X2,X0,X1)
% 27.97/4.00      | ~ v1_funct_2(X3,X1,X0)
% 27.97/4.00      | ~ v5_relat_1(X4,X5)
% 27.97/4.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 27.97/4.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 27.97/4.00      | ~ v1_funct_1(X2)
% 27.97/4.00      | ~ v1_funct_1(X3)
% 27.97/4.00      | ~ v1_relat_1(X4)
% 27.97/4.00      | X3 != X4
% 27.97/4.00      | X0 != X5
% 27.97/4.00      | k2_relat_1(X4) = X5 ),
% 27.97/4.00      inference(resolution_lifted,[status(thm)],[c_24,c_29]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_485,plain,
% 27.97/4.00      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 27.97/4.00      | ~ v1_funct_2(X2,X0,X1)
% 27.97/4.00      | ~ v1_funct_2(X3,X1,X0)
% 27.97/4.00      | ~ v5_relat_1(X3,X0)
% 27.97/4.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 27.97/4.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 27.97/4.00      | ~ v1_funct_1(X3)
% 27.97/4.00      | ~ v1_funct_1(X2)
% 27.97/4.00      | ~ v1_relat_1(X3)
% 27.97/4.00      | k2_relat_1(X3) = X0 ),
% 27.97/4.00      inference(unflattening,[status(thm)],[c_484]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_13,plain,
% 27.97/4.00      ( v5_relat_1(X0,X1)
% 27.97/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 27.97/4.00      inference(cnf_transformation,[],[f72]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_509,plain,
% 27.97/4.00      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 27.97/4.00      | ~ v1_funct_2(X2,X0,X1)
% 27.97/4.00      | ~ v1_funct_2(X3,X1,X0)
% 27.97/4.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 27.97/4.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 27.97/4.00      | ~ v1_funct_1(X3)
% 27.97/4.00      | ~ v1_funct_1(X2)
% 27.97/4.00      | ~ v1_relat_1(X3)
% 27.97/4.00      | k2_relat_1(X3) = X0 ),
% 27.97/4.00      inference(forward_subsumption_resolution,
% 27.97/4.00                [status(thm)],
% 27.97/4.00                [c_485,c_13]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_1745,plain,
% 27.97/4.00      ( k2_relat_1(X0) = X1
% 27.97/4.00      | r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X0),k6_partfun1(X1)) != iProver_top
% 27.97/4.00      | v1_funct_2(X3,X1,X2) != iProver_top
% 27.97/4.00      | v1_funct_2(X0,X2,X1) != iProver_top
% 27.97/4.00      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 27.97/4.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 27.97/4.00      | v1_funct_1(X3) != iProver_top
% 27.97/4.00      | v1_funct_1(X0) != iProver_top
% 27.97/4.00      | v1_relat_1(X0) != iProver_top ),
% 27.97/4.00      inference(predicate_to_equality,[status(thm)],[c_509]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_2745,plain,
% 27.97/4.00      ( k2_relat_1(sK3) = sK0
% 27.97/4.00      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 27.97/4.00      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 27.97/4.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 27.97/4.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 27.97/4.00      | v1_funct_1(sK3) != iProver_top
% 27.97/4.00      | v1_funct_1(sK2) != iProver_top
% 27.97/4.00      | v1_relat_1(sK3) != iProver_top ),
% 27.97/4.00      inference(superposition,[status(thm)],[c_1752,c_1745]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_43,negated_conjecture,
% 27.97/4.00      ( v1_funct_2(sK2,sK0,sK1) ),
% 27.97/4.00      inference(cnf_transformation,[],[f94]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_46,plain,
% 27.97/4.00      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 27.97/4.00      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_40,negated_conjecture,
% 27.97/4.00      ( v1_funct_2(sK3,sK1,sK0) ),
% 27.97/4.00      inference(cnf_transformation,[],[f97]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_49,plain,
% 27.97/4.00      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 27.97/4.00      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_2748,plain,
% 27.97/4.00      ( k2_relat_1(sK3) = sK0 | v1_relat_1(sK3) != iProver_top ),
% 27.97/4.00      inference(global_propositional_subsumption,
% 27.97/4.00                [status(thm)],
% 27.97/4.00                [c_2745,c_45,c_46,c_47,c_48,c_49,c_50]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_3372,plain,
% 27.97/4.00      ( k2_relat_1(sK3) = sK0 ),
% 27.97/4.00      inference(superposition,[status(thm)],[c_3367,c_2748]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_1746,plain,
% 27.97/4.00      ( v1_funct_1(sK2) = iProver_top ),
% 27.97/4.00      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_11,plain,
% 27.97/4.00      ( ~ v1_funct_1(X0)
% 27.97/4.00      | ~ v2_funct_1(X0)
% 27.97/4.00      | ~ v1_relat_1(X0)
% 27.97/4.00      | k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) ),
% 27.97/4.00      inference(cnf_transformation,[],[f69]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_1771,plain,
% 27.97/4.00      ( k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0)
% 27.97/4.00      | v1_funct_1(X0) != iProver_top
% 27.97/4.00      | v2_funct_1(X0) != iProver_top
% 27.97/4.00      | v1_relat_1(X0) != iProver_top ),
% 27.97/4.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_4406,plain,
% 27.97/4.00      ( k1_relat_1(k5_relat_1(k2_funct_1(sK2),sK2)) = k2_relat_1(sK2)
% 27.97/4.00      | v2_funct_1(sK2) != iProver_top
% 27.97/4.00      | v1_relat_1(sK2) != iProver_top ),
% 27.97/4.00      inference(superposition,[status(thm)],[c_1746,c_1771]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_5,plain,
% 27.97/4.00      ( ~ v1_funct_1(X0)
% 27.97/4.00      | ~ v2_funct_1(X0)
% 27.97/4.00      | ~ v1_relat_1(X0)
% 27.97/4.00      | k2_funct_1(X0) = k4_relat_1(X0) ),
% 27.97/4.00      inference(cnf_transformation,[],[f64]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_1777,plain,
% 27.97/4.00      ( k2_funct_1(X0) = k4_relat_1(X0)
% 27.97/4.00      | v1_funct_1(X0) != iProver_top
% 27.97/4.00      | v2_funct_1(X0) != iProver_top
% 27.97/4.00      | v1_relat_1(X0) != iProver_top ),
% 27.97/4.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_3544,plain,
% 27.97/4.00      ( k2_funct_1(sK2) = k4_relat_1(sK2)
% 27.97/4.00      | v2_funct_1(sK2) != iProver_top
% 27.97/4.00      | v1_relat_1(sK2) != iProver_top ),
% 27.97/4.00      inference(superposition,[status(thm)],[c_1746,c_1777]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_36,negated_conjecture,
% 27.97/4.00      ( v2_funct_1(sK2) ),
% 27.97/4.00      inference(cnf_transformation,[],[f101]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_52,plain,
% 27.97/4.00      ( v2_funct_1(sK2) = iProver_top ),
% 27.97/4.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_1779,plain,
% 27.97/4.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 27.97/4.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_3065,plain,
% 27.97/4.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 27.97/4.00      | v1_relat_1(sK2) = iProver_top ),
% 27.97/4.00      inference(superposition,[status(thm)],[c_1748,c_1780]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_3429,plain,
% 27.97/4.00      ( v1_relat_1(sK2) = iProver_top ),
% 27.97/4.00      inference(superposition,[status(thm)],[c_1779,c_3065]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_3680,plain,
% 27.97/4.00      ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 27.97/4.00      inference(global_propositional_subsumption,
% 27.97/4.00                [status(thm)],
% 27.97/4.00                [c_3544,c_52,c_3429]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_38,negated_conjecture,
% 27.97/4.00      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 27.97/4.00      inference(cnf_transformation,[],[f99]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_31,plain,
% 27.97/4.00      ( ~ v1_funct_2(X0,X1,X2)
% 27.97/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.97/4.00      | ~ v1_funct_1(X0)
% 27.97/4.00      | ~ v2_funct_1(X0)
% 27.97/4.00      | k2_relset_1(X1,X2,X0) != X2
% 27.97/4.00      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
% 27.97/4.00      | k1_xboole_0 = X2 ),
% 27.97/4.00      inference(cnf_transformation,[],[f92]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_1755,plain,
% 27.97/4.00      ( k2_relset_1(X0,X1,X2) != X1
% 27.97/4.00      | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
% 27.97/4.00      | k1_xboole_0 = X1
% 27.97/4.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 27.97/4.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 27.97/4.00      | v1_funct_1(X2) != iProver_top
% 27.97/4.00      | v2_funct_1(X2) != iProver_top ),
% 27.97/4.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_3477,plain,
% 27.97/4.00      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 27.97/4.00      | sK1 = k1_xboole_0
% 27.97/4.00      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 27.97/4.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 27.97/4.00      | v1_funct_1(sK2) != iProver_top
% 27.97/4.00      | v2_funct_1(sK2) != iProver_top ),
% 27.97/4.00      inference(superposition,[status(thm)],[c_38,c_1755]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_34,negated_conjecture,
% 27.97/4.00      ( k1_xboole_0 != sK1 ),
% 27.97/4.00      inference(cnf_transformation,[],[f103]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_1846,plain,
% 27.97/4.00      ( ~ v1_funct_2(X0,X1,sK1)
% 27.97/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 27.97/4.00      | ~ v1_funct_1(X0)
% 27.97/4.00      | ~ v2_funct_1(X0)
% 27.97/4.00      | k2_relset_1(X1,sK1,X0) != sK1
% 27.97/4.00      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(sK1)
% 27.97/4.00      | k1_xboole_0 = sK1 ),
% 27.97/4.00      inference(instantiation,[status(thm)],[c_31]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_2040,plain,
% 27.97/4.00      ( ~ v1_funct_2(sK2,X0,sK1)
% 27.97/4.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
% 27.97/4.00      | ~ v1_funct_1(sK2)
% 27.97/4.00      | ~ v2_funct_1(sK2)
% 27.97/4.00      | k2_relset_1(X0,sK1,sK2) != sK1
% 27.97/4.00      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 27.97/4.00      | k1_xboole_0 = sK1 ),
% 27.97/4.00      inference(instantiation,[status(thm)],[c_1846]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_2124,plain,
% 27.97/4.00      ( ~ v1_funct_2(sK2,sK0,sK1)
% 27.97/4.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 27.97/4.00      | ~ v1_funct_1(sK2)
% 27.97/4.00      | ~ v2_funct_1(sK2)
% 27.97/4.00      | k2_relset_1(sK0,sK1,sK2) != sK1
% 27.97/4.00      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 27.97/4.00      | k1_xboole_0 = sK1 ),
% 27.97/4.00      inference(instantiation,[status(thm)],[c_2040]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_3605,plain,
% 27.97/4.00      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
% 27.97/4.00      inference(global_propositional_subsumption,
% 27.97/4.00                [status(thm)],
% 27.97/4.00                [c_3477,c_44,c_43,c_42,c_38,c_36,c_34,c_2124]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_3682,plain,
% 27.97/4.00      ( k5_relat_1(k4_relat_1(sK2),sK2) = k6_partfun1(sK1) ),
% 27.97/4.00      inference(demodulation,[status(thm)],[c_3680,c_3605]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_4407,plain,
% 27.97/4.00      ( k1_relat_1(k6_partfun1(sK1)) = k2_relat_1(sK2)
% 27.97/4.00      | v2_funct_1(sK2) != iProver_top
% 27.97/4.00      | v1_relat_1(sK2) != iProver_top ),
% 27.97/4.00      inference(light_normalisation,[status(thm)],[c_4406,c_3680,c_3682]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_4,plain,
% 27.97/4.00      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 27.97/4.00      inference(cnf_transformation,[],[f106]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_4408,plain,
% 27.97/4.00      ( k2_relat_1(sK2) = sK1
% 27.97/4.00      | v2_funct_1(sK2) != iProver_top
% 27.97/4.00      | v1_relat_1(sK2) != iProver_top ),
% 27.97/4.00      inference(demodulation,[status(thm)],[c_4407,c_4]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_4544,plain,
% 27.97/4.00      ( k2_relat_1(sK2) = sK1 ),
% 27.97/4.00      inference(global_propositional_subsumption,
% 27.97/4.00                [status(thm)],
% 27.97/4.00                [c_4408,c_52,c_3429]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_22,plain,
% 27.97/4.00      ( ~ v1_funct_2(X0,X1,X2)
% 27.97/4.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.97/4.00      | k1_relset_1(X1,X2,X0) = X1
% 27.97/4.00      | k1_xboole_0 = X2 ),
% 27.97/4.00      inference(cnf_transformation,[],[f76]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_1761,plain,
% 27.97/4.00      ( k1_relset_1(X0,X1,X2) = X0
% 27.97/4.00      | k1_xboole_0 = X1
% 27.97/4.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 27.97/4.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 27.97/4.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_5514,plain,
% 27.97/4.00      ( k1_relset_1(sK1,sK0,sK3) = sK1
% 27.97/4.00      | sK0 = k1_xboole_0
% 27.97/4.00      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 27.97/4.00      inference(superposition,[status(thm)],[c_1751,c_1761]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_14,plain,
% 27.97/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.97/4.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 27.97/4.00      inference(cnf_transformation,[],[f73]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_1769,plain,
% 27.97/4.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 27.97/4.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 27.97/4.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_2921,plain,
% 27.97/4.00      ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
% 27.97/4.00      inference(superposition,[status(thm)],[c_1751,c_1769]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_5517,plain,
% 27.97/4.00      ( k1_relat_1(sK3) = sK1
% 27.97/4.00      | sK0 = k1_xboole_0
% 27.97/4.00      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 27.97/4.00      inference(demodulation,[status(thm)],[c_5514,c_2921]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_35,negated_conjecture,
% 27.97/4.00      ( k1_xboole_0 != sK0 ),
% 27.97/4.00      inference(cnf_transformation,[],[f102]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_1153,plain,( X0 = X0 ),theory(equality) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_1190,plain,
% 27.97/4.00      ( k1_xboole_0 = k1_xboole_0 ),
% 27.97/4.00      inference(instantiation,[status(thm)],[c_1153]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_1154,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_1899,plain,
% 27.97/4.00      ( sK0 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK0 ),
% 27.97/4.00      inference(instantiation,[status(thm)],[c_1154]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_1900,plain,
% 27.97/4.00      ( sK0 != k1_xboole_0
% 27.97/4.00      | k1_xboole_0 = sK0
% 27.97/4.00      | k1_xboole_0 != k1_xboole_0 ),
% 27.97/4.00      inference(instantiation,[status(thm)],[c_1899]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_10261,plain,
% 27.97/4.00      ( k1_relat_1(sK3) = sK1 ),
% 27.97/4.00      inference(global_propositional_subsumption,
% 27.97/4.00                [status(thm)],
% 27.97/4.00                [c_5517,c_49,c_35,c_1190,c_1900]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_10771,plain,
% 27.97/4.00      ( k2_funct_1(sK3) = sK2
% 27.97/4.00      | k6_partfun1(sK0) != k6_partfun1(sK0)
% 27.97/4.00      | sK1 != sK1
% 27.97/4.00      | v1_funct_1(sK3) != iProver_top
% 27.97/4.00      | v1_funct_1(sK2) != iProver_top
% 27.97/4.00      | v2_funct_1(sK3) != iProver_top
% 27.97/4.00      | v1_relat_1(sK3) != iProver_top
% 27.97/4.00      | v1_relat_1(sK2) != iProver_top ),
% 27.97/4.00      inference(light_normalisation,
% 27.97/4.00                [status(thm)],
% 27.97/4.00                [c_10770,c_3372,c_4544,c_10261]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_10772,plain,
% 27.97/4.00      ( k2_funct_1(sK3) = sK2
% 27.97/4.00      | v1_funct_1(sK3) != iProver_top
% 27.97/4.00      | v1_funct_1(sK2) != iProver_top
% 27.97/4.00      | v2_funct_1(sK3) != iProver_top
% 27.97/4.00      | v1_relat_1(sK3) != iProver_top
% 27.97/4.00      | v1_relat_1(sK2) != iProver_top ),
% 27.97/4.00      inference(equality_resolution_simp,[status(thm)],[c_10771]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_6,plain,
% 27.97/4.00      ( v2_funct_1(k6_partfun1(X0)) ),
% 27.97/4.00      inference(cnf_transformation,[],[f107]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_8910,plain,
% 27.97/4.00      ( v2_funct_1(k6_partfun1(sK0)) ),
% 27.97/4.00      inference(instantiation,[status(thm)],[c_6]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_8911,plain,
% 27.97/4.00      ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
% 27.97/4.00      inference(predicate_to_equality,[status(thm)],[c_8910]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_8,plain,
% 27.97/4.00      ( ~ v1_funct_1(X0)
% 27.97/4.00      | ~ v1_funct_1(X1)
% 27.97/4.00      | v2_funct_1(X0)
% 27.97/4.00      | ~ v2_funct_1(k5_relat_1(X1,X0))
% 27.97/4.00      | ~ v1_relat_1(X0)
% 27.97/4.00      | ~ v1_relat_1(X1)
% 27.97/4.00      | k1_relat_1(X0) != k2_relat_1(X1) ),
% 27.97/4.00      inference(cnf_transformation,[],[f68]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_1774,plain,
% 27.97/4.00      ( k1_relat_1(X0) != k2_relat_1(X1)
% 27.97/4.00      | v1_funct_1(X0) != iProver_top
% 27.97/4.00      | v1_funct_1(X1) != iProver_top
% 27.97/4.00      | v2_funct_1(X0) = iProver_top
% 27.97/4.00      | v2_funct_1(k5_relat_1(X1,X0)) != iProver_top
% 27.97/4.00      | v1_relat_1(X0) != iProver_top
% 27.97/4.00      | v1_relat_1(X1) != iProver_top ),
% 27.97/4.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_10265,plain,
% 27.97/4.00      ( k2_relat_1(X0) != sK1
% 27.97/4.00      | v1_funct_1(X0) != iProver_top
% 27.97/4.00      | v1_funct_1(sK3) != iProver_top
% 27.97/4.00      | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
% 27.97/4.00      | v2_funct_1(sK3) = iProver_top
% 27.97/4.00      | v1_relat_1(X0) != iProver_top
% 27.97/4.00      | v1_relat_1(sK3) != iProver_top ),
% 27.97/4.00      inference(superposition,[status(thm)],[c_10261,c_1774]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_57153,plain,
% 27.97/4.00      ( v1_relat_1(X0) != iProver_top
% 27.97/4.00      | v2_funct_1(sK3) = iProver_top
% 27.97/4.00      | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
% 27.97/4.00      | k2_relat_1(X0) != sK1
% 27.97/4.00      | v1_funct_1(X0) != iProver_top ),
% 27.97/4.00      inference(global_propositional_subsumption,
% 27.97/4.00                [status(thm)],
% 27.97/4.00                [c_10265,c_48,c_3064,c_3142]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_57154,plain,
% 27.97/4.00      ( k2_relat_1(X0) != sK1
% 27.97/4.00      | v1_funct_1(X0) != iProver_top
% 27.97/4.00      | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
% 27.97/4.00      | v2_funct_1(sK3) = iProver_top
% 27.97/4.00      | v1_relat_1(X0) != iProver_top ),
% 27.97/4.00      inference(renaming,[status(thm)],[c_57153]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_57160,plain,
% 27.97/4.00      ( v1_funct_1(sK2) != iProver_top
% 27.97/4.00      | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
% 27.97/4.00      | v2_funct_1(sK3) = iProver_top
% 27.97/4.00      | v1_relat_1(sK2) != iProver_top ),
% 27.97/4.00      inference(superposition,[status(thm)],[c_4544,c_57154]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_57163,plain,
% 27.97/4.00      ( v1_funct_1(sK2) != iProver_top
% 27.97/4.00      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 27.97/4.00      | v2_funct_1(sK3) = iProver_top
% 27.97/4.00      | v1_relat_1(sK2) != iProver_top ),
% 27.97/4.00      inference(light_normalisation,[status(thm)],[c_57160,c_10753]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_87476,plain,
% 27.97/4.00      ( k2_funct_1(sK3) = sK2 ),
% 27.97/4.00      inference(global_propositional_subsumption,
% 27.97/4.00                [status(thm)],
% 27.97/4.00                [c_10772,c_45,c_48,c_3064,c_3142,c_3429,c_8911,c_57163]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_57171,plain,
% 27.97/4.00      ( v2_funct_1(sK3) = iProver_top ),
% 27.97/4.00      inference(global_propositional_subsumption,
% 27.97/4.00                [status(thm)],
% 27.97/4.00                [c_57163,c_45,c_3429,c_8911]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_1749,plain,
% 27.97/4.00      ( v1_funct_1(sK3) = iProver_top ),
% 27.97/4.00      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_3543,plain,
% 27.97/4.00      ( k2_funct_1(sK3) = k4_relat_1(sK3)
% 27.97/4.00      | v2_funct_1(sK3) != iProver_top
% 27.97/4.00      | v1_relat_1(sK3) != iProver_top ),
% 27.97/4.00      inference(superposition,[status(thm)],[c_1749,c_1777]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_3675,plain,
% 27.97/4.00      ( v2_funct_1(sK3) != iProver_top
% 27.97/4.00      | k2_funct_1(sK3) = k4_relat_1(sK3) ),
% 27.97/4.00      inference(global_propositional_subsumption,
% 27.97/4.00                [status(thm)],
% 27.97/4.00                [c_3543,c_3064,c_3142]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_3676,plain,
% 27.97/4.00      ( k2_funct_1(sK3) = k4_relat_1(sK3)
% 27.97/4.00      | v2_funct_1(sK3) != iProver_top ),
% 27.97/4.00      inference(renaming,[status(thm)],[c_3675]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_57177,plain,
% 27.97/4.00      ( k2_funct_1(sK3) = k4_relat_1(sK3) ),
% 27.97/4.00      inference(superposition,[status(thm)],[c_57171,c_3676]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_87478,plain,
% 27.97/4.00      ( k4_relat_1(sK3) = sK2 ),
% 27.97/4.00      inference(demodulation,[status(thm)],[c_87476,c_57177]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_2,plain,
% 27.97/4.00      ( ~ v1_relat_1(X0) | k4_relat_1(k4_relat_1(X0)) = X0 ),
% 27.97/4.00      inference(cnf_transformation,[],[f61]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_1778,plain,
% 27.97/4.00      ( k4_relat_1(k4_relat_1(X0)) = X0 | v1_relat_1(X0) != iProver_top ),
% 27.97/4.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_3371,plain,
% 27.97/4.00      ( k4_relat_1(k4_relat_1(sK3)) = sK3 ),
% 27.97/4.00      inference(superposition,[status(thm)],[c_3367,c_1778]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_87556,plain,
% 27.97/4.00      ( k4_relat_1(sK2) = sK3 ),
% 27.97/4.00      inference(demodulation,[status(thm)],[c_87478,c_3371]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_33,negated_conjecture,
% 27.97/4.00      ( k2_funct_1(sK2) != sK3 ),
% 27.97/4.00      inference(cnf_transformation,[],[f104]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(c_3684,plain,
% 27.97/4.00      ( k4_relat_1(sK2) != sK3 ),
% 27.97/4.00      inference(demodulation,[status(thm)],[c_3680,c_33]) ).
% 27.97/4.00  
% 27.97/4.00  cnf(contradiction,plain,
% 27.97/4.00      ( $false ),
% 27.97/4.00      inference(minisat,[status(thm)],[c_87556,c_3684]) ).
% 27.97/4.00  
% 27.97/4.00  
% 27.97/4.00  % SZS output end CNFRefutation for theBenchmark.p
% 27.97/4.00  
% 27.97/4.00  ------                               Statistics
% 27.97/4.00  
% 27.97/4.00  ------ General
% 27.97/4.00  
% 27.97/4.00  abstr_ref_over_cycles:                  0
% 27.97/4.00  abstr_ref_under_cycles:                 0
% 27.97/4.00  gc_basic_clause_elim:                   0
% 27.97/4.00  forced_gc_time:                         0
% 27.97/4.00  parsing_time:                           0.01
% 27.97/4.00  unif_index_cands_time:                  0.
% 27.97/4.00  unif_index_add_time:                    0.
% 27.97/4.00  orderings_time:                         0.
% 27.97/4.00  out_proof_time:                         0.032
% 27.97/4.00  total_time:                             3.369
% 27.97/4.00  num_of_symbols:                         55
% 27.97/4.00  num_of_terms:                           107129
% 27.97/4.00  
% 27.97/4.00  ------ Preprocessing
% 27.97/4.00  
% 27.97/4.00  num_of_splits:                          0
% 27.97/4.00  num_of_split_atoms:                     0
% 27.97/4.00  num_of_reused_defs:                     0
% 27.97/4.00  num_eq_ax_congr_red:                    8
% 27.97/4.00  num_of_sem_filtered_clauses:            1
% 27.97/4.00  num_of_subtypes:                        0
% 27.97/4.00  monotx_restored_types:                  0
% 27.97/4.00  sat_num_of_epr_types:                   0
% 27.97/4.00  sat_num_of_non_cyclic_types:            0
% 27.97/4.00  sat_guarded_non_collapsed_types:        0
% 27.97/4.00  num_pure_diseq_elim:                    0
% 27.97/4.00  simp_replaced_by:                       0
% 27.97/4.00  res_preprocessed:                       210
% 27.97/4.00  prep_upred:                             0
% 27.97/4.00  prep_unflattend:                        38
% 27.97/4.00  smt_new_axioms:                         0
% 27.97/4.00  pred_elim_cands:                        6
% 27.97/4.00  pred_elim:                              2
% 27.97/4.00  pred_elim_cl:                           3
% 27.97/4.00  pred_elim_cycles:                       5
% 27.97/4.00  merged_defs:                            0
% 27.97/4.00  merged_defs_ncl:                        0
% 27.97/4.00  bin_hyper_res:                          0
% 27.97/4.00  prep_cycles:                            4
% 27.97/4.00  pred_elim_time:                         0.014
% 27.97/4.00  splitting_time:                         0.
% 27.97/4.00  sem_filter_time:                        0.
% 27.97/4.00  monotx_time:                            0.001
% 27.97/4.00  subtype_inf_time:                       0.
% 27.97/4.00  
% 27.97/4.00  ------ Problem properties
% 27.97/4.00  
% 27.97/4.00  clauses:                                42
% 27.97/4.00  conjectures:                            12
% 27.97/4.00  epr:                                    7
% 27.97/4.00  horn:                                   36
% 27.97/4.00  ground:                                 12
% 27.97/4.00  unary:                                  18
% 27.97/4.00  binary:                                 3
% 27.97/4.00  lits:                                   132
% 27.97/4.00  lits_eq:                                34
% 27.97/4.00  fd_pure:                                0
% 27.97/4.00  fd_pseudo:                              0
% 27.97/4.00  fd_cond:                                5
% 27.97/4.00  fd_pseudo_cond:                         3
% 27.97/4.00  ac_symbols:                             0
% 27.97/4.00  
% 27.97/4.00  ------ Propositional Solver
% 27.97/4.00  
% 27.97/4.00  prop_solver_calls:                      47
% 27.97/4.00  prop_fast_solver_calls:                 5577
% 27.97/4.00  smt_solver_calls:                       0
% 27.97/4.00  smt_fast_solver_calls:                  0
% 27.97/4.00  prop_num_of_clauses:                    40515
% 27.97/4.00  prop_preprocess_simplified:             80384
% 27.97/4.00  prop_fo_subsumed:                       1487
% 27.97/4.00  prop_solver_time:                       0.
% 27.97/4.00  smt_solver_time:                        0.
% 27.97/4.00  smt_fast_solver_time:                   0.
% 27.97/4.00  prop_fast_solver_time:                  0.
% 27.97/4.00  prop_unsat_core_time:                   0.008
% 27.97/4.00  
% 27.97/4.00  ------ QBF
% 27.97/4.00  
% 27.97/4.00  qbf_q_res:                              0
% 27.97/4.00  qbf_num_tautologies:                    0
% 27.97/4.00  qbf_prep_cycles:                        0
% 27.97/4.00  
% 27.97/4.00  ------ BMC1
% 27.97/4.00  
% 27.97/4.00  bmc1_current_bound:                     -1
% 27.97/4.00  bmc1_last_solved_bound:                 -1
% 27.97/4.00  bmc1_unsat_core_size:                   -1
% 27.97/4.00  bmc1_unsat_core_parents_size:           -1
% 27.97/4.00  bmc1_merge_next_fun:                    0
% 27.97/4.00  bmc1_unsat_core_clauses_time:           0.
% 27.97/4.00  
% 27.97/4.00  ------ Instantiation
% 27.97/4.00  
% 27.97/4.00  inst_num_of_clauses:                    4634
% 27.97/4.00  inst_num_in_passive:                    2985
% 27.97/4.00  inst_num_in_active:                     4134
% 27.97/4.00  inst_num_in_unprocessed:                222
% 27.97/4.00  inst_num_of_loops:                      4499
% 27.97/4.00  inst_num_of_learning_restarts:          1
% 27.97/4.00  inst_num_moves_active_passive:          362
% 27.97/4.00  inst_lit_activity:                      0
% 27.97/4.00  inst_lit_activity_moves:                4
% 27.97/4.00  inst_num_tautologies:                   0
% 27.97/4.00  inst_num_prop_implied:                  0
% 27.97/4.00  inst_num_existing_simplified:           0
% 27.97/4.00  inst_num_eq_res_simplified:             0
% 27.97/4.00  inst_num_child_elim:                    0
% 27.97/4.00  inst_num_of_dismatching_blockings:      3631
% 27.97/4.00  inst_num_of_non_proper_insts:           10736
% 27.97/4.00  inst_num_of_duplicates:                 0
% 27.97/4.00  inst_inst_num_from_inst_to_res:         0
% 27.97/4.00  inst_dismatching_checking_time:         0.
% 27.97/4.00  
% 27.97/4.00  ------ Resolution
% 27.97/4.00  
% 27.97/4.00  res_num_of_clauses:                     61
% 27.97/4.00  res_num_in_passive:                     61
% 27.97/4.00  res_num_in_active:                      0
% 27.97/4.00  res_num_of_loops:                       214
% 27.97/4.00  res_forward_subset_subsumed:            576
% 27.97/4.00  res_backward_subset_subsumed:           0
% 27.97/4.00  res_forward_subsumed:                   0
% 27.97/4.00  res_backward_subsumed:                  0
% 27.97/4.00  res_forward_subsumption_resolution:     4
% 27.97/4.00  res_backward_subsumption_resolution:    0
% 27.97/4.00  res_clause_to_clause_subsumption:       12468
% 27.97/4.00  res_orphan_elimination:                 0
% 27.97/4.00  res_tautology_del:                      253
% 27.97/4.00  res_num_eq_res_simplified:              0
% 27.97/4.00  res_num_sel_changes:                    0
% 27.97/4.00  res_moves_from_active_to_pass:          0
% 27.97/4.00  
% 27.97/4.00  ------ Superposition
% 27.97/4.00  
% 27.97/4.00  sup_time_total:                         0.
% 27.97/4.00  sup_time_generating:                    0.
% 27.97/4.00  sup_time_sim_full:                      0.
% 27.97/4.00  sup_time_sim_immed:                     0.
% 27.97/4.00  
% 27.97/4.00  sup_num_of_clauses:                     4642
% 27.97/4.00  sup_num_in_active:                      841
% 27.97/4.00  sup_num_in_passive:                     3801
% 27.97/4.00  sup_num_of_loops:                       898
% 27.97/4.00  sup_fw_superposition:                   1790
% 27.97/4.00  sup_bw_superposition:                   3542
% 27.97/4.00  sup_immediate_simplified:               2834
% 27.97/4.00  sup_given_eliminated:                   1
% 27.97/4.00  comparisons_done:                       0
% 27.97/4.00  comparisons_avoided:                    1
% 27.97/4.00  
% 27.97/4.00  ------ Simplifications
% 27.97/4.00  
% 27.97/4.00  
% 27.97/4.00  sim_fw_subset_subsumed:                 88
% 27.97/4.00  sim_bw_subset_subsumed:                 213
% 27.97/4.00  sim_fw_subsumed:                        50
% 27.97/4.00  sim_bw_subsumed:                        9
% 27.97/4.00  sim_fw_subsumption_res:                 0
% 27.97/4.00  sim_bw_subsumption_res:                 0
% 27.97/4.00  sim_tautology_del:                      0
% 27.97/4.00  sim_eq_tautology_del:                   84
% 27.97/4.00  sim_eq_res_simp:                        2
% 27.97/4.00  sim_fw_demodulated:                     462
% 27.97/4.00  sim_bw_demodulated:                     24
% 27.97/4.00  sim_light_normalised:                   2520
% 27.97/4.00  sim_joinable_taut:                      0
% 27.97/4.00  sim_joinable_simp:                      0
% 27.97/4.00  sim_ac_normalised:                      0
% 27.97/4.00  sim_smt_subsumption:                    0
% 27.97/4.00  
%------------------------------------------------------------------------------
