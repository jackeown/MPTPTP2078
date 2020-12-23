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
% DateTime   : Thu Dec  3 12:07:19 EST 2020

% Result     : Theorem 3.34s
% Output     : CNFRefutation 3.34s
% Verified   : 
% Statistics : Number of formulae       :  234 (17152 expanded)
%              Number of clauses        :  155 (5127 expanded)
%              Number of leaves         :   19 (3362 expanded)
%              Depth                    :   29
%              Number of atoms          :  754 (82134 expanded)
%              Number of equality atoms :  344 (8802 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   13 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f89,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f33])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f47,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f48,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f47])).

fof(f55,plain,
    ( ? [X0,X1] :
        ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
        | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v3_funct_2(sK1,sK0,sK0)
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) )
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK1,sK0,sK0)
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f48,f55])).

fof(f96,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f56])).

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

fof(f37,plain,(
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

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f53,plain,(
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
    inference(nnf_transformation,[],[f38])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f94,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f56])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_1(X1) = k2_funct_2(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f45])).

fof(f91,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f93,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f95,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f56])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f41])).

fof(f88,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f17,axiom,(
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
    inference(ennf_transformation,[],[f17])).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f43])).

fof(f90,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f85,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k2_funct_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f29,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f67,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f19,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f92,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f19])).

fof(f99,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f67,f92])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f35])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f68,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f98,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f68,f92])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f97,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f56])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f66,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f52])).

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

fof(f59,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f87,plain,(
    ! [X0,X1] :
      ( v3_funct_2(k2_funct_2(X0,X1),X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

cnf(c_32,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1552,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_16,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1564,plain,
    ( r2_relset_1(X0,X1,X2,X2) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3445,plain,
    ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0)) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1552,c_1564])).

cnf(c_10260,plain,
    ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1552,c_3445])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1548,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1557,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3473,plain,
    ( k1_relset_1(sK0,sK0,sK1) = sK0
    | sK0 = k1_xboole_0
    | v1_funct_2(sK1,sK0,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1548,c_1557])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1565,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2218,plain,
    ( k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_1548,c_1565])).

cnf(c_3477,plain,
    ( k1_relat_1(sK1) = sK0
    | sK0 = k1_xboole_0
    | v1_funct_2(sK1,sK0,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3473,c_2218])).

cnf(c_38,negated_conjecture,
    ( v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_41,plain,
    ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_3801,plain,
    ( sK0 = k1_xboole_0
    | k1_relat_1(sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3477,c_41])).

cnf(c_3802,plain,
    ( k1_relat_1(sK1) = sK0
    | sK0 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_3801])).

cnf(c_34,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1550,plain,
    ( k2_funct_2(X0,X1) = k2_funct_1(X1)
    | v1_funct_2(X1,X0,X0) != iProver_top
    | v3_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_4493,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1548,c_1550])).

cnf(c_39,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_37,negated_conjecture,
    ( v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1966,plain,
    ( ~ v1_funct_2(sK1,X0,X0)
    | ~ v3_funct_2(sK1,X0,X0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v1_funct_1(sK1)
    | k2_funct_2(X0,sK1) = k2_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_34])).

cnf(c_2207,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1966])).

cnf(c_4958,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4493,c_39,c_38,c_37,c_36,c_2207])).

cnf(c_28,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1556,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_5405,plain,
    ( v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4958,c_1556])).

cnf(c_40,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_42,plain,
    ( v3_funct_2(sK1,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_43,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_6383,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5405,c_40,c_41,c_42,c_43])).

cnf(c_33,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1551,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_6401,plain,
    ( k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6383,c_1551])).

cnf(c_31,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_2(X1,X0)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1553,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_2(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_4263,plain,
    ( v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(k2_funct_2(sK0,sK1)) = iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1548,c_1553])).

cnf(c_1951,plain,
    ( ~ v1_funct_2(sK1,X0,X0)
    | ~ v3_funct_2(sK1,X0,X0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | v1_funct_1(k2_funct_2(X0,sK1))
    | ~ v1_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_2136,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v1_funct_1(k2_funct_2(sK0,sK1))
    | ~ v1_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1951])).

cnf(c_2137,plain,
    ( v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(k2_funct_2(sK0,sK1)) = iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2136])).

cnf(c_4936,plain,
    ( v1_funct_1(k2_funct_2(sK0,sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4263,c_40,c_41,c_42,c_43,c_2137])).

cnf(c_4961,plain,
    ( v1_funct_1(k2_funct_1(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4958,c_4936])).

cnf(c_8956,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6401,c_4961])).

cnf(c_8957,plain,
    ( k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_8956])).

cnf(c_8968,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k5_relat_1(sK1,k2_funct_1(sK1))
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1548,c_8957])).

cnf(c_1545,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_11,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1567,plain,
    ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3350,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
    | v2_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1545,c_1567])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1849,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1884,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_18,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1909,plain,
    ( ~ v3_funct_2(sK1,X0,X1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK1)
    | v2_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_2066,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | v2_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1909])).

cnf(c_3702,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3350,c_39,c_37,c_36,c_1849,c_1884,c_2066])).

cnf(c_8976,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
    | v1_funct_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8968,c_3702])).

cnf(c_9466,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8976,c_40])).

cnf(c_5647,plain,
    ( k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1548,c_1551])).

cnf(c_6126,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5647,c_40])).

cnf(c_6127,plain,
    ( k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_6126])).

cnf(c_6136,plain,
    ( k1_partfun1(X0,X0,sK0,sK0,k2_funct_2(X0,X1),sK1) = k5_relat_1(k2_funct_2(X0,X1),sK1)
    | v1_funct_2(X1,X0,X0) != iProver_top
    | v3_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(k2_funct_2(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1556,c_6127])).

cnf(c_6539,plain,
    ( k1_partfun1(X0,X0,sK0,sK0,k2_funct_2(X0,X1),sK1) = k5_relat_1(k2_funct_2(X0,X1),sK1)
    | v1_funct_2(X1,X0,X0) != iProver_top
    | v3_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6136,c_1553])).

cnf(c_6546,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1) = k5_relat_1(k2_funct_2(sK0,sK1),sK1)
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1548,c_6539])).

cnf(c_10,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1568,plain,
    ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3357,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1))
    | v2_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1545,c_1568])).

cnf(c_17,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_27,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_461,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ v5_relat_1(X3,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X3)
    | X3 != X0
    | X4 != X2
    | k2_relat_1(X3) = X4 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_27])).

cnf(c_462,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ v5_relat_1(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(unflattening,[status(thm)],[c_461])).

cnf(c_466,plain,
    ( ~ v1_funct_1(X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v5_relat_1(X0,X2)
    | ~ v3_funct_2(X0,X1,X2)
    | k2_relat_1(X0) = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_462,c_12])).

cnf(c_467,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ v5_relat_1(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(renaming,[status(thm)],[c_466])).

cnf(c_13,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_482,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_467,c_13])).

cnf(c_1543,plain,
    ( k2_relat_1(X0) = X1
    | v3_funct_2(X0,X2,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_482])).

cnf(c_2550,plain,
    ( k2_relat_1(sK1) = sK0
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1548,c_1543])).

cnf(c_1929,plain,
    ( ~ v3_funct_2(sK1,X0,X1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK1)
    | k2_relat_1(sK1) = X1 ),
    inference(instantiation,[status(thm)],[c_482])).

cnf(c_2103,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | k2_relat_1(sK1) = sK0 ),
    inference(instantiation,[status(thm)],[c_1929])).

cnf(c_2912,plain,
    ( k2_relat_1(sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2550,c_39,c_37,c_36,c_2103])).

cnf(c_3358,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
    | v2_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3357,c_2912])).

cnf(c_1850,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1849])).

cnf(c_2067,plain,
    ( v3_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v2_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2066])).

cnf(c_3797,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3358,c_40,c_42,c_43,c_1850,c_2067])).

cnf(c_6560,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6546,c_3797,c_4958])).

cnf(c_6388,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k5_relat_1(k2_funct_1(sK1),sK1)
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6383,c_6127])).

cnf(c_6475,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6388,c_3797])).

cnf(c_6609,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6560,c_4961,c_6475])).

cnf(c_35,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1549,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) != iProver_top
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_4962,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) != iProver_top
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4958,c_1549])).

cnf(c_6612,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top
    | r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6609,c_4962])).

cnf(c_9469,plain,
    ( r2_relset_1(sK0,sK0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(sK0)) != iProver_top
    | r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9466,c_6612])).

cnf(c_9582,plain,
    ( sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3802,c_9469])).

cnf(c_10272,plain,
    ( sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_10260,c_9582])).

cnf(c_10612,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(k1_xboole_0)) != iProver_top
    | r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),k6_partfun1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10272,c_9469])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1570,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2916,plain,
    ( sK1 = k1_xboole_0
    | sK0 != k1_xboole_0
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2912,c_1570])).

cnf(c_2917,plain,
    ( ~ v1_relat_1(sK1)
    | sK1 = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2916])).

cnf(c_2919,plain,
    ( sK0 != k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2916,c_36,c_1849,c_2917])).

cnf(c_2920,plain,
    ( sK1 = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_2919])).

cnf(c_10640,plain,
    ( sK1 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_10272,c_2920])).

cnf(c_10656,plain,
    ( sK1 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_10640])).

cnf(c_10614,plain,
    ( k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
    inference(demodulation,[status(thm)],[c_10272,c_9466])).

cnf(c_7,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_497,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_13,c_7])).

cnf(c_501,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_497,c_12])).

cnf(c_502,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_501])).

cnf(c_1542,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_502])).

cnf(c_6395,plain,
    ( r1_tarski(k2_relat_1(k2_funct_1(sK1)),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6383,c_1542])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1573,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_7317,plain,
    ( k2_relat_1(k2_funct_1(sK1)) = sK0
    | r1_tarski(sK0,k2_relat_1(k2_funct_1(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6395,c_1573])).

cnf(c_29,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | v3_funct_2(k2_funct_2(X1,X0),X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1555,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(k2_funct_2(X1,X0),X1,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_5211,plain,
    ( v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) = iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1548,c_1555])).

cnf(c_5216,plain,
    ( v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(k2_funct_1(sK1),sK0,sK0) = iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5211,c_4958])).

cnf(c_6396,plain,
    ( k2_relat_1(k2_funct_1(sK1)) = sK0
    | v3_funct_2(k2_funct_1(sK1),sK0,sK0) != iProver_top
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6383,c_1543])).

cnf(c_8434,plain,
    ( k2_relat_1(k2_funct_1(sK1)) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7317,c_40,c_41,c_42,c_4961,c_5216,c_6396])).

cnf(c_8441,plain,
    ( k2_funct_1(sK1) = k1_xboole_0
    | sK0 != k1_xboole_0
    | v1_relat_1(k2_funct_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8434,c_1570])).

cnf(c_1566,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_6394,plain,
    ( v1_relat_1(k2_funct_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6383,c_1566])).

cnf(c_8605,plain,
    ( sK0 != k1_xboole_0
    | k2_funct_1(sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8441,c_6394])).

cnf(c_8606,plain,
    ( k2_funct_1(sK1) = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_8605])).

cnf(c_10619,plain,
    ( k2_funct_1(sK1) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_10272,c_8606])).

cnf(c_10745,plain,
    ( k2_funct_1(sK1) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_10619])).

cnf(c_10746,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_10745,c_10656])).

cnf(c_10636,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_10272,c_3797])).

cnf(c_10679,plain,
    ( k5_relat_1(k2_funct_1(k1_xboole_0),k1_xboole_0) = k6_partfun1(k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_10636,c_10656])).

cnf(c_10758,plain,
    ( k5_relat_1(k1_xboole_0,k1_xboole_0) = k6_partfun1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_10746,c_10679])).

cnf(c_6138,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK1) = k5_relat_1(sK1,sK1)
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1548,c_6127])).

cnf(c_1986,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK1)
    | k1_partfun1(X1,X2,X3,X4,X0,sK1) = k5_relat_1(X0,sK1) ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_2235,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(sK1)
    | k1_partfun1(X0,X1,X2,X3,sK1,sK1) = k5_relat_1(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_1986])).

cnf(c_2581,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | k1_partfun1(sK0,sK0,X0,X1,sK1,sK1) = k5_relat_1(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_2235])).

cnf(c_2674,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK1) = k5_relat_1(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_2581])).

cnf(c_6174,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK1) = k5_relat_1(sK1,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6138,c_39,c_36,c_2674])).

cnf(c_10631,plain,
    ( k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK1,sK1) = k5_relat_1(sK1,sK1) ),
    inference(demodulation,[status(thm)],[c_10272,c_6174])).

cnf(c_10695,plain,
    ( k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k5_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_10631,c_10656])).

cnf(c_10762,plain,
    ( k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k6_partfun1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_10758,c_10695])).

cnf(c_10776,plain,
    ( k6_partfun1(k1_relat_1(k1_xboole_0)) = k6_partfun1(k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_10614,c_10656,c_10746,c_10762])).

cnf(c_10780,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),k6_partfun1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10612,c_10656,c_10776])).

cnf(c_1936,plain,
    ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1937,plain,
    ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0)) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1936])).

cnf(c_1939,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),k6_partfun1(k1_xboole_0)) = iProver_top
    | m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1937])).

cnf(c_3,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1837,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1840,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1837])).

cnf(c_1842,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1840])).

cnf(c_51,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_53,plain,
    ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_51])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10780,c_1939,c_1842,c_53])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : iproveropt_run.sh %d %s
% 0.11/0.32  % Computer   : n005.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 14:34:02 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  % Running in FOF mode
% 3.34/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.34/0.98  
% 3.34/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.34/0.98  
% 3.34/0.98  ------  iProver source info
% 3.34/0.98  
% 3.34/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.34/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.34/0.98  git: non_committed_changes: false
% 3.34/0.98  git: last_make_outside_of_git: false
% 3.34/0.98  
% 3.34/0.98  ------ 
% 3.34/0.98  
% 3.34/0.98  ------ Input Options
% 3.34/0.98  
% 3.34/0.98  --out_options                           all
% 3.34/0.98  --tptp_safe_out                         true
% 3.34/0.98  --problem_path                          ""
% 3.34/0.98  --include_path                          ""
% 3.34/0.98  --clausifier                            res/vclausify_rel
% 3.34/0.98  --clausifier_options                    --mode clausify
% 3.34/0.98  --stdin                                 false
% 3.34/0.98  --stats_out                             all
% 3.34/0.98  
% 3.34/0.98  ------ General Options
% 3.34/0.98  
% 3.34/0.98  --fof                                   false
% 3.34/0.98  --time_out_real                         305.
% 3.34/0.98  --time_out_virtual                      -1.
% 3.34/0.98  --symbol_type_check                     false
% 3.34/0.98  --clausify_out                          false
% 3.34/0.98  --sig_cnt_out                           false
% 3.34/0.98  --trig_cnt_out                          false
% 3.34/0.98  --trig_cnt_out_tolerance                1.
% 3.34/0.98  --trig_cnt_out_sk_spl                   false
% 3.34/0.98  --abstr_cl_out                          false
% 3.34/0.98  
% 3.34/0.98  ------ Global Options
% 3.34/0.98  
% 3.34/0.98  --schedule                              default
% 3.34/0.98  --add_important_lit                     false
% 3.34/0.98  --prop_solver_per_cl                    1000
% 3.34/0.98  --min_unsat_core                        false
% 3.34/0.98  --soft_assumptions                      false
% 3.34/0.98  --soft_lemma_size                       3
% 3.34/0.98  --prop_impl_unit_size                   0
% 3.34/0.98  --prop_impl_unit                        []
% 3.34/0.98  --share_sel_clauses                     true
% 3.34/0.98  --reset_solvers                         false
% 3.34/0.98  --bc_imp_inh                            [conj_cone]
% 3.34/0.98  --conj_cone_tolerance                   3.
% 3.34/0.98  --extra_neg_conj                        none
% 3.34/0.98  --large_theory_mode                     true
% 3.34/0.98  --prolific_symb_bound                   200
% 3.34/0.98  --lt_threshold                          2000
% 3.34/0.98  --clause_weak_htbl                      true
% 3.34/0.98  --gc_record_bc_elim                     false
% 3.34/0.98  
% 3.34/0.98  ------ Preprocessing Options
% 3.34/0.98  
% 3.34/0.98  --preprocessing_flag                    true
% 3.34/0.98  --time_out_prep_mult                    0.1
% 3.34/0.98  --splitting_mode                        input
% 3.34/0.98  --splitting_grd                         true
% 3.34/0.98  --splitting_cvd                         false
% 3.34/0.98  --splitting_cvd_svl                     false
% 3.34/0.98  --splitting_nvd                         32
% 3.34/0.98  --sub_typing                            true
% 3.34/0.98  --prep_gs_sim                           true
% 3.34/0.98  --prep_unflatten                        true
% 3.34/0.98  --prep_res_sim                          true
% 3.34/0.98  --prep_upred                            true
% 3.34/0.98  --prep_sem_filter                       exhaustive
% 3.34/0.98  --prep_sem_filter_out                   false
% 3.34/0.98  --pred_elim                             true
% 3.34/0.98  --res_sim_input                         true
% 3.34/0.98  --eq_ax_congr_red                       true
% 3.34/0.98  --pure_diseq_elim                       true
% 3.34/0.98  --brand_transform                       false
% 3.34/0.98  --non_eq_to_eq                          false
% 3.34/0.98  --prep_def_merge                        true
% 3.34/0.98  --prep_def_merge_prop_impl              false
% 3.34/0.98  --prep_def_merge_mbd                    true
% 3.34/0.98  --prep_def_merge_tr_red                 false
% 3.34/0.98  --prep_def_merge_tr_cl                  false
% 3.34/0.98  --smt_preprocessing                     true
% 3.34/0.98  --smt_ac_axioms                         fast
% 3.34/0.98  --preprocessed_out                      false
% 3.34/0.98  --preprocessed_stats                    false
% 3.34/0.98  
% 3.34/0.98  ------ Abstraction refinement Options
% 3.34/0.98  
% 3.34/0.98  --abstr_ref                             []
% 3.34/0.98  --abstr_ref_prep                        false
% 3.34/0.98  --abstr_ref_until_sat                   false
% 3.34/0.98  --abstr_ref_sig_restrict                funpre
% 3.34/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.34/0.98  --abstr_ref_under                       []
% 3.34/0.98  
% 3.34/0.98  ------ SAT Options
% 3.34/0.98  
% 3.34/0.98  --sat_mode                              false
% 3.34/0.98  --sat_fm_restart_options                ""
% 3.34/0.98  --sat_gr_def                            false
% 3.34/0.98  --sat_epr_types                         true
% 3.34/0.98  --sat_non_cyclic_types                  false
% 3.34/0.98  --sat_finite_models                     false
% 3.34/0.98  --sat_fm_lemmas                         false
% 3.34/0.98  --sat_fm_prep                           false
% 3.34/0.98  --sat_fm_uc_incr                        true
% 3.34/0.98  --sat_out_model                         small
% 3.34/0.98  --sat_out_clauses                       false
% 3.34/0.98  
% 3.34/0.98  ------ QBF Options
% 3.34/0.98  
% 3.34/0.98  --qbf_mode                              false
% 3.34/0.98  --qbf_elim_univ                         false
% 3.34/0.98  --qbf_dom_inst                          none
% 3.34/0.98  --qbf_dom_pre_inst                      false
% 3.34/0.98  --qbf_sk_in                             false
% 3.34/0.98  --qbf_pred_elim                         true
% 3.34/0.98  --qbf_split                             512
% 3.34/0.98  
% 3.34/0.98  ------ BMC1 Options
% 3.34/0.98  
% 3.34/0.98  --bmc1_incremental                      false
% 3.34/0.98  --bmc1_axioms                           reachable_all
% 3.34/0.98  --bmc1_min_bound                        0
% 3.34/0.98  --bmc1_max_bound                        -1
% 3.34/0.98  --bmc1_max_bound_default                -1
% 3.34/0.98  --bmc1_symbol_reachability              true
% 3.34/0.98  --bmc1_property_lemmas                  false
% 3.34/0.98  --bmc1_k_induction                      false
% 3.34/0.98  --bmc1_non_equiv_states                 false
% 3.34/0.98  --bmc1_deadlock                         false
% 3.34/0.98  --bmc1_ucm                              false
% 3.34/0.98  --bmc1_add_unsat_core                   none
% 3.34/0.98  --bmc1_unsat_core_children              false
% 3.34/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.34/0.98  --bmc1_out_stat                         full
% 3.34/0.98  --bmc1_ground_init                      false
% 3.34/0.98  --bmc1_pre_inst_next_state              false
% 3.34/0.98  --bmc1_pre_inst_state                   false
% 3.34/0.98  --bmc1_pre_inst_reach_state             false
% 3.34/0.98  --bmc1_out_unsat_core                   false
% 3.34/0.98  --bmc1_aig_witness_out                  false
% 3.34/0.98  --bmc1_verbose                          false
% 3.34/0.98  --bmc1_dump_clauses_tptp                false
% 3.34/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.34/0.98  --bmc1_dump_file                        -
% 3.34/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.34/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.34/0.98  --bmc1_ucm_extend_mode                  1
% 3.34/0.98  --bmc1_ucm_init_mode                    2
% 3.34/0.98  --bmc1_ucm_cone_mode                    none
% 3.34/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.34/0.98  --bmc1_ucm_relax_model                  4
% 3.34/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.34/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.34/0.98  --bmc1_ucm_layered_model                none
% 3.34/0.98  --bmc1_ucm_max_lemma_size               10
% 3.34/0.98  
% 3.34/0.98  ------ AIG Options
% 3.34/0.98  
% 3.34/0.98  --aig_mode                              false
% 3.34/0.98  
% 3.34/0.98  ------ Instantiation Options
% 3.34/0.98  
% 3.34/0.98  --instantiation_flag                    true
% 3.34/0.98  --inst_sos_flag                         false
% 3.34/0.98  --inst_sos_phase                        true
% 3.34/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.34/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.34/0.98  --inst_lit_sel_side                     num_symb
% 3.34/0.98  --inst_solver_per_active                1400
% 3.34/0.98  --inst_solver_calls_frac                1.
% 3.34/0.98  --inst_passive_queue_type               priority_queues
% 3.34/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.34/0.98  --inst_passive_queues_freq              [25;2]
% 3.34/0.98  --inst_dismatching                      true
% 3.34/0.98  --inst_eager_unprocessed_to_passive     true
% 3.34/0.98  --inst_prop_sim_given                   true
% 3.34/0.98  --inst_prop_sim_new                     false
% 3.34/0.98  --inst_subs_new                         false
% 3.34/0.98  --inst_eq_res_simp                      false
% 3.34/0.98  --inst_subs_given                       false
% 3.34/0.98  --inst_orphan_elimination               true
% 3.34/0.98  --inst_learning_loop_flag               true
% 3.34/0.98  --inst_learning_start                   3000
% 3.34/0.98  --inst_learning_factor                  2
% 3.34/0.98  --inst_start_prop_sim_after_learn       3
% 3.34/0.98  --inst_sel_renew                        solver
% 3.34/0.98  --inst_lit_activity_flag                true
% 3.34/0.98  --inst_restr_to_given                   false
% 3.34/0.98  --inst_activity_threshold               500
% 3.34/0.98  --inst_out_proof                        true
% 3.34/0.98  
% 3.34/0.98  ------ Resolution Options
% 3.34/0.98  
% 3.34/0.98  --resolution_flag                       true
% 3.34/0.98  --res_lit_sel                           adaptive
% 3.34/0.98  --res_lit_sel_side                      none
% 3.34/0.98  --res_ordering                          kbo
% 3.34/0.98  --res_to_prop_solver                    active
% 3.34/0.98  --res_prop_simpl_new                    false
% 3.34/0.98  --res_prop_simpl_given                  true
% 3.34/0.98  --res_passive_queue_type                priority_queues
% 3.34/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.34/0.98  --res_passive_queues_freq               [15;5]
% 3.34/0.98  --res_forward_subs                      full
% 3.34/0.98  --res_backward_subs                     full
% 3.34/0.98  --res_forward_subs_resolution           true
% 3.34/0.98  --res_backward_subs_resolution          true
% 3.34/0.98  --res_orphan_elimination                true
% 3.34/0.98  --res_time_limit                        2.
% 3.34/0.98  --res_out_proof                         true
% 3.34/0.98  
% 3.34/0.98  ------ Superposition Options
% 3.34/0.98  
% 3.34/0.98  --superposition_flag                    true
% 3.34/0.98  --sup_passive_queue_type                priority_queues
% 3.34/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.34/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.34/0.98  --demod_completeness_check              fast
% 3.34/0.98  --demod_use_ground                      true
% 3.34/0.98  --sup_to_prop_solver                    passive
% 3.34/0.98  --sup_prop_simpl_new                    true
% 3.34/0.98  --sup_prop_simpl_given                  true
% 3.34/0.98  --sup_fun_splitting                     false
% 3.34/0.98  --sup_smt_interval                      50000
% 3.34/0.98  
% 3.34/0.98  ------ Superposition Simplification Setup
% 3.34/0.98  
% 3.34/0.98  --sup_indices_passive                   []
% 3.34/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.34/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/0.98  --sup_full_bw                           [BwDemod]
% 3.34/0.98  --sup_immed_triv                        [TrivRules]
% 3.34/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.34/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/0.98  --sup_immed_bw_main                     []
% 3.34/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.34/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.34/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.34/0.98  
% 3.34/0.98  ------ Combination Options
% 3.34/0.98  
% 3.34/0.98  --comb_res_mult                         3
% 3.34/0.98  --comb_sup_mult                         2
% 3.34/0.98  --comb_inst_mult                        10
% 3.34/0.98  
% 3.34/0.98  ------ Debug Options
% 3.34/0.98  
% 3.34/0.98  --dbg_backtrace                         false
% 3.34/0.98  --dbg_dump_prop_clauses                 false
% 3.34/0.98  --dbg_dump_prop_clauses_file            -
% 3.34/0.98  --dbg_out_stat                          false
% 3.34/0.98  ------ Parsing...
% 3.34/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.34/0.98  
% 3.34/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.34/0.98  
% 3.34/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.34/0.98  
% 3.34/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.34/0.98  ------ Proving...
% 3.34/0.98  ------ Problem Properties 
% 3.34/0.98  
% 3.34/0.98  
% 3.34/0.98  clauses                                 32
% 3.34/0.98  conjectures                             5
% 3.34/0.98  EPR                                     5
% 3.34/0.98  Horn                                    28
% 3.34/0.98  unary                                   7
% 3.34/0.98  binary                                  5
% 3.34/0.98  lits                                    96
% 3.34/0.98  lits eq                                 20
% 3.34/0.98  fd_pure                                 0
% 3.34/0.98  fd_pseudo                               0
% 3.34/0.98  fd_cond                                 5
% 3.34/0.98  fd_pseudo_cond                          2
% 3.34/0.98  AC symbols                              0
% 3.34/0.98  
% 3.34/0.98  ------ Schedule dynamic 5 is on 
% 3.34/0.98  
% 3.34/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.34/0.98  
% 3.34/0.98  
% 3.34/0.98  ------ 
% 3.34/0.98  Current options:
% 3.34/0.98  ------ 
% 3.34/0.98  
% 3.34/0.98  ------ Input Options
% 3.34/0.98  
% 3.34/0.98  --out_options                           all
% 3.34/0.98  --tptp_safe_out                         true
% 3.34/0.98  --problem_path                          ""
% 3.34/0.98  --include_path                          ""
% 3.34/0.98  --clausifier                            res/vclausify_rel
% 3.34/0.98  --clausifier_options                    --mode clausify
% 3.34/0.98  --stdin                                 false
% 3.34/0.98  --stats_out                             all
% 3.34/0.98  
% 3.34/0.98  ------ General Options
% 3.34/0.98  
% 3.34/0.98  --fof                                   false
% 3.34/0.98  --time_out_real                         305.
% 3.34/0.98  --time_out_virtual                      -1.
% 3.34/0.98  --symbol_type_check                     false
% 3.34/0.98  --clausify_out                          false
% 3.34/0.98  --sig_cnt_out                           false
% 3.34/0.98  --trig_cnt_out                          false
% 3.34/0.98  --trig_cnt_out_tolerance                1.
% 3.34/0.98  --trig_cnt_out_sk_spl                   false
% 3.34/0.98  --abstr_cl_out                          false
% 3.34/0.98  
% 3.34/0.98  ------ Global Options
% 3.34/0.98  
% 3.34/0.98  --schedule                              default
% 3.34/0.98  --add_important_lit                     false
% 3.34/0.98  --prop_solver_per_cl                    1000
% 3.34/0.98  --min_unsat_core                        false
% 3.34/0.98  --soft_assumptions                      false
% 3.34/0.98  --soft_lemma_size                       3
% 3.34/0.98  --prop_impl_unit_size                   0
% 3.34/0.98  --prop_impl_unit                        []
% 3.34/0.98  --share_sel_clauses                     true
% 3.34/0.98  --reset_solvers                         false
% 3.34/0.98  --bc_imp_inh                            [conj_cone]
% 3.34/0.98  --conj_cone_tolerance                   3.
% 3.34/0.98  --extra_neg_conj                        none
% 3.34/0.98  --large_theory_mode                     true
% 3.34/0.98  --prolific_symb_bound                   200
% 3.34/0.98  --lt_threshold                          2000
% 3.34/0.98  --clause_weak_htbl                      true
% 3.34/0.98  --gc_record_bc_elim                     false
% 3.34/0.98  
% 3.34/0.98  ------ Preprocessing Options
% 3.34/0.98  
% 3.34/0.98  --preprocessing_flag                    true
% 3.34/0.98  --time_out_prep_mult                    0.1
% 3.34/0.98  --splitting_mode                        input
% 3.34/0.98  --splitting_grd                         true
% 3.34/0.98  --splitting_cvd                         false
% 3.34/0.98  --splitting_cvd_svl                     false
% 3.34/0.98  --splitting_nvd                         32
% 3.34/0.98  --sub_typing                            true
% 3.34/0.98  --prep_gs_sim                           true
% 3.34/0.98  --prep_unflatten                        true
% 3.34/0.98  --prep_res_sim                          true
% 3.34/0.98  --prep_upred                            true
% 3.34/0.98  --prep_sem_filter                       exhaustive
% 3.34/0.98  --prep_sem_filter_out                   false
% 3.34/0.98  --pred_elim                             true
% 3.34/0.98  --res_sim_input                         true
% 3.34/0.98  --eq_ax_congr_red                       true
% 3.34/0.98  --pure_diseq_elim                       true
% 3.34/0.98  --brand_transform                       false
% 3.34/0.98  --non_eq_to_eq                          false
% 3.34/0.98  --prep_def_merge                        true
% 3.34/0.98  --prep_def_merge_prop_impl              false
% 3.34/0.98  --prep_def_merge_mbd                    true
% 3.34/0.98  --prep_def_merge_tr_red                 false
% 3.34/0.98  --prep_def_merge_tr_cl                  false
% 3.34/0.98  --smt_preprocessing                     true
% 3.34/0.98  --smt_ac_axioms                         fast
% 3.34/0.98  --preprocessed_out                      false
% 3.34/0.98  --preprocessed_stats                    false
% 3.34/0.98  
% 3.34/0.98  ------ Abstraction refinement Options
% 3.34/0.98  
% 3.34/0.98  --abstr_ref                             []
% 3.34/0.98  --abstr_ref_prep                        false
% 3.34/0.98  --abstr_ref_until_sat                   false
% 3.34/0.98  --abstr_ref_sig_restrict                funpre
% 3.34/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.34/0.98  --abstr_ref_under                       []
% 3.34/0.98  
% 3.34/0.98  ------ SAT Options
% 3.34/0.98  
% 3.34/0.98  --sat_mode                              false
% 3.34/0.98  --sat_fm_restart_options                ""
% 3.34/0.98  --sat_gr_def                            false
% 3.34/0.98  --sat_epr_types                         true
% 3.34/0.98  --sat_non_cyclic_types                  false
% 3.34/0.98  --sat_finite_models                     false
% 3.34/0.98  --sat_fm_lemmas                         false
% 3.34/0.98  --sat_fm_prep                           false
% 3.34/0.98  --sat_fm_uc_incr                        true
% 3.34/0.98  --sat_out_model                         small
% 3.34/0.98  --sat_out_clauses                       false
% 3.34/0.98  
% 3.34/0.98  ------ QBF Options
% 3.34/0.98  
% 3.34/0.98  --qbf_mode                              false
% 3.34/0.98  --qbf_elim_univ                         false
% 3.34/0.98  --qbf_dom_inst                          none
% 3.34/0.98  --qbf_dom_pre_inst                      false
% 3.34/0.98  --qbf_sk_in                             false
% 3.34/0.98  --qbf_pred_elim                         true
% 3.34/0.98  --qbf_split                             512
% 3.34/0.98  
% 3.34/0.98  ------ BMC1 Options
% 3.34/0.98  
% 3.34/0.98  --bmc1_incremental                      false
% 3.34/0.98  --bmc1_axioms                           reachable_all
% 3.34/0.98  --bmc1_min_bound                        0
% 3.34/0.98  --bmc1_max_bound                        -1
% 3.34/0.98  --bmc1_max_bound_default                -1
% 3.34/0.98  --bmc1_symbol_reachability              true
% 3.34/0.98  --bmc1_property_lemmas                  false
% 3.34/0.98  --bmc1_k_induction                      false
% 3.34/0.98  --bmc1_non_equiv_states                 false
% 3.34/0.98  --bmc1_deadlock                         false
% 3.34/0.98  --bmc1_ucm                              false
% 3.34/0.98  --bmc1_add_unsat_core                   none
% 3.34/0.98  --bmc1_unsat_core_children              false
% 3.34/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.34/0.98  --bmc1_out_stat                         full
% 3.34/0.98  --bmc1_ground_init                      false
% 3.34/0.98  --bmc1_pre_inst_next_state              false
% 3.34/0.98  --bmc1_pre_inst_state                   false
% 3.34/0.98  --bmc1_pre_inst_reach_state             false
% 3.34/0.98  --bmc1_out_unsat_core                   false
% 3.34/0.98  --bmc1_aig_witness_out                  false
% 3.34/0.98  --bmc1_verbose                          false
% 3.34/0.98  --bmc1_dump_clauses_tptp                false
% 3.34/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.34/0.98  --bmc1_dump_file                        -
% 3.34/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.34/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.34/0.98  --bmc1_ucm_extend_mode                  1
% 3.34/0.98  --bmc1_ucm_init_mode                    2
% 3.34/0.98  --bmc1_ucm_cone_mode                    none
% 3.34/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.34/0.98  --bmc1_ucm_relax_model                  4
% 3.34/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.34/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.34/0.98  --bmc1_ucm_layered_model                none
% 3.34/0.98  --bmc1_ucm_max_lemma_size               10
% 3.34/0.98  
% 3.34/0.98  ------ AIG Options
% 3.34/0.98  
% 3.34/0.98  --aig_mode                              false
% 3.34/0.98  
% 3.34/0.98  ------ Instantiation Options
% 3.34/0.98  
% 3.34/0.98  --instantiation_flag                    true
% 3.34/0.98  --inst_sos_flag                         false
% 3.34/0.98  --inst_sos_phase                        true
% 3.34/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.34/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.34/0.98  --inst_lit_sel_side                     none
% 3.34/0.98  --inst_solver_per_active                1400
% 3.34/0.98  --inst_solver_calls_frac                1.
% 3.34/0.98  --inst_passive_queue_type               priority_queues
% 3.34/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.34/0.98  --inst_passive_queues_freq              [25;2]
% 3.34/0.98  --inst_dismatching                      true
% 3.34/0.98  --inst_eager_unprocessed_to_passive     true
% 3.34/0.98  --inst_prop_sim_given                   true
% 3.34/0.98  --inst_prop_sim_new                     false
% 3.34/0.98  --inst_subs_new                         false
% 3.34/0.98  --inst_eq_res_simp                      false
% 3.34/0.98  --inst_subs_given                       false
% 3.34/0.98  --inst_orphan_elimination               true
% 3.34/0.98  --inst_learning_loop_flag               true
% 3.34/0.98  --inst_learning_start                   3000
% 3.34/0.98  --inst_learning_factor                  2
% 3.34/0.98  --inst_start_prop_sim_after_learn       3
% 3.34/0.98  --inst_sel_renew                        solver
% 3.34/0.98  --inst_lit_activity_flag                true
% 3.34/0.98  --inst_restr_to_given                   false
% 3.34/0.98  --inst_activity_threshold               500
% 3.34/0.98  --inst_out_proof                        true
% 3.34/0.98  
% 3.34/0.98  ------ Resolution Options
% 3.34/0.98  
% 3.34/0.98  --resolution_flag                       false
% 3.34/0.98  --res_lit_sel                           adaptive
% 3.34/0.98  --res_lit_sel_side                      none
% 3.34/0.98  --res_ordering                          kbo
% 3.34/0.98  --res_to_prop_solver                    active
% 3.34/0.98  --res_prop_simpl_new                    false
% 3.34/0.98  --res_prop_simpl_given                  true
% 3.34/0.98  --res_passive_queue_type                priority_queues
% 3.34/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.34/0.98  --res_passive_queues_freq               [15;5]
% 3.34/0.98  --res_forward_subs                      full
% 3.34/0.98  --res_backward_subs                     full
% 3.34/0.98  --res_forward_subs_resolution           true
% 3.34/0.98  --res_backward_subs_resolution          true
% 3.34/0.98  --res_orphan_elimination                true
% 3.34/0.98  --res_time_limit                        2.
% 3.34/0.98  --res_out_proof                         true
% 3.34/0.98  
% 3.34/0.98  ------ Superposition Options
% 3.34/0.98  
% 3.34/0.98  --superposition_flag                    true
% 3.34/0.98  --sup_passive_queue_type                priority_queues
% 3.34/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.34/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.34/0.98  --demod_completeness_check              fast
% 3.34/0.98  --demod_use_ground                      true
% 3.34/0.98  --sup_to_prop_solver                    passive
% 3.34/0.98  --sup_prop_simpl_new                    true
% 3.34/0.98  --sup_prop_simpl_given                  true
% 3.34/0.98  --sup_fun_splitting                     false
% 3.34/0.98  --sup_smt_interval                      50000
% 3.34/0.98  
% 3.34/0.98  ------ Superposition Simplification Setup
% 3.34/0.98  
% 3.34/0.98  --sup_indices_passive                   []
% 3.34/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.34/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/0.98  --sup_full_bw                           [BwDemod]
% 3.34/0.98  --sup_immed_triv                        [TrivRules]
% 3.34/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.34/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/0.98  --sup_immed_bw_main                     []
% 3.34/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.34/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.34/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.34/0.98  
% 3.34/0.98  ------ Combination Options
% 3.34/0.98  
% 3.34/0.98  --comb_res_mult                         3
% 3.34/0.98  --comb_sup_mult                         2
% 3.34/0.98  --comb_inst_mult                        10
% 3.34/0.98  
% 3.34/0.98  ------ Debug Options
% 3.34/0.98  
% 3.34/0.98  --dbg_backtrace                         false
% 3.34/0.98  --dbg_dump_prop_clauses                 false
% 3.34/0.98  --dbg_dump_prop_clauses_file            -
% 3.34/0.98  --dbg_out_stat                          false
% 3.34/0.98  
% 3.34/0.98  
% 3.34/0.98  
% 3.34/0.98  
% 3.34/0.98  ------ Proving...
% 3.34/0.98  
% 3.34/0.98  
% 3.34/0.98  % SZS status Theorem for theBenchmark.p
% 3.34/0.98  
% 3.34/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.34/0.98  
% 3.34/0.98  fof(f16,axiom,(
% 3.34/0.98    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 3.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f22,plain,(
% 3.34/0.98    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.34/0.98    inference(pure_predicate_removal,[],[f16])).
% 3.34/0.98  
% 3.34/0.98  fof(f89,plain,(
% 3.34/0.98    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.34/0.98    inference(cnf_transformation,[],[f22])).
% 3.34/0.98  
% 3.34/0.98  fof(f11,axiom,(
% 3.34/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 3.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f33,plain,(
% 3.34/0.98    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.34/0.98    inference(ennf_transformation,[],[f11])).
% 3.34/0.98  
% 3.34/0.98  fof(f34,plain,(
% 3.34/0.98    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.34/0.98    inference(flattening,[],[f33])).
% 3.34/0.98  
% 3.34/0.98  fof(f73,plain,(
% 3.34/0.98    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.34/0.98    inference(cnf_transformation,[],[f34])).
% 3.34/0.98  
% 3.34/0.98  fof(f20,conjecture,(
% 3.34/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 3.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f21,negated_conjecture,(
% 3.34/0.98    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 3.34/0.98    inference(negated_conjecture,[],[f20])).
% 3.34/0.98  
% 3.34/0.98  fof(f47,plain,(
% 3.34/0.98    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 3.34/0.98    inference(ennf_transformation,[],[f21])).
% 3.34/0.98  
% 3.34/0.98  fof(f48,plain,(
% 3.34/0.98    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 3.34/0.98    inference(flattening,[],[f47])).
% 3.34/0.98  
% 3.34/0.98  fof(f55,plain,(
% 3.34/0.98    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 3.34/0.98    introduced(choice_axiom,[])).
% 3.34/0.98  
% 3.34/0.98  fof(f56,plain,(
% 3.34/0.98    (~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 3.34/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f48,f55])).
% 3.34/0.98  
% 3.34/0.98  fof(f96,plain,(
% 3.34/0.98    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.34/0.98    inference(cnf_transformation,[],[f56])).
% 3.34/0.98  
% 3.34/0.98  fof(f13,axiom,(
% 3.34/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f37,plain,(
% 3.34/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.34/0.98    inference(ennf_transformation,[],[f13])).
% 3.34/0.98  
% 3.34/0.98  fof(f38,plain,(
% 3.34/0.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.34/0.98    inference(flattening,[],[f37])).
% 3.34/0.98  
% 3.34/0.98  fof(f53,plain,(
% 3.34/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.34/0.98    inference(nnf_transformation,[],[f38])).
% 3.34/0.98  
% 3.34/0.98  fof(f77,plain,(
% 3.34/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.34/0.98    inference(cnf_transformation,[],[f53])).
% 3.34/0.98  
% 3.34/0.98  fof(f10,axiom,(
% 3.34/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f32,plain,(
% 3.34/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.34/0.98    inference(ennf_transformation,[],[f10])).
% 3.34/0.98  
% 3.34/0.98  fof(f72,plain,(
% 3.34/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.34/0.98    inference(cnf_transformation,[],[f32])).
% 3.34/0.98  
% 3.34/0.98  fof(f94,plain,(
% 3.34/0.98    v1_funct_2(sK1,sK0,sK0)),
% 3.34/0.98    inference(cnf_transformation,[],[f56])).
% 3.34/0.98  
% 3.34/0.98  fof(f18,axiom,(
% 3.34/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 3.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f45,plain,(
% 3.34/0.98    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.34/0.98    inference(ennf_transformation,[],[f18])).
% 3.34/0.98  
% 3.34/0.98  fof(f46,plain,(
% 3.34/0.98    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.34/0.98    inference(flattening,[],[f45])).
% 3.34/0.98  
% 3.34/0.98  fof(f91,plain,(
% 3.34/0.98    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.34/0.98    inference(cnf_transformation,[],[f46])).
% 3.34/0.98  
% 3.34/0.98  fof(f93,plain,(
% 3.34/0.98    v1_funct_1(sK1)),
% 3.34/0.98    inference(cnf_transformation,[],[f56])).
% 3.34/0.98  
% 3.34/0.98  fof(f95,plain,(
% 3.34/0.98    v3_funct_2(sK1,sK0,sK0)),
% 3.34/0.98    inference(cnf_transformation,[],[f56])).
% 3.34/0.98  
% 3.34/0.98  fof(f15,axiom,(
% 3.34/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 3.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f41,plain,(
% 3.34/0.98    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.34/0.98    inference(ennf_transformation,[],[f15])).
% 3.34/0.98  
% 3.34/0.98  fof(f42,plain,(
% 3.34/0.98    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.34/0.98    inference(flattening,[],[f41])).
% 3.34/0.98  
% 3.34/0.98  fof(f88,plain,(
% 3.34/0.98    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.34/0.98    inference(cnf_transformation,[],[f42])).
% 3.34/0.98  
% 3.34/0.98  fof(f17,axiom,(
% 3.34/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f43,plain,(
% 3.34/0.98    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.34/0.98    inference(ennf_transformation,[],[f17])).
% 3.34/0.98  
% 3.34/0.98  fof(f44,plain,(
% 3.34/0.98    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.34/0.98    inference(flattening,[],[f43])).
% 3.34/0.98  
% 3.34/0.98  fof(f90,plain,(
% 3.34/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.34/0.98    inference(cnf_transformation,[],[f44])).
% 3.34/0.98  
% 3.34/0.98  fof(f85,plain,(
% 3.34/0.98    ( ! [X0,X1] : (v1_funct_1(k2_funct_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.34/0.98    inference(cnf_transformation,[],[f42])).
% 3.34/0.98  
% 3.34/0.98  fof(f7,axiom,(
% 3.34/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 3.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f28,plain,(
% 3.34/0.98    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.34/0.98    inference(ennf_transformation,[],[f7])).
% 3.34/0.98  
% 3.34/0.98  fof(f29,plain,(
% 3.34/0.98    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.34/0.98    inference(flattening,[],[f28])).
% 3.34/0.98  
% 3.34/0.98  fof(f67,plain,(
% 3.34/0.98    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.34/0.98    inference(cnf_transformation,[],[f29])).
% 3.34/0.98  
% 3.34/0.98  fof(f19,axiom,(
% 3.34/0.98    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f92,plain,(
% 3.34/0.98    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.34/0.98    inference(cnf_transformation,[],[f19])).
% 3.34/0.98  
% 3.34/0.98  fof(f99,plain,(
% 3.34/0.98    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.34/0.98    inference(definition_unfolding,[],[f67,f92])).
% 3.34/0.98  
% 3.34/0.98  fof(f8,axiom,(
% 3.34/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f30,plain,(
% 3.34/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.34/0.98    inference(ennf_transformation,[],[f8])).
% 3.34/0.98  
% 3.34/0.98  fof(f69,plain,(
% 3.34/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.34/0.98    inference(cnf_transformation,[],[f30])).
% 3.34/0.98  
% 3.34/0.98  fof(f12,axiom,(
% 3.34/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 3.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f35,plain,(
% 3.34/0.98    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.34/0.98    inference(ennf_transformation,[],[f12])).
% 3.34/0.98  
% 3.34/0.98  fof(f36,plain,(
% 3.34/0.98    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.34/0.98    inference(flattening,[],[f35])).
% 3.34/0.98  
% 3.34/0.98  fof(f75,plain,(
% 3.34/0.98    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.34/0.98    inference(cnf_transformation,[],[f36])).
% 3.34/0.98  
% 3.34/0.98  fof(f68,plain,(
% 3.34/0.98    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.34/0.98    inference(cnf_transformation,[],[f29])).
% 3.34/0.98  
% 3.34/0.98  fof(f98,plain,(
% 3.34/0.98    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.34/0.98    inference(definition_unfolding,[],[f68,f92])).
% 3.34/0.98  
% 3.34/0.98  fof(f76,plain,(
% 3.34/0.98    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.34/0.98    inference(cnf_transformation,[],[f36])).
% 3.34/0.98  
% 3.34/0.98  fof(f14,axiom,(
% 3.34/0.98    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f39,plain,(
% 3.34/0.98    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.34/0.98    inference(ennf_transformation,[],[f14])).
% 3.34/0.98  
% 3.34/0.98  fof(f40,plain,(
% 3.34/0.98    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.34/0.98    inference(flattening,[],[f39])).
% 3.34/0.98  
% 3.34/0.98  fof(f54,plain,(
% 3.34/0.98    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.34/0.98    inference(nnf_transformation,[],[f40])).
% 3.34/0.98  
% 3.34/0.98  fof(f83,plain,(
% 3.34/0.98    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.34/0.98    inference(cnf_transformation,[],[f54])).
% 3.34/0.98  
% 3.34/0.98  fof(f9,axiom,(
% 3.34/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f31,plain,(
% 3.34/0.98    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.34/0.98    inference(ennf_transformation,[],[f9])).
% 3.34/0.98  
% 3.34/0.98  fof(f71,plain,(
% 3.34/0.98    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.34/0.98    inference(cnf_transformation,[],[f31])).
% 3.34/0.98  
% 3.34/0.98  fof(f97,plain,(
% 3.34/0.98    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))),
% 3.34/0.98    inference(cnf_transformation,[],[f56])).
% 3.34/0.98  
% 3.34/0.98  fof(f6,axiom,(
% 3.34/0.98    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 3.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f26,plain,(
% 3.34/0.98    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.34/0.98    inference(ennf_transformation,[],[f6])).
% 3.34/0.98  
% 3.34/0.98  fof(f27,plain,(
% 3.34/0.98    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.34/0.98    inference(flattening,[],[f26])).
% 3.34/0.98  
% 3.34/0.98  fof(f66,plain,(
% 3.34/0.98    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.34/0.98    inference(cnf_transformation,[],[f27])).
% 3.34/0.98  
% 3.34/0.98  fof(f5,axiom,(
% 3.34/0.98    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f25,plain,(
% 3.34/0.98    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.34/0.98    inference(ennf_transformation,[],[f5])).
% 3.34/0.98  
% 3.34/0.98  fof(f52,plain,(
% 3.34/0.98    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.34/0.98    inference(nnf_transformation,[],[f25])).
% 3.34/0.98  
% 3.34/0.98  fof(f63,plain,(
% 3.34/0.98    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.34/0.98    inference(cnf_transformation,[],[f52])).
% 3.34/0.98  
% 3.34/0.98  fof(f1,axiom,(
% 3.34/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f49,plain,(
% 3.34/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.34/0.98    inference(nnf_transformation,[],[f1])).
% 3.34/0.98  
% 3.34/0.98  fof(f50,plain,(
% 3.34/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.34/0.98    inference(flattening,[],[f49])).
% 3.34/0.98  
% 3.34/0.98  fof(f59,plain,(
% 3.34/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.34/0.98    inference(cnf_transformation,[],[f50])).
% 3.34/0.98  
% 3.34/0.98  fof(f87,plain,(
% 3.34/0.98    ( ! [X0,X1] : (v3_funct_2(k2_funct_2(X0,X1),X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.34/0.98    inference(cnf_transformation,[],[f42])).
% 3.34/0.98  
% 3.34/0.98  fof(f2,axiom,(
% 3.34/0.98    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f60,plain,(
% 3.34/0.98    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.34/0.98    inference(cnf_transformation,[],[f2])).
% 3.34/0.98  
% 3.34/0.98  cnf(c_32,plain,
% 3.34/0.98      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.34/0.98      inference(cnf_transformation,[],[f89]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1552,plain,
% 3.34/0.98      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_16,plain,
% 3.34/0.98      ( r2_relset_1(X0,X1,X2,X2)
% 3.34/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.34/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.34/0.98      inference(cnf_transformation,[],[f73]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1564,plain,
% 3.34/0.98      ( r2_relset_1(X0,X1,X2,X2) = iProver_top
% 3.34/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.34/0.98      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_3445,plain,
% 3.34/0.98      ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0)) = iProver_top
% 3.34/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_1552,c_1564]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_10260,plain,
% 3.34/0.98      ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0)) = iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_1552,c_3445]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_36,negated_conjecture,
% 3.34/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.34/0.98      inference(cnf_transformation,[],[f96]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1548,plain,
% 3.34/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_25,plain,
% 3.34/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.34/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/0.98      | k1_relset_1(X1,X2,X0) = X1
% 3.34/0.98      | k1_xboole_0 = X2 ),
% 3.34/0.98      inference(cnf_transformation,[],[f77]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1557,plain,
% 3.34/0.98      ( k1_relset_1(X0,X1,X2) = X0
% 3.34/0.98      | k1_xboole_0 = X1
% 3.34/0.98      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.34/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_3473,plain,
% 3.34/0.98      ( k1_relset_1(sK0,sK0,sK1) = sK0
% 3.34/0.98      | sK0 = k1_xboole_0
% 3.34/0.98      | v1_funct_2(sK1,sK0,sK0) != iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_1548,c_1557]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_15,plain,
% 3.34/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.34/0.98      inference(cnf_transformation,[],[f72]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1565,plain,
% 3.34/0.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.34/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2218,plain,
% 3.34/0.98      ( k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_1548,c_1565]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_3477,plain,
% 3.34/0.98      ( k1_relat_1(sK1) = sK0
% 3.34/0.98      | sK0 = k1_xboole_0
% 3.34/0.98      | v1_funct_2(sK1,sK0,sK0) != iProver_top ),
% 3.34/0.98      inference(demodulation,[status(thm)],[c_3473,c_2218]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_38,negated_conjecture,
% 3.34/0.98      ( v1_funct_2(sK1,sK0,sK0) ),
% 3.34/0.98      inference(cnf_transformation,[],[f94]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_41,plain,
% 3.34/0.98      ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_3801,plain,
% 3.34/0.98      ( sK0 = k1_xboole_0 | k1_relat_1(sK1) = sK0 ),
% 3.34/0.98      inference(global_propositional_subsumption,
% 3.34/0.98                [status(thm)],
% 3.34/0.98                [c_3477,c_41]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_3802,plain,
% 3.34/0.98      ( k1_relat_1(sK1) = sK0 | sK0 = k1_xboole_0 ),
% 3.34/0.98      inference(renaming,[status(thm)],[c_3801]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_34,plain,
% 3.34/0.98      ( ~ v1_funct_2(X0,X1,X1)
% 3.34/0.98      | ~ v3_funct_2(X0,X1,X1)
% 3.34/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.34/0.98      | ~ v1_funct_1(X0)
% 3.34/0.98      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 3.34/0.98      inference(cnf_transformation,[],[f91]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1550,plain,
% 3.34/0.98      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
% 3.34/0.98      | v1_funct_2(X1,X0,X0) != iProver_top
% 3.34/0.98      | v3_funct_2(X1,X0,X0) != iProver_top
% 3.34/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 3.34/0.98      | v1_funct_1(X1) != iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_4493,plain,
% 3.34/0.98      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
% 3.34/0.98      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.34/0.98      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.34/0.98      | v1_funct_1(sK1) != iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_1548,c_1550]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_39,negated_conjecture,
% 3.34/0.98      ( v1_funct_1(sK1) ),
% 3.34/0.98      inference(cnf_transformation,[],[f93]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_37,negated_conjecture,
% 3.34/0.98      ( v3_funct_2(sK1,sK0,sK0) ),
% 3.34/0.98      inference(cnf_transformation,[],[f95]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1966,plain,
% 3.34/0.98      ( ~ v1_funct_2(sK1,X0,X0)
% 3.34/0.98      | ~ v3_funct_2(sK1,X0,X0)
% 3.34/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 3.34/0.98      | ~ v1_funct_1(sK1)
% 3.34/0.98      | k2_funct_2(X0,sK1) = k2_funct_1(sK1) ),
% 3.34/0.98      inference(instantiation,[status(thm)],[c_34]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2207,plain,
% 3.34/0.98      ( ~ v1_funct_2(sK1,sK0,sK0)
% 3.34/0.98      | ~ v3_funct_2(sK1,sK0,sK0)
% 3.34/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.34/0.98      | ~ v1_funct_1(sK1)
% 3.34/0.98      | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 3.34/0.98      inference(instantiation,[status(thm)],[c_1966]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_4958,plain,
% 3.34/0.98      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 3.34/0.98      inference(global_propositional_subsumption,
% 3.34/0.98                [status(thm)],
% 3.34/0.98                [c_4493,c_39,c_38,c_37,c_36,c_2207]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_28,plain,
% 3.34/0.98      ( ~ v1_funct_2(X0,X1,X1)
% 3.34/0.98      | ~ v3_funct_2(X0,X1,X1)
% 3.34/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.34/0.98      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.34/0.98      | ~ v1_funct_1(X0) ),
% 3.34/0.98      inference(cnf_transformation,[],[f88]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1556,plain,
% 3.34/0.98      ( v1_funct_2(X0,X1,X1) != iProver_top
% 3.34/0.98      | v3_funct_2(X0,X1,X1) != iProver_top
% 3.34/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 3.34/0.98      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) = iProver_top
% 3.34/0.98      | v1_funct_1(X0) != iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_5405,plain,
% 3.34/0.98      ( v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.34/0.98      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.34/0.98      | m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 3.34/0.98      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.34/0.98      | v1_funct_1(sK1) != iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_4958,c_1556]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_40,plain,
% 3.34/0.98      ( v1_funct_1(sK1) = iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_42,plain,
% 3.34/0.98      ( v3_funct_2(sK1,sK0,sK0) = iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_43,plain,
% 3.34/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_6383,plain,
% 3.34/0.98      ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.34/0.98      inference(global_propositional_subsumption,
% 3.34/0.98                [status(thm)],
% 3.34/0.98                [c_5405,c_40,c_41,c_42,c_43]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_33,plain,
% 3.34/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.34/0.98      | ~ v1_funct_1(X0)
% 3.34/0.98      | ~ v1_funct_1(X3)
% 3.34/0.98      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.34/0.98      inference(cnf_transformation,[],[f90]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1551,plain,
% 3.34/0.98      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 3.34/0.98      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.34/0.98      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.34/0.98      | v1_funct_1(X5) != iProver_top
% 3.34/0.98      | v1_funct_1(X4) != iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_6401,plain,
% 3.34/0.98      ( k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1))
% 3.34/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.34/0.98      | v1_funct_1(X2) != iProver_top
% 3.34/0.98      | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_6383,c_1551]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_31,plain,
% 3.34/0.98      ( ~ v1_funct_2(X0,X1,X1)
% 3.34/0.98      | ~ v3_funct_2(X0,X1,X1)
% 3.34/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.34/0.98      | ~ v1_funct_1(X0)
% 3.34/0.98      | v1_funct_1(k2_funct_2(X1,X0)) ),
% 3.34/0.98      inference(cnf_transformation,[],[f85]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1553,plain,
% 3.34/0.98      ( v1_funct_2(X0,X1,X1) != iProver_top
% 3.34/0.98      | v3_funct_2(X0,X1,X1) != iProver_top
% 3.34/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 3.34/0.98      | v1_funct_1(X0) != iProver_top
% 3.34/0.98      | v1_funct_1(k2_funct_2(X1,X0)) = iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_4263,plain,
% 3.34/0.98      ( v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.34/0.98      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.34/0.98      | v1_funct_1(k2_funct_2(sK0,sK1)) = iProver_top
% 3.34/0.98      | v1_funct_1(sK1) != iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_1548,c_1553]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1951,plain,
% 3.34/0.98      ( ~ v1_funct_2(sK1,X0,X0)
% 3.34/0.98      | ~ v3_funct_2(sK1,X0,X0)
% 3.34/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 3.34/0.98      | v1_funct_1(k2_funct_2(X0,sK1))
% 3.34/0.98      | ~ v1_funct_1(sK1) ),
% 3.34/0.98      inference(instantiation,[status(thm)],[c_31]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2136,plain,
% 3.34/0.98      ( ~ v1_funct_2(sK1,sK0,sK0)
% 3.34/0.98      | ~ v3_funct_2(sK1,sK0,sK0)
% 3.34/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.34/0.98      | v1_funct_1(k2_funct_2(sK0,sK1))
% 3.34/0.98      | ~ v1_funct_1(sK1) ),
% 3.34/0.98      inference(instantiation,[status(thm)],[c_1951]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2137,plain,
% 3.34/0.98      ( v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.34/0.98      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.34/0.98      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.34/0.98      | v1_funct_1(k2_funct_2(sK0,sK1)) = iProver_top
% 3.34/0.98      | v1_funct_1(sK1) != iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_2136]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_4936,plain,
% 3.34/0.98      ( v1_funct_1(k2_funct_2(sK0,sK1)) = iProver_top ),
% 3.34/0.98      inference(global_propositional_subsumption,
% 3.34/0.98                [status(thm)],
% 3.34/0.98                [c_4263,c_40,c_41,c_42,c_43,c_2137]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_4961,plain,
% 3.34/0.98      ( v1_funct_1(k2_funct_1(sK1)) = iProver_top ),
% 3.34/0.98      inference(demodulation,[status(thm)],[c_4958,c_4936]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_8956,plain,
% 3.34/0.98      ( v1_funct_1(X2) != iProver_top
% 3.34/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.34/0.98      | k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1)) ),
% 3.34/0.98      inference(global_propositional_subsumption,
% 3.34/0.98                [status(thm)],
% 3.34/0.98                [c_6401,c_4961]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_8957,plain,
% 3.34/0.98      ( k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1))
% 3.34/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.34/0.98      | v1_funct_1(X2) != iProver_top ),
% 3.34/0.98      inference(renaming,[status(thm)],[c_8956]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_8968,plain,
% 3.34/0.98      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k5_relat_1(sK1,k2_funct_1(sK1))
% 3.34/0.98      | v1_funct_1(sK1) != iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_1548,c_8957]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1545,plain,
% 3.34/0.98      ( v1_funct_1(sK1) = iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_11,plain,
% 3.34/0.98      ( ~ v1_funct_1(X0)
% 3.34/0.98      | ~ v2_funct_1(X0)
% 3.34/0.98      | ~ v1_relat_1(X0)
% 3.34/0.98      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
% 3.34/0.98      inference(cnf_transformation,[],[f99]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1567,plain,
% 3.34/0.98      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
% 3.34/0.98      | v1_funct_1(X0) != iProver_top
% 3.34/0.98      | v2_funct_1(X0) != iProver_top
% 3.34/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_3350,plain,
% 3.34/0.98      ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
% 3.34/0.98      | v2_funct_1(sK1) != iProver_top
% 3.34/0.98      | v1_relat_1(sK1) != iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_1545,c_1567]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_12,plain,
% 3.34/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/0.98      | v1_relat_1(X0) ),
% 3.34/0.98      inference(cnf_transformation,[],[f69]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1849,plain,
% 3.34/0.98      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.34/0.98      | v1_relat_1(sK1) ),
% 3.34/0.98      inference(instantiation,[status(thm)],[c_12]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1884,plain,
% 3.34/0.98      ( ~ v1_funct_1(sK1)
% 3.34/0.98      | ~ v2_funct_1(sK1)
% 3.34/0.98      | ~ v1_relat_1(sK1)
% 3.34/0.98      | k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
% 3.34/0.98      inference(instantiation,[status(thm)],[c_11]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_18,plain,
% 3.34/0.98      ( ~ v3_funct_2(X0,X1,X2)
% 3.34/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/0.98      | ~ v1_funct_1(X0)
% 3.34/0.98      | v2_funct_1(X0) ),
% 3.34/0.98      inference(cnf_transformation,[],[f75]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1909,plain,
% 3.34/0.98      ( ~ v3_funct_2(sK1,X0,X1)
% 3.34/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.34/0.98      | ~ v1_funct_1(sK1)
% 3.34/0.98      | v2_funct_1(sK1) ),
% 3.34/0.98      inference(instantiation,[status(thm)],[c_18]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2066,plain,
% 3.34/0.98      ( ~ v3_funct_2(sK1,sK0,sK0)
% 3.34/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.34/0.98      | ~ v1_funct_1(sK1)
% 3.34/0.98      | v2_funct_1(sK1) ),
% 3.34/0.98      inference(instantiation,[status(thm)],[c_1909]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_3702,plain,
% 3.34/0.98      ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
% 3.34/0.98      inference(global_propositional_subsumption,
% 3.34/0.98                [status(thm)],
% 3.34/0.98                [c_3350,c_39,c_37,c_36,c_1849,c_1884,c_2066]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_8976,plain,
% 3.34/0.98      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
% 3.34/0.98      | v1_funct_1(sK1) != iProver_top ),
% 3.34/0.98      inference(light_normalisation,[status(thm)],[c_8968,c_3702]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_9466,plain,
% 3.34/0.98      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
% 3.34/0.98      inference(global_propositional_subsumption,
% 3.34/0.98                [status(thm)],
% 3.34/0.98                [c_8976,c_40]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_5647,plain,
% 3.34/0.98      ( k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1)
% 3.34/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.34/0.98      | v1_funct_1(X2) != iProver_top
% 3.34/0.98      | v1_funct_1(sK1) != iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_1548,c_1551]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_6126,plain,
% 3.34/0.98      ( v1_funct_1(X2) != iProver_top
% 3.34/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.34/0.98      | k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1) ),
% 3.34/0.98      inference(global_propositional_subsumption,
% 3.34/0.98                [status(thm)],
% 3.34/0.98                [c_5647,c_40]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_6127,plain,
% 3.34/0.98      ( k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1)
% 3.34/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.34/0.98      | v1_funct_1(X2) != iProver_top ),
% 3.34/0.98      inference(renaming,[status(thm)],[c_6126]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_6136,plain,
% 3.34/0.98      ( k1_partfun1(X0,X0,sK0,sK0,k2_funct_2(X0,X1),sK1) = k5_relat_1(k2_funct_2(X0,X1),sK1)
% 3.34/0.98      | v1_funct_2(X1,X0,X0) != iProver_top
% 3.34/0.98      | v3_funct_2(X1,X0,X0) != iProver_top
% 3.34/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 3.34/0.98      | v1_funct_1(X1) != iProver_top
% 3.34/0.98      | v1_funct_1(k2_funct_2(X0,X1)) != iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_1556,c_6127]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_6539,plain,
% 3.34/0.98      ( k1_partfun1(X0,X0,sK0,sK0,k2_funct_2(X0,X1),sK1) = k5_relat_1(k2_funct_2(X0,X1),sK1)
% 3.34/0.98      | v1_funct_2(X1,X0,X0) != iProver_top
% 3.34/0.98      | v3_funct_2(X1,X0,X0) != iProver_top
% 3.34/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 3.34/0.98      | v1_funct_1(X1) != iProver_top ),
% 3.34/0.98      inference(forward_subsumption_resolution,
% 3.34/0.98                [status(thm)],
% 3.34/0.98                [c_6136,c_1553]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_6546,plain,
% 3.34/0.98      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1) = k5_relat_1(k2_funct_2(sK0,sK1),sK1)
% 3.34/0.98      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.34/0.98      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.34/0.98      | v1_funct_1(sK1) != iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_1548,c_6539]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_10,plain,
% 3.34/0.98      ( ~ v1_funct_1(X0)
% 3.34/0.98      | ~ v2_funct_1(X0)
% 3.34/0.98      | ~ v1_relat_1(X0)
% 3.34/0.98      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
% 3.34/0.98      inference(cnf_transformation,[],[f98]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1568,plain,
% 3.34/0.98      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
% 3.34/0.98      | v1_funct_1(X0) != iProver_top
% 3.34/0.98      | v2_funct_1(X0) != iProver_top
% 3.34/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_3357,plain,
% 3.34/0.98      ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1))
% 3.34/0.98      | v2_funct_1(sK1) != iProver_top
% 3.34/0.98      | v1_relat_1(sK1) != iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_1545,c_1568]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_17,plain,
% 3.34/0.98      ( ~ v3_funct_2(X0,X1,X2)
% 3.34/0.98      | v2_funct_2(X0,X2)
% 3.34/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/0.98      | ~ v1_funct_1(X0) ),
% 3.34/0.98      inference(cnf_transformation,[],[f76]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_27,plain,
% 3.34/0.98      ( ~ v2_funct_2(X0,X1)
% 3.34/0.98      | ~ v5_relat_1(X0,X1)
% 3.34/0.98      | ~ v1_relat_1(X0)
% 3.34/0.98      | k2_relat_1(X0) = X1 ),
% 3.34/0.98      inference(cnf_transformation,[],[f83]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_461,plain,
% 3.34/0.98      ( ~ v3_funct_2(X0,X1,X2)
% 3.34/0.98      | ~ v5_relat_1(X3,X4)
% 3.34/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/0.98      | ~ v1_funct_1(X0)
% 3.34/0.98      | ~ v1_relat_1(X3)
% 3.34/0.98      | X3 != X0
% 3.34/0.98      | X4 != X2
% 3.34/0.98      | k2_relat_1(X3) = X4 ),
% 3.34/0.98      inference(resolution_lifted,[status(thm)],[c_17,c_27]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_462,plain,
% 3.34/0.98      ( ~ v3_funct_2(X0,X1,X2)
% 3.34/0.98      | ~ v5_relat_1(X0,X2)
% 3.34/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/0.98      | ~ v1_funct_1(X0)
% 3.34/0.98      | ~ v1_relat_1(X0)
% 3.34/0.98      | k2_relat_1(X0) = X2 ),
% 3.34/0.98      inference(unflattening,[status(thm)],[c_461]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_466,plain,
% 3.34/0.98      ( ~ v1_funct_1(X0)
% 3.34/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/0.98      | ~ v5_relat_1(X0,X2)
% 3.34/0.98      | ~ v3_funct_2(X0,X1,X2)
% 3.34/0.98      | k2_relat_1(X0) = X2 ),
% 3.34/0.98      inference(global_propositional_subsumption,
% 3.34/0.98                [status(thm)],
% 3.34/0.98                [c_462,c_12]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_467,plain,
% 3.34/0.98      ( ~ v3_funct_2(X0,X1,X2)
% 3.34/0.98      | ~ v5_relat_1(X0,X2)
% 3.34/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/0.98      | ~ v1_funct_1(X0)
% 3.34/0.98      | k2_relat_1(X0) = X2 ),
% 3.34/0.98      inference(renaming,[status(thm)],[c_466]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_13,plain,
% 3.34/0.98      ( v5_relat_1(X0,X1)
% 3.34/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.34/0.98      inference(cnf_transformation,[],[f71]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_482,plain,
% 3.34/0.98      ( ~ v3_funct_2(X0,X1,X2)
% 3.34/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/0.98      | ~ v1_funct_1(X0)
% 3.34/0.98      | k2_relat_1(X0) = X2 ),
% 3.34/0.98      inference(forward_subsumption_resolution,
% 3.34/0.98                [status(thm)],
% 3.34/0.98                [c_467,c_13]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1543,plain,
% 3.34/0.98      ( k2_relat_1(X0) = X1
% 3.34/0.98      | v3_funct_2(X0,X2,X1) != iProver_top
% 3.34/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 3.34/0.98      | v1_funct_1(X0) != iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_482]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2550,plain,
% 3.34/0.98      ( k2_relat_1(sK1) = sK0
% 3.34/0.98      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.34/0.98      | v1_funct_1(sK1) != iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_1548,c_1543]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1929,plain,
% 3.34/0.98      ( ~ v3_funct_2(sK1,X0,X1)
% 3.34/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.34/0.98      | ~ v1_funct_1(sK1)
% 3.34/0.98      | k2_relat_1(sK1) = X1 ),
% 3.34/0.98      inference(instantiation,[status(thm)],[c_482]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2103,plain,
% 3.34/0.98      ( ~ v3_funct_2(sK1,sK0,sK0)
% 3.34/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.34/0.98      | ~ v1_funct_1(sK1)
% 3.34/0.98      | k2_relat_1(sK1) = sK0 ),
% 3.34/0.98      inference(instantiation,[status(thm)],[c_1929]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2912,plain,
% 3.34/0.98      ( k2_relat_1(sK1) = sK0 ),
% 3.34/0.98      inference(global_propositional_subsumption,
% 3.34/0.98                [status(thm)],
% 3.34/0.98                [c_2550,c_39,c_37,c_36,c_2103]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_3358,plain,
% 3.34/0.98      ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
% 3.34/0.98      | v2_funct_1(sK1) != iProver_top
% 3.34/0.98      | v1_relat_1(sK1) != iProver_top ),
% 3.34/0.98      inference(light_normalisation,[status(thm)],[c_3357,c_2912]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1850,plain,
% 3.34/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.34/0.98      | v1_relat_1(sK1) = iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_1849]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2067,plain,
% 3.34/0.98      ( v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.34/0.98      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.34/0.98      | v1_funct_1(sK1) != iProver_top
% 3.34/0.98      | v2_funct_1(sK1) = iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_2066]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_3797,plain,
% 3.34/0.98      ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(sK0) ),
% 3.34/0.98      inference(global_propositional_subsumption,
% 3.34/0.98                [status(thm)],
% 3.34/0.98                [c_3358,c_40,c_42,c_43,c_1850,c_2067]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_6560,plain,
% 3.34/0.98      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
% 3.34/0.98      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.34/0.98      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.34/0.98      | v1_funct_1(sK1) != iProver_top ),
% 3.34/0.98      inference(light_normalisation,[status(thm)],[c_6546,c_3797,c_4958]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_6388,plain,
% 3.34/0.98      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k5_relat_1(k2_funct_1(sK1),sK1)
% 3.34/0.98      | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_6383,c_6127]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_6475,plain,
% 3.34/0.98      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
% 3.34/0.98      | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
% 3.34/0.98      inference(light_normalisation,[status(thm)],[c_6388,c_3797]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_6609,plain,
% 3.34/0.98      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0) ),
% 3.34/0.98      inference(global_propositional_subsumption,
% 3.34/0.98                [status(thm)],
% 3.34/0.98                [c_6560,c_4961,c_6475]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_35,negated_conjecture,
% 3.34/0.98      ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
% 3.34/0.98      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
% 3.34/0.98      inference(cnf_transformation,[],[f97]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1549,plain,
% 3.34/0.98      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) != iProver_top
% 3.34/0.98      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) != iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_4962,plain,
% 3.34/0.98      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) != iProver_top
% 3.34/0.98      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
% 3.34/0.98      inference(demodulation,[status(thm)],[c_4958,c_1549]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_6612,plain,
% 3.34/0.98      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top
% 3.34/0.98      | r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
% 3.34/0.98      inference(demodulation,[status(thm)],[c_6609,c_4962]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_9469,plain,
% 3.34/0.98      ( r2_relset_1(sK0,sK0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(sK0)) != iProver_top
% 3.34/0.98      | r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
% 3.34/0.98      inference(demodulation,[status(thm)],[c_9466,c_6612]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_9582,plain,
% 3.34/0.98      ( sK0 = k1_xboole_0
% 3.34/0.98      | r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_3802,c_9469]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_10272,plain,
% 3.34/0.98      ( sK0 = k1_xboole_0 ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_10260,c_9582]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_10612,plain,
% 3.34/0.98      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(k1_xboole_0)) != iProver_top
% 3.34/0.98      | r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),k6_partfun1(k1_xboole_0)) != iProver_top ),
% 3.34/0.98      inference(demodulation,[status(thm)],[c_10272,c_9469]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_8,plain,
% 3.34/0.98      ( ~ v1_relat_1(X0)
% 3.34/0.98      | k2_relat_1(X0) != k1_xboole_0
% 3.34/0.98      | k1_xboole_0 = X0 ),
% 3.34/0.98      inference(cnf_transformation,[],[f66]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1570,plain,
% 3.34/0.98      ( k2_relat_1(X0) != k1_xboole_0
% 3.34/0.98      | k1_xboole_0 = X0
% 3.34/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2916,plain,
% 3.34/0.98      ( sK1 = k1_xboole_0
% 3.34/0.98      | sK0 != k1_xboole_0
% 3.34/0.98      | v1_relat_1(sK1) != iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_2912,c_1570]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2917,plain,
% 3.34/0.98      ( ~ v1_relat_1(sK1) | sK1 = k1_xboole_0 | sK0 != k1_xboole_0 ),
% 3.34/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_2916]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2919,plain,
% 3.34/0.98      ( sK0 != k1_xboole_0 | sK1 = k1_xboole_0 ),
% 3.34/0.98      inference(global_propositional_subsumption,
% 3.34/0.98                [status(thm)],
% 3.34/0.98                [c_2916,c_36,c_1849,c_2917]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2920,plain,
% 3.34/0.98      ( sK1 = k1_xboole_0 | sK0 != k1_xboole_0 ),
% 3.34/0.98      inference(renaming,[status(thm)],[c_2919]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_10640,plain,
% 3.34/0.98      ( sK1 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.34/0.98      inference(demodulation,[status(thm)],[c_10272,c_2920]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_10656,plain,
% 3.34/0.98      ( sK1 = k1_xboole_0 ),
% 3.34/0.98      inference(equality_resolution_simp,[status(thm)],[c_10640]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_10614,plain,
% 3.34/0.98      ( k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
% 3.34/0.98      inference(demodulation,[status(thm)],[c_10272,c_9466]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_7,plain,
% 3.34/0.98      ( ~ v5_relat_1(X0,X1)
% 3.34/0.98      | r1_tarski(k2_relat_1(X0),X1)
% 3.34/0.98      | ~ v1_relat_1(X0) ),
% 3.34/0.98      inference(cnf_transformation,[],[f63]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_497,plain,
% 3.34/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/0.98      | r1_tarski(k2_relat_1(X0),X2)
% 3.34/0.98      | ~ v1_relat_1(X0) ),
% 3.34/0.98      inference(resolution,[status(thm)],[c_13,c_7]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_501,plain,
% 3.34/0.98      ( r1_tarski(k2_relat_1(X0),X2)
% 3.34/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.34/0.98      inference(global_propositional_subsumption,
% 3.34/0.98                [status(thm)],
% 3.34/0.98                [c_497,c_12]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_502,plain,
% 3.34/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/0.98      | r1_tarski(k2_relat_1(X0),X2) ),
% 3.34/0.98      inference(renaming,[status(thm)],[c_501]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1542,plain,
% 3.34/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.34/0.98      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_502]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_6395,plain,
% 3.34/0.98      ( r1_tarski(k2_relat_1(k2_funct_1(sK1)),sK0) = iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_6383,c_1542]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_0,plain,
% 3.34/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.34/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1573,plain,
% 3.34/0.98      ( X0 = X1
% 3.34/0.98      | r1_tarski(X0,X1) != iProver_top
% 3.34/0.98      | r1_tarski(X1,X0) != iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_7317,plain,
% 3.34/0.98      ( k2_relat_1(k2_funct_1(sK1)) = sK0
% 3.34/0.98      | r1_tarski(sK0,k2_relat_1(k2_funct_1(sK1))) != iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_6395,c_1573]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_29,plain,
% 3.34/0.98      ( ~ v1_funct_2(X0,X1,X1)
% 3.34/0.98      | ~ v3_funct_2(X0,X1,X1)
% 3.34/0.98      | v3_funct_2(k2_funct_2(X1,X0),X1,X1)
% 3.34/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.34/0.98      | ~ v1_funct_1(X0) ),
% 3.34/0.98      inference(cnf_transformation,[],[f87]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1555,plain,
% 3.34/0.98      ( v1_funct_2(X0,X1,X1) != iProver_top
% 3.34/0.98      | v3_funct_2(X0,X1,X1) != iProver_top
% 3.34/0.98      | v3_funct_2(k2_funct_2(X1,X0),X1,X1) = iProver_top
% 3.34/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 3.34/0.98      | v1_funct_1(X0) != iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_5211,plain,
% 3.34/0.98      ( v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.34/0.98      | v3_funct_2(k2_funct_2(sK0,sK1),sK0,sK0) = iProver_top
% 3.34/0.98      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.34/0.98      | v1_funct_1(sK1) != iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_1548,c_1555]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_5216,plain,
% 3.34/0.98      ( v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.34/0.98      | v3_funct_2(k2_funct_1(sK1),sK0,sK0) = iProver_top
% 3.34/0.98      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.34/0.98      | v1_funct_1(sK1) != iProver_top ),
% 3.34/0.98      inference(light_normalisation,[status(thm)],[c_5211,c_4958]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_6396,plain,
% 3.34/0.98      ( k2_relat_1(k2_funct_1(sK1)) = sK0
% 3.34/0.98      | v3_funct_2(k2_funct_1(sK1),sK0,sK0) != iProver_top
% 3.34/0.98      | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_6383,c_1543]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_8434,plain,
% 3.34/0.98      ( k2_relat_1(k2_funct_1(sK1)) = sK0 ),
% 3.34/0.98      inference(global_propositional_subsumption,
% 3.34/0.98                [status(thm)],
% 3.34/0.98                [c_7317,c_40,c_41,c_42,c_4961,c_5216,c_6396]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_8441,plain,
% 3.34/0.98      ( k2_funct_1(sK1) = k1_xboole_0
% 3.34/0.98      | sK0 != k1_xboole_0
% 3.34/0.98      | v1_relat_1(k2_funct_1(sK1)) != iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_8434,c_1570]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1566,plain,
% 3.34/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.34/0.98      | v1_relat_1(X0) = iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_6394,plain,
% 3.34/0.98      ( v1_relat_1(k2_funct_1(sK1)) = iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_6383,c_1566]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_8605,plain,
% 3.34/0.98      ( sK0 != k1_xboole_0 | k2_funct_1(sK1) = k1_xboole_0 ),
% 3.34/0.98      inference(global_propositional_subsumption,
% 3.34/0.98                [status(thm)],
% 3.34/0.98                [c_8441,c_6394]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_8606,plain,
% 3.34/0.98      ( k2_funct_1(sK1) = k1_xboole_0 | sK0 != k1_xboole_0 ),
% 3.34/0.98      inference(renaming,[status(thm)],[c_8605]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_10619,plain,
% 3.34/0.98      ( k2_funct_1(sK1) = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.34/0.98      inference(demodulation,[status(thm)],[c_10272,c_8606]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_10745,plain,
% 3.34/0.98      ( k2_funct_1(sK1) = k1_xboole_0 ),
% 3.34/0.98      inference(equality_resolution_simp,[status(thm)],[c_10619]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_10746,plain,
% 3.34/0.98      ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
% 3.34/0.98      inference(light_normalisation,[status(thm)],[c_10745,c_10656]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_10636,plain,
% 3.34/0.98      ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k1_xboole_0) ),
% 3.34/0.98      inference(demodulation,[status(thm)],[c_10272,c_3797]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_10679,plain,
% 3.34/0.98      ( k5_relat_1(k2_funct_1(k1_xboole_0),k1_xboole_0) = k6_partfun1(k1_xboole_0) ),
% 3.34/0.98      inference(light_normalisation,[status(thm)],[c_10636,c_10656]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_10758,plain,
% 3.34/0.98      ( k5_relat_1(k1_xboole_0,k1_xboole_0) = k6_partfun1(k1_xboole_0) ),
% 3.34/0.98      inference(demodulation,[status(thm)],[c_10746,c_10679]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_6138,plain,
% 3.34/0.98      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK1) = k5_relat_1(sK1,sK1)
% 3.34/0.98      | v1_funct_1(sK1) != iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_1548,c_6127]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1986,plain,
% 3.34/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 3.34/0.98      | ~ v1_funct_1(X0)
% 3.34/0.98      | ~ v1_funct_1(sK1)
% 3.34/0.98      | k1_partfun1(X1,X2,X3,X4,X0,sK1) = k5_relat_1(X0,sK1) ),
% 3.34/0.98      inference(instantiation,[status(thm)],[c_33]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2235,plain,
% 3.34/0.98      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.34/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.34/0.98      | ~ v1_funct_1(sK1)
% 3.34/0.98      | k1_partfun1(X0,X1,X2,X3,sK1,sK1) = k5_relat_1(sK1,sK1) ),
% 3.34/0.98      inference(instantiation,[status(thm)],[c_1986]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2581,plain,
% 3.34/0.98      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.34/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.34/0.98      | ~ v1_funct_1(sK1)
% 3.34/0.98      | k1_partfun1(sK0,sK0,X0,X1,sK1,sK1) = k5_relat_1(sK1,sK1) ),
% 3.34/0.98      inference(instantiation,[status(thm)],[c_2235]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2674,plain,
% 3.34/0.98      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.34/0.98      | ~ v1_funct_1(sK1)
% 3.34/0.98      | k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK1) = k5_relat_1(sK1,sK1) ),
% 3.34/0.98      inference(instantiation,[status(thm)],[c_2581]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_6174,plain,
% 3.34/0.98      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK1) = k5_relat_1(sK1,sK1) ),
% 3.34/0.98      inference(global_propositional_subsumption,
% 3.34/0.98                [status(thm)],
% 3.34/0.98                [c_6138,c_39,c_36,c_2674]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_10631,plain,
% 3.34/0.98      ( k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK1,sK1) = k5_relat_1(sK1,sK1) ),
% 3.34/0.98      inference(demodulation,[status(thm)],[c_10272,c_6174]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_10695,plain,
% 3.34/0.98      ( k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k5_relat_1(k1_xboole_0,k1_xboole_0) ),
% 3.34/0.98      inference(light_normalisation,[status(thm)],[c_10631,c_10656]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_10762,plain,
% 3.34/0.98      ( k1_partfun1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = k6_partfun1(k1_xboole_0) ),
% 3.34/0.98      inference(demodulation,[status(thm)],[c_10758,c_10695]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_10776,plain,
% 3.34/0.98      ( k6_partfun1(k1_relat_1(k1_xboole_0)) = k6_partfun1(k1_xboole_0) ),
% 3.34/0.98      inference(light_normalisation,
% 3.34/0.98                [status(thm)],
% 3.34/0.98                [c_10614,c_10656,c_10746,c_10762]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_10780,plain,
% 3.34/0.98      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),k6_partfun1(k1_xboole_0)) != iProver_top ),
% 3.34/0.98      inference(light_normalisation,
% 3.34/0.98                [status(thm)],
% 3.34/0.98                [c_10612,c_10656,c_10776]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1936,plain,
% 3.34/0.98      ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0))
% 3.34/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 3.34/0.98      | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.34/0.98      inference(instantiation,[status(thm)],[c_16]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1937,plain,
% 3.34/0.98      ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0)) = iProver_top
% 3.34/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 3.34/0.98      | m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_1936]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1939,plain,
% 3.34/0.98      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),k6_partfun1(k1_xboole_0)) = iProver_top
% 3.34/0.98      | m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 3.34/0.98      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 3.34/0.98      inference(instantiation,[status(thm)],[c_1937]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_3,plain,
% 3.34/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.34/0.98      inference(cnf_transformation,[],[f60]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1837,plain,
% 3.34/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.34/0.98      inference(instantiation,[status(thm)],[c_3]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1840,plain,
% 3.34/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_1837]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1842,plain,
% 3.34/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.34/0.98      inference(instantiation,[status(thm)],[c_1840]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_51,plain,
% 3.34/0.98      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_53,plain,
% 3.34/0.98      ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.34/0.98      inference(instantiation,[status(thm)],[c_51]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(contradiction,plain,
% 3.34/0.98      ( $false ),
% 3.34/0.98      inference(minisat,[status(thm)],[c_10780,c_1939,c_1842,c_53]) ).
% 3.34/0.98  
% 3.34/0.98  
% 3.34/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.34/0.98  
% 3.34/0.98  ------                               Statistics
% 3.34/0.98  
% 3.34/0.98  ------ General
% 3.34/0.98  
% 3.34/0.98  abstr_ref_over_cycles:                  0
% 3.34/0.98  abstr_ref_under_cycles:                 0
% 3.34/0.98  gc_basic_clause_elim:                   0
% 3.34/0.98  forced_gc_time:                         0
% 3.34/0.98  parsing_time:                           0.019
% 3.34/0.98  unif_index_cands_time:                  0.
% 3.34/0.98  unif_index_add_time:                    0.
% 3.34/0.98  orderings_time:                         0.
% 3.34/0.98  out_proof_time:                         0.013
% 3.34/0.98  total_time:                             0.304
% 3.34/0.98  num_of_symbols:                         55
% 3.34/0.98  num_of_terms:                           9523
% 3.34/0.98  
% 3.34/0.98  ------ Preprocessing
% 3.34/0.98  
% 3.34/0.98  num_of_splits:                          0
% 3.34/0.98  num_of_split_atoms:                     0
% 3.34/0.98  num_of_reused_defs:                     0
% 3.34/0.98  num_eq_ax_congr_red:                    28
% 3.34/0.98  num_of_sem_filtered_clauses:            1
% 3.34/0.98  num_of_subtypes:                        0
% 3.34/0.98  monotx_restored_types:                  0
% 3.34/0.98  sat_num_of_epr_types:                   0
% 3.34/0.98  sat_num_of_non_cyclic_types:            0
% 3.34/0.98  sat_guarded_non_collapsed_types:        0
% 3.34/0.98  num_pure_diseq_elim:                    0
% 3.34/0.98  simp_replaced_by:                       0
% 3.34/0.98  res_preprocessed:                       165
% 3.34/0.98  prep_upred:                             0
% 3.34/0.98  prep_unflattend:                        4
% 3.34/0.98  smt_new_axioms:                         0
% 3.34/0.98  pred_elim_cands:                        8
% 3.34/0.98  pred_elim:                              3
% 3.34/0.98  pred_elim_cl:                           6
% 3.34/0.98  pred_elim_cycles:                       7
% 3.34/0.98  merged_defs:                            0
% 3.34/0.98  merged_defs_ncl:                        0
% 3.34/0.98  bin_hyper_res:                          0
% 3.34/0.98  prep_cycles:                            4
% 3.34/0.98  pred_elim_time:                         0.007
% 3.34/0.98  splitting_time:                         0.
% 3.34/0.98  sem_filter_time:                        0.
% 3.34/0.98  monotx_time:                            0.001
% 3.34/0.98  subtype_inf_time:                       0.
% 3.34/0.98  
% 3.34/0.98  ------ Problem properties
% 3.34/0.98  
% 3.34/0.98  clauses:                                32
% 3.34/0.98  conjectures:                            5
% 3.34/0.98  epr:                                    5
% 3.34/0.98  horn:                                   28
% 3.34/0.98  ground:                                 5
% 3.34/0.98  unary:                                  7
% 3.34/0.98  binary:                                 5
% 3.34/0.98  lits:                                   96
% 3.34/0.98  lits_eq:                                20
% 3.34/0.98  fd_pure:                                0
% 3.34/0.98  fd_pseudo:                              0
% 3.34/0.98  fd_cond:                                5
% 3.34/0.98  fd_pseudo_cond:                         2
% 3.34/0.98  ac_symbols:                             0
% 3.34/0.98  
% 3.34/0.98  ------ Propositional Solver
% 3.34/0.98  
% 3.34/0.98  prop_solver_calls:                      28
% 3.34/0.98  prop_fast_solver_calls:                 1443
% 3.34/0.98  smt_solver_calls:                       0
% 3.34/0.98  smt_fast_solver_calls:                  0
% 3.34/0.98  prop_num_of_clauses:                    3781
% 3.34/0.98  prop_preprocess_simplified:             10805
% 3.34/0.98  prop_fo_subsumed:                       65
% 3.34/0.98  prop_solver_time:                       0.
% 3.34/0.98  smt_solver_time:                        0.
% 3.34/0.98  smt_fast_solver_time:                   0.
% 3.34/0.98  prop_fast_solver_time:                  0.
% 3.34/0.98  prop_unsat_core_time:                   0.
% 3.34/0.98  
% 3.34/0.98  ------ QBF
% 3.34/0.98  
% 3.34/0.98  qbf_q_res:                              0
% 3.34/0.98  qbf_num_tautologies:                    0
% 3.34/0.98  qbf_prep_cycles:                        0
% 3.34/0.98  
% 3.34/0.98  ------ BMC1
% 3.34/0.98  
% 3.34/0.98  bmc1_current_bound:                     -1
% 3.34/0.98  bmc1_last_solved_bound:                 -1
% 3.34/0.98  bmc1_unsat_core_size:                   -1
% 3.34/0.98  bmc1_unsat_core_parents_size:           -1
% 3.34/0.98  bmc1_merge_next_fun:                    0
% 3.34/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.34/0.98  
% 3.34/0.98  ------ Instantiation
% 3.34/0.98  
% 3.34/0.98  inst_num_of_clauses:                    1176
% 3.34/0.98  inst_num_in_passive:                    336
% 3.34/0.98  inst_num_in_active:                     487
% 3.34/0.98  inst_num_in_unprocessed:                353
% 3.34/0.98  inst_num_of_loops:                      570
% 3.34/0.98  inst_num_of_learning_restarts:          0
% 3.34/0.98  inst_num_moves_active_passive:          81
% 3.34/0.98  inst_lit_activity:                      0
% 3.34/0.98  inst_lit_activity_moves:                0
% 3.34/0.98  inst_num_tautologies:                   0
% 3.34/0.98  inst_num_prop_implied:                  0
% 3.34/0.98  inst_num_existing_simplified:           0
% 3.34/0.98  inst_num_eq_res_simplified:             0
% 3.34/0.98  inst_num_child_elim:                    0
% 3.34/0.98  inst_num_of_dismatching_blockings:      376
% 3.34/0.98  inst_num_of_non_proper_insts:           1139
% 3.34/0.98  inst_num_of_duplicates:                 0
% 3.34/0.98  inst_inst_num_from_inst_to_res:         0
% 3.34/0.98  inst_dismatching_checking_time:         0.
% 3.34/0.98  
% 3.34/0.98  ------ Resolution
% 3.34/0.98  
% 3.34/0.98  res_num_of_clauses:                     0
% 3.34/0.98  res_num_in_passive:                     0
% 3.34/0.98  res_num_in_active:                      0
% 3.34/0.98  res_num_of_loops:                       169
% 3.34/0.98  res_forward_subset_subsumed:            128
% 3.34/0.98  res_backward_subset_subsumed:           0
% 3.34/0.98  res_forward_subsumed:                   0
% 3.34/0.98  res_backward_subsumed:                  0
% 3.34/0.98  res_forward_subsumption_resolution:     1
% 3.34/0.98  res_backward_subsumption_resolution:    0
% 3.34/0.98  res_clause_to_clause_subsumption:       340
% 3.34/0.98  res_orphan_elimination:                 0
% 3.34/0.98  res_tautology_del:                      62
% 3.34/0.98  res_num_eq_res_simplified:              0
% 3.34/0.98  res_num_sel_changes:                    0
% 3.34/0.98  res_moves_from_active_to_pass:          0
% 3.34/0.98  
% 3.34/0.98  ------ Superposition
% 3.34/0.98  
% 3.34/0.98  sup_time_total:                         0.
% 3.34/0.98  sup_time_generating:                    0.
% 3.34/0.98  sup_time_sim_full:                      0.
% 3.34/0.98  sup_time_sim_immed:                     0.
% 3.34/0.98  
% 3.34/0.98  sup_num_of_clauses:                     114
% 3.34/0.98  sup_num_in_active:                      58
% 3.34/0.98  sup_num_in_passive:                     56
% 3.34/0.98  sup_num_of_loops:                       112
% 3.34/0.98  sup_fw_superposition:                   90
% 3.34/0.98  sup_bw_superposition:                   58
% 3.34/0.98  sup_immediate_simplified:               79
% 3.34/0.98  sup_given_eliminated:                   0
% 3.34/0.98  comparisons_done:                       0
% 3.34/0.98  comparisons_avoided:                    0
% 3.34/0.98  
% 3.34/0.98  ------ Simplifications
% 3.34/0.98  
% 3.34/0.98  
% 3.34/0.98  sim_fw_subset_subsumed:                 6
% 3.34/0.98  sim_bw_subset_subsumed:                 12
% 3.34/0.98  sim_fw_subsumed:                        9
% 3.34/0.98  sim_bw_subsumed:                        3
% 3.34/0.98  sim_fw_subsumption_res:                 4
% 3.34/0.98  sim_bw_subsumption_res:                 0
% 3.34/0.98  sim_tautology_del:                      1
% 3.34/0.98  sim_eq_tautology_del:                   12
% 3.34/0.98  sim_eq_res_simp:                        2
% 3.34/0.98  sim_fw_demodulated:                     7
% 3.34/0.98  sim_bw_demodulated:                     67
% 3.34/0.98  sim_light_normalised:                   43
% 3.34/0.98  sim_joinable_taut:                      0
% 3.34/0.98  sim_joinable_simp:                      0
% 3.34/0.98  sim_ac_normalised:                      0
% 3.34/0.98  sim_smt_subsumption:                    0
% 3.34/0.98  
%------------------------------------------------------------------------------
