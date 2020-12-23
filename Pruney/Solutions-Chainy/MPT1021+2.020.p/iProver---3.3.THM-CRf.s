%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:21 EST 2020

% Result     : Theorem 3.18s
% Output     : CNFRefutation 3.18s
% Verified   : 
% Statistics : Number of formulae       :  196 (3153 expanded)
%              Number of clauses        :  121 ( 935 expanded)
%              Number of leaves         :   18 ( 622 expanded)
%              Depth                    :   26
%              Number of atoms          :  637 (14915 expanded)
%              Number of equality atoms :  301 (1701 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   13 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f80,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f32])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f46,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f47,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f46])).

fof(f52,plain,
    ( ? [X0,X1] :
        ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
        | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
      & v3_funct_2(sK2,sK1,sK1)
      & v1_funct_2(sK2,sK1,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
      | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    & v3_funct_2(sK2,sK1,sK1)
    & v1_funct_2(sK2,sK1,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f47,f52])).

fof(f93,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f53])).

fof(f11,axiom,(
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

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f11])).

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
    inference(flattening,[],[f36])).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f37])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f91,plain,(
    v1_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_1(X1) = k2_funct_2(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f44])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f90,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f92,plain,(
    v3_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

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
    inference(flattening,[],[f40])).

fof(f79,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f16,axiom,(
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
    inference(ennf_transformation,[],[f16])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f42])).

fof(f87,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k2_funct_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f28,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f59,plain,(
    ! [X0] :
      ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f18,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f89,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f98,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f59,f89])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f34])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f60,plain,(
    ! [X0] :
      ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f97,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f60,f89])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f94,plain,
    ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
    | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f53])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f56,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f96,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f57,f89])).

fof(f55,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f1])).

cnf(c_26,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1636,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_10,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1648,plain,
    ( r2_relset_1(X0,X1,X2,X2) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4634,plain,
    ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0)) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1636,c_1648])).

cnf(c_8871,plain,
    ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1636,c_4634])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1627,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1641,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4708,plain,
    ( k1_relset_1(sK1,sK1,sK2) = sK1
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK1,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1627,c_1641])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1649,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2767,plain,
    ( k1_relset_1(sK1,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1627,c_1649])).

cnf(c_4712,plain,
    ( k1_relat_1(sK2) = sK1
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK1,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4708,c_2767])).

cnf(c_38,negated_conjecture,
    ( v1_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_41,plain,
    ( v1_funct_2(sK2,sK1,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_4911,plain,
    ( sK1 = k1_xboole_0
    | k1_relat_1(sK2) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4712,c_41])).

cnf(c_4912,plain,
    ( k1_relat_1(sK2) = sK1
    | sK1 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_4911])).

cnf(c_34,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1629,plain,
    ( k2_funct_2(X0,X1) = k2_funct_1(X1)
    | v1_funct_2(X1,X0,X0) != iProver_top
    | v3_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_2513,plain,
    ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1627,c_1629])).

cnf(c_39,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_37,negated_conjecture,
    ( v3_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2096,plain,
    ( ~ v1_funct_2(sK2,X0,X0)
    | ~ v3_funct_2(sK2,X0,X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v1_funct_1(sK2)
    | k2_funct_2(X0,sK2) = k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_34])).

cnf(c_2260,plain,
    ( ~ v1_funct_2(sK2,sK1,sK1)
    | ~ v3_funct_2(sK2,sK1,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK2)
    | k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2096])).

cnf(c_2791,plain,
    ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2513,c_39,c_38,c_37,c_36,c_2260])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1640,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_5304,plain,
    ( v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2791,c_1640])).

cnf(c_40,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_42,plain,
    ( v3_funct_2(sK2,sK1,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_43,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_6020,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5304,c_40,c_41,c_42,c_43])).

cnf(c_33,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1630,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_6036,plain,
    ( k1_partfun1(X0,X1,sK1,sK1,X2,k2_funct_1(sK2)) = k5_relat_1(X2,k2_funct_1(sK2))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6020,c_1630])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_2(X1,X0)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1637,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_2(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_4203,plain,
    ( v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1627,c_1637])).

cnf(c_4208,plain,
    ( v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4203,c_2791])).

cnf(c_7861,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK1,X2,k2_funct_1(sK2)) = k5_relat_1(X2,k2_funct_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6036,c_40,c_41,c_42,c_4208])).

cnf(c_7862,plain,
    ( k1_partfun1(X0,X1,sK1,sK1,X2,k2_funct_1(sK2)) = k5_relat_1(X2,k2_funct_1(sK2))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_7861])).

cnf(c_7874,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2))
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1627,c_7862])).

cnf(c_1624,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_6,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1651,plain,
    ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3575,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1624,c_1651])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1936,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1958,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_12,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2005,plain,
    ( ~ v3_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | v2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2187,plain,
    ( ~ v3_funct_2(sK2,sK1,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK2)
    | v2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2005])).

cnf(c_3591,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3575,c_39,c_37,c_36,c_1936,c_1958,c_2187])).

cnf(c_7882,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7874,c_3591])).

cnf(c_7924,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7882,c_40])).

cnf(c_3259,plain,
    ( k1_partfun1(X0,X1,sK1,sK1,X2,sK2) = k5_relat_1(X2,sK2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1627,c_1630])).

cnf(c_3719,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK1,X2,sK2) = k5_relat_1(X2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3259,c_40])).

cnf(c_3720,plain,
    ( k1_partfun1(X0,X1,sK1,sK1,X2,sK2) = k5_relat_1(X2,sK2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_3719])).

cnf(c_5310,plain,
    ( k1_partfun1(X0,X0,sK1,sK1,k2_funct_2(X0,X1),sK2) = k5_relat_1(k2_funct_2(X0,X1),sK2)
    | v1_funct_2(X1,X0,X0) != iProver_top
    | v3_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(k2_funct_2(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1640,c_3720])).

cnf(c_6131,plain,
    ( k1_partfun1(X0,X0,sK1,sK1,k2_funct_2(X0,X1),sK2) = k5_relat_1(k2_funct_2(X0,X1),sK2)
    | v1_funct_2(X1,X0,X0) != iProver_top
    | v3_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5310,c_1637])).

cnf(c_6139,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2) = k5_relat_1(k2_funct_2(sK1,sK2),sK2)
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1627,c_6131])).

cnf(c_5,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1652,plain,
    ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4613,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1624,c_1652])).

cnf(c_11,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_21,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_429,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ v5_relat_1(X3,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X3)
    | X3 != X0
    | X4 != X2
    | k2_relat_1(X3) = X4 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_21])).

cnf(c_430,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ v5_relat_1(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(unflattening,[status(thm)],[c_429])).

cnf(c_434,plain,
    ( ~ v1_funct_1(X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v5_relat_1(X0,X2)
    | ~ v3_funct_2(X0,X1,X2)
    | k2_relat_1(X0) = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_430,c_7])).

cnf(c_435,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ v5_relat_1(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(renaming,[status(thm)],[c_434])).

cnf(c_8,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_450,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_435,c_8])).

cnf(c_1623,plain,
    ( k2_relat_1(X0) = X1
    | v3_funct_2(X0,X2,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_450])).

cnf(c_2154,plain,
    ( k2_relat_1(sK2) = sK1
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1627,c_1623])).

cnf(c_2248,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2154,c_40,c_42])).

cnf(c_4617,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4613,c_2248])).

cnf(c_1937,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1936])).

cnf(c_2188,plain,
    ( v3_funct_2(sK2,sK1,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2187])).

cnf(c_4823,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4617,c_40,c_42,c_43,c_1937,c_2188])).

cnf(c_6153,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | v1_funct_2(sK2,sK1,sK1) != iProver_top
    | v3_funct_2(sK2,sK1,sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6139,c_2791,c_4823])).

cnf(c_6030,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k5_relat_1(k2_funct_1(sK2),sK2)
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6020,c_3720])).

cnf(c_6081,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6030,c_4823])).

cnf(c_6301,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6153,c_40,c_41,c_42,c_4208,c_6081])).

cnf(c_35,negated_conjecture,
    ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
    | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1628,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) != iProver_top
    | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_2794,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top
    | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)),k6_partfun1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2791,c_1628])).

cnf(c_6304,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)),k6_partfun1(sK1)) != iProver_top
    | r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6301,c_2794])).

cnf(c_7927,plain,
    ( r2_relset_1(sK1,sK1,k6_partfun1(k1_relat_1(sK2)),k6_partfun1(sK1)) != iProver_top
    | r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7924,c_6304])).

cnf(c_8030,plain,
    ( sK1 = k1_xboole_0
    | r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4912,c_7927])).

cnf(c_9044,plain,
    ( sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8871,c_8030])).

cnf(c_9167,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_relat_1(sK2)),k6_partfun1(k1_xboole_0)) != iProver_top
    | r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),k6_partfun1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9044,c_7927])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1654,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2713,plain,
    ( sK2 = k1_xboole_0
    | sK1 != k1_xboole_0
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2248,c_1654])).

cnf(c_2720,plain,
    ( ~ v1_relat_1(sK2)
    | sK2 = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2713])).

cnf(c_2817,plain,
    ( sK1 != k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2713,c_36,c_1936,c_2720])).

cnf(c_2818,plain,
    ( sK2 = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_2817])).

cnf(c_9191,plain,
    ( sK2 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9044,c_2818])).

cnf(c_9210,plain,
    ( sK2 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_9191])).

cnf(c_9324,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_relat_1(k1_xboole_0)),k6_partfun1(k1_xboole_0)) != iProver_top
    | r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),k6_partfun1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9167,c_9210])).

cnf(c_4,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1653,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2500,plain,
    ( k6_partfun1(X0) = k1_xboole_0
    | k1_xboole_0 != X0
    | v1_relat_1(k6_partfun1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_1653])).

cnf(c_69,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_1930,plain,
    ( ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | v1_relat_1(k6_partfun1(X0)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1931,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_relat_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1930])).

cnf(c_2722,plain,
    ( k1_xboole_0 != X0
    | k6_partfun1(X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2500,c_69,c_1931])).

cnf(c_2723,plain,
    ( k6_partfun1(X0) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(renaming,[status(thm)],[c_2722])).

cnf(c_2727,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_2723])).

cnf(c_3023,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2727,c_4])).

cnf(c_9327,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9324,c_2727,c_3023])).

cnf(c_0,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1923,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1926,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1923])).

cnf(c_1928,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1926])).

cnf(c_115,plain,
    ( r2_relset_1(X0,X1,X2,X2) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_117,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_115])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9327,c_1928,c_117])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:11:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.18/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.18/1.00  
% 3.18/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.18/1.00  
% 3.18/1.00  ------  iProver source info
% 3.18/1.00  
% 3.18/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.18/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.18/1.00  git: non_committed_changes: false
% 3.18/1.00  git: last_make_outside_of_git: false
% 3.18/1.00  
% 3.18/1.00  ------ 
% 3.18/1.00  
% 3.18/1.00  ------ Input Options
% 3.18/1.00  
% 3.18/1.00  --out_options                           all
% 3.18/1.00  --tptp_safe_out                         true
% 3.18/1.00  --problem_path                          ""
% 3.18/1.00  --include_path                          ""
% 3.18/1.00  --clausifier                            res/vclausify_rel
% 3.18/1.00  --clausifier_options                    --mode clausify
% 3.18/1.00  --stdin                                 false
% 3.18/1.00  --stats_out                             all
% 3.18/1.00  
% 3.18/1.00  ------ General Options
% 3.18/1.00  
% 3.18/1.00  --fof                                   false
% 3.18/1.00  --time_out_real                         305.
% 3.18/1.00  --time_out_virtual                      -1.
% 3.18/1.00  --symbol_type_check                     false
% 3.18/1.00  --clausify_out                          false
% 3.18/1.00  --sig_cnt_out                           false
% 3.18/1.00  --trig_cnt_out                          false
% 3.18/1.00  --trig_cnt_out_tolerance                1.
% 3.18/1.00  --trig_cnt_out_sk_spl                   false
% 3.18/1.00  --abstr_cl_out                          false
% 3.18/1.00  
% 3.18/1.00  ------ Global Options
% 3.18/1.00  
% 3.18/1.00  --schedule                              default
% 3.18/1.00  --add_important_lit                     false
% 3.18/1.00  --prop_solver_per_cl                    1000
% 3.18/1.00  --min_unsat_core                        false
% 3.18/1.00  --soft_assumptions                      false
% 3.18/1.00  --soft_lemma_size                       3
% 3.18/1.00  --prop_impl_unit_size                   0
% 3.18/1.00  --prop_impl_unit                        []
% 3.18/1.00  --share_sel_clauses                     true
% 3.18/1.00  --reset_solvers                         false
% 3.18/1.00  --bc_imp_inh                            [conj_cone]
% 3.18/1.00  --conj_cone_tolerance                   3.
% 3.18/1.00  --extra_neg_conj                        none
% 3.18/1.00  --large_theory_mode                     true
% 3.18/1.00  --prolific_symb_bound                   200
% 3.18/1.00  --lt_threshold                          2000
% 3.18/1.00  --clause_weak_htbl                      true
% 3.18/1.00  --gc_record_bc_elim                     false
% 3.18/1.00  
% 3.18/1.00  ------ Preprocessing Options
% 3.18/1.00  
% 3.18/1.00  --preprocessing_flag                    true
% 3.18/1.00  --time_out_prep_mult                    0.1
% 3.18/1.00  --splitting_mode                        input
% 3.18/1.00  --splitting_grd                         true
% 3.18/1.00  --splitting_cvd                         false
% 3.18/1.00  --splitting_cvd_svl                     false
% 3.18/1.00  --splitting_nvd                         32
% 3.18/1.00  --sub_typing                            true
% 3.18/1.00  --prep_gs_sim                           true
% 3.18/1.00  --prep_unflatten                        true
% 3.18/1.00  --prep_res_sim                          true
% 3.18/1.00  --prep_upred                            true
% 3.18/1.00  --prep_sem_filter                       exhaustive
% 3.18/1.00  --prep_sem_filter_out                   false
% 3.18/1.00  --pred_elim                             true
% 3.18/1.00  --res_sim_input                         true
% 3.18/1.00  --eq_ax_congr_red                       true
% 3.18/1.00  --pure_diseq_elim                       true
% 3.18/1.00  --brand_transform                       false
% 3.18/1.00  --non_eq_to_eq                          false
% 3.18/1.00  --prep_def_merge                        true
% 3.18/1.00  --prep_def_merge_prop_impl              false
% 3.18/1.00  --prep_def_merge_mbd                    true
% 3.18/1.00  --prep_def_merge_tr_red                 false
% 3.18/1.00  --prep_def_merge_tr_cl                  false
% 3.18/1.00  --smt_preprocessing                     true
% 3.18/1.00  --smt_ac_axioms                         fast
% 3.18/1.00  --preprocessed_out                      false
% 3.18/1.00  --preprocessed_stats                    false
% 3.18/1.00  
% 3.18/1.00  ------ Abstraction refinement Options
% 3.18/1.00  
% 3.18/1.00  --abstr_ref                             []
% 3.18/1.00  --abstr_ref_prep                        false
% 3.18/1.00  --abstr_ref_until_sat                   false
% 3.18/1.00  --abstr_ref_sig_restrict                funpre
% 3.18/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.18/1.00  --abstr_ref_under                       []
% 3.18/1.00  
% 3.18/1.00  ------ SAT Options
% 3.18/1.00  
% 3.18/1.00  --sat_mode                              false
% 3.18/1.00  --sat_fm_restart_options                ""
% 3.18/1.00  --sat_gr_def                            false
% 3.18/1.00  --sat_epr_types                         true
% 3.18/1.00  --sat_non_cyclic_types                  false
% 3.18/1.00  --sat_finite_models                     false
% 3.18/1.00  --sat_fm_lemmas                         false
% 3.18/1.00  --sat_fm_prep                           false
% 3.18/1.00  --sat_fm_uc_incr                        true
% 3.18/1.00  --sat_out_model                         small
% 3.18/1.00  --sat_out_clauses                       false
% 3.18/1.00  
% 3.18/1.00  ------ QBF Options
% 3.18/1.00  
% 3.18/1.00  --qbf_mode                              false
% 3.18/1.00  --qbf_elim_univ                         false
% 3.18/1.00  --qbf_dom_inst                          none
% 3.18/1.00  --qbf_dom_pre_inst                      false
% 3.18/1.00  --qbf_sk_in                             false
% 3.18/1.00  --qbf_pred_elim                         true
% 3.18/1.00  --qbf_split                             512
% 3.18/1.00  
% 3.18/1.00  ------ BMC1 Options
% 3.18/1.00  
% 3.18/1.00  --bmc1_incremental                      false
% 3.18/1.00  --bmc1_axioms                           reachable_all
% 3.18/1.00  --bmc1_min_bound                        0
% 3.18/1.00  --bmc1_max_bound                        -1
% 3.18/1.00  --bmc1_max_bound_default                -1
% 3.18/1.00  --bmc1_symbol_reachability              true
% 3.18/1.00  --bmc1_property_lemmas                  false
% 3.18/1.00  --bmc1_k_induction                      false
% 3.18/1.00  --bmc1_non_equiv_states                 false
% 3.18/1.00  --bmc1_deadlock                         false
% 3.18/1.00  --bmc1_ucm                              false
% 3.18/1.00  --bmc1_add_unsat_core                   none
% 3.18/1.00  --bmc1_unsat_core_children              false
% 3.18/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.18/1.00  --bmc1_out_stat                         full
% 3.18/1.00  --bmc1_ground_init                      false
% 3.18/1.00  --bmc1_pre_inst_next_state              false
% 3.18/1.00  --bmc1_pre_inst_state                   false
% 3.18/1.00  --bmc1_pre_inst_reach_state             false
% 3.18/1.00  --bmc1_out_unsat_core                   false
% 3.18/1.00  --bmc1_aig_witness_out                  false
% 3.18/1.00  --bmc1_verbose                          false
% 3.18/1.00  --bmc1_dump_clauses_tptp                false
% 3.18/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.18/1.00  --bmc1_dump_file                        -
% 3.18/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.18/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.18/1.00  --bmc1_ucm_extend_mode                  1
% 3.18/1.00  --bmc1_ucm_init_mode                    2
% 3.18/1.00  --bmc1_ucm_cone_mode                    none
% 3.18/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.18/1.00  --bmc1_ucm_relax_model                  4
% 3.18/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.18/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.18/1.00  --bmc1_ucm_layered_model                none
% 3.18/1.00  --bmc1_ucm_max_lemma_size               10
% 3.18/1.00  
% 3.18/1.00  ------ AIG Options
% 3.18/1.00  
% 3.18/1.00  --aig_mode                              false
% 3.18/1.00  
% 3.18/1.00  ------ Instantiation Options
% 3.18/1.00  
% 3.18/1.00  --instantiation_flag                    true
% 3.18/1.00  --inst_sos_flag                         false
% 3.18/1.00  --inst_sos_phase                        true
% 3.18/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.18/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.18/1.00  --inst_lit_sel_side                     num_symb
% 3.18/1.00  --inst_solver_per_active                1400
% 3.18/1.00  --inst_solver_calls_frac                1.
% 3.18/1.00  --inst_passive_queue_type               priority_queues
% 3.18/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.18/1.00  --inst_passive_queues_freq              [25;2]
% 3.18/1.00  --inst_dismatching                      true
% 3.18/1.00  --inst_eager_unprocessed_to_passive     true
% 3.18/1.00  --inst_prop_sim_given                   true
% 3.18/1.00  --inst_prop_sim_new                     false
% 3.18/1.00  --inst_subs_new                         false
% 3.18/1.00  --inst_eq_res_simp                      false
% 3.18/1.00  --inst_subs_given                       false
% 3.18/1.00  --inst_orphan_elimination               true
% 3.18/1.00  --inst_learning_loop_flag               true
% 3.18/1.00  --inst_learning_start                   3000
% 3.18/1.00  --inst_learning_factor                  2
% 3.18/1.00  --inst_start_prop_sim_after_learn       3
% 3.18/1.00  --inst_sel_renew                        solver
% 3.18/1.00  --inst_lit_activity_flag                true
% 3.18/1.00  --inst_restr_to_given                   false
% 3.18/1.00  --inst_activity_threshold               500
% 3.18/1.00  --inst_out_proof                        true
% 3.18/1.00  
% 3.18/1.00  ------ Resolution Options
% 3.18/1.00  
% 3.18/1.00  --resolution_flag                       true
% 3.18/1.00  --res_lit_sel                           adaptive
% 3.18/1.00  --res_lit_sel_side                      none
% 3.18/1.00  --res_ordering                          kbo
% 3.18/1.00  --res_to_prop_solver                    active
% 3.18/1.00  --res_prop_simpl_new                    false
% 3.18/1.00  --res_prop_simpl_given                  true
% 3.18/1.00  --res_passive_queue_type                priority_queues
% 3.18/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.18/1.00  --res_passive_queues_freq               [15;5]
% 3.18/1.00  --res_forward_subs                      full
% 3.18/1.00  --res_backward_subs                     full
% 3.18/1.00  --res_forward_subs_resolution           true
% 3.18/1.00  --res_backward_subs_resolution          true
% 3.18/1.00  --res_orphan_elimination                true
% 3.18/1.00  --res_time_limit                        2.
% 3.18/1.00  --res_out_proof                         true
% 3.18/1.00  
% 3.18/1.00  ------ Superposition Options
% 3.18/1.00  
% 3.18/1.00  --superposition_flag                    true
% 3.18/1.00  --sup_passive_queue_type                priority_queues
% 3.18/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.18/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.18/1.00  --demod_completeness_check              fast
% 3.18/1.00  --demod_use_ground                      true
% 3.18/1.00  --sup_to_prop_solver                    passive
% 3.18/1.00  --sup_prop_simpl_new                    true
% 3.18/1.00  --sup_prop_simpl_given                  true
% 3.18/1.00  --sup_fun_splitting                     false
% 3.18/1.00  --sup_smt_interval                      50000
% 3.18/1.00  
% 3.18/1.00  ------ Superposition Simplification Setup
% 3.18/1.00  
% 3.18/1.00  --sup_indices_passive                   []
% 3.18/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.18/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/1.00  --sup_full_bw                           [BwDemod]
% 3.18/1.00  --sup_immed_triv                        [TrivRules]
% 3.18/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.18/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/1.00  --sup_immed_bw_main                     []
% 3.18/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.18/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.18/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.18/1.00  
% 3.18/1.00  ------ Combination Options
% 3.18/1.00  
% 3.18/1.00  --comb_res_mult                         3
% 3.18/1.00  --comb_sup_mult                         2
% 3.18/1.00  --comb_inst_mult                        10
% 3.18/1.00  
% 3.18/1.00  ------ Debug Options
% 3.18/1.00  
% 3.18/1.00  --dbg_backtrace                         false
% 3.18/1.00  --dbg_dump_prop_clauses                 false
% 3.18/1.00  --dbg_dump_prop_clauses_file            -
% 3.18/1.00  --dbg_out_stat                          false
% 3.18/1.00  ------ Parsing...
% 3.18/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.18/1.00  
% 3.18/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.18/1.00  
% 3.18/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.18/1.00  
% 3.18/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.18/1.00  ------ Proving...
% 3.18/1.00  ------ Problem Properties 
% 3.18/1.00  
% 3.18/1.00  
% 3.18/1.00  clauses                                 35
% 3.18/1.00  conjectures                             5
% 3.18/1.00  EPR                                     3
% 3.18/1.00  Horn                                    31
% 3.18/1.00  unary                                   13
% 3.18/1.00  binary                                  3
% 3.18/1.00  lits                                    95
% 3.18/1.00  lits eq                                 21
% 3.18/1.00  fd_pure                                 0
% 3.18/1.00  fd_pseudo                               0
% 3.18/1.00  fd_cond                                 5
% 3.18/1.00  fd_pseudo_cond                          1
% 3.18/1.00  AC symbols                              0
% 3.18/1.00  
% 3.18/1.00  ------ Schedule dynamic 5 is on 
% 3.18/1.00  
% 3.18/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.18/1.00  
% 3.18/1.00  
% 3.18/1.00  ------ 
% 3.18/1.00  Current options:
% 3.18/1.00  ------ 
% 3.18/1.00  
% 3.18/1.00  ------ Input Options
% 3.18/1.00  
% 3.18/1.00  --out_options                           all
% 3.18/1.00  --tptp_safe_out                         true
% 3.18/1.00  --problem_path                          ""
% 3.18/1.00  --include_path                          ""
% 3.18/1.00  --clausifier                            res/vclausify_rel
% 3.18/1.00  --clausifier_options                    --mode clausify
% 3.18/1.00  --stdin                                 false
% 3.18/1.00  --stats_out                             all
% 3.18/1.00  
% 3.18/1.00  ------ General Options
% 3.18/1.00  
% 3.18/1.00  --fof                                   false
% 3.18/1.00  --time_out_real                         305.
% 3.18/1.00  --time_out_virtual                      -1.
% 3.18/1.00  --symbol_type_check                     false
% 3.18/1.00  --clausify_out                          false
% 3.18/1.00  --sig_cnt_out                           false
% 3.18/1.00  --trig_cnt_out                          false
% 3.18/1.00  --trig_cnt_out_tolerance                1.
% 3.18/1.00  --trig_cnt_out_sk_spl                   false
% 3.18/1.00  --abstr_cl_out                          false
% 3.18/1.00  
% 3.18/1.00  ------ Global Options
% 3.18/1.00  
% 3.18/1.00  --schedule                              default
% 3.18/1.00  --add_important_lit                     false
% 3.18/1.00  --prop_solver_per_cl                    1000
% 3.18/1.00  --min_unsat_core                        false
% 3.18/1.00  --soft_assumptions                      false
% 3.18/1.00  --soft_lemma_size                       3
% 3.18/1.00  --prop_impl_unit_size                   0
% 3.18/1.00  --prop_impl_unit                        []
% 3.18/1.00  --share_sel_clauses                     true
% 3.18/1.00  --reset_solvers                         false
% 3.18/1.00  --bc_imp_inh                            [conj_cone]
% 3.18/1.00  --conj_cone_tolerance                   3.
% 3.18/1.00  --extra_neg_conj                        none
% 3.18/1.00  --large_theory_mode                     true
% 3.18/1.00  --prolific_symb_bound                   200
% 3.18/1.00  --lt_threshold                          2000
% 3.18/1.00  --clause_weak_htbl                      true
% 3.18/1.00  --gc_record_bc_elim                     false
% 3.18/1.00  
% 3.18/1.00  ------ Preprocessing Options
% 3.18/1.00  
% 3.18/1.00  --preprocessing_flag                    true
% 3.18/1.00  --time_out_prep_mult                    0.1
% 3.18/1.00  --splitting_mode                        input
% 3.18/1.00  --splitting_grd                         true
% 3.18/1.00  --splitting_cvd                         false
% 3.18/1.00  --splitting_cvd_svl                     false
% 3.18/1.00  --splitting_nvd                         32
% 3.18/1.00  --sub_typing                            true
% 3.18/1.00  --prep_gs_sim                           true
% 3.18/1.00  --prep_unflatten                        true
% 3.18/1.00  --prep_res_sim                          true
% 3.18/1.00  --prep_upred                            true
% 3.18/1.00  --prep_sem_filter                       exhaustive
% 3.18/1.00  --prep_sem_filter_out                   false
% 3.18/1.00  --pred_elim                             true
% 3.18/1.00  --res_sim_input                         true
% 3.18/1.00  --eq_ax_congr_red                       true
% 3.18/1.00  --pure_diseq_elim                       true
% 3.18/1.00  --brand_transform                       false
% 3.18/1.00  --non_eq_to_eq                          false
% 3.18/1.00  --prep_def_merge                        true
% 3.18/1.00  --prep_def_merge_prop_impl              false
% 3.18/1.00  --prep_def_merge_mbd                    true
% 3.18/1.00  --prep_def_merge_tr_red                 false
% 3.18/1.00  --prep_def_merge_tr_cl                  false
% 3.18/1.00  --smt_preprocessing                     true
% 3.18/1.00  --smt_ac_axioms                         fast
% 3.18/1.00  --preprocessed_out                      false
% 3.18/1.00  --preprocessed_stats                    false
% 3.18/1.00  
% 3.18/1.00  ------ Abstraction refinement Options
% 3.18/1.00  
% 3.18/1.00  --abstr_ref                             []
% 3.18/1.00  --abstr_ref_prep                        false
% 3.18/1.00  --abstr_ref_until_sat                   false
% 3.18/1.00  --abstr_ref_sig_restrict                funpre
% 3.18/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.18/1.00  --abstr_ref_under                       []
% 3.18/1.00  
% 3.18/1.00  ------ SAT Options
% 3.18/1.00  
% 3.18/1.00  --sat_mode                              false
% 3.18/1.00  --sat_fm_restart_options                ""
% 3.18/1.00  --sat_gr_def                            false
% 3.18/1.00  --sat_epr_types                         true
% 3.18/1.00  --sat_non_cyclic_types                  false
% 3.18/1.00  --sat_finite_models                     false
% 3.18/1.00  --sat_fm_lemmas                         false
% 3.18/1.00  --sat_fm_prep                           false
% 3.18/1.00  --sat_fm_uc_incr                        true
% 3.18/1.00  --sat_out_model                         small
% 3.18/1.00  --sat_out_clauses                       false
% 3.18/1.00  
% 3.18/1.00  ------ QBF Options
% 3.18/1.00  
% 3.18/1.00  --qbf_mode                              false
% 3.18/1.00  --qbf_elim_univ                         false
% 3.18/1.00  --qbf_dom_inst                          none
% 3.18/1.00  --qbf_dom_pre_inst                      false
% 3.18/1.00  --qbf_sk_in                             false
% 3.18/1.00  --qbf_pred_elim                         true
% 3.18/1.00  --qbf_split                             512
% 3.18/1.00  
% 3.18/1.00  ------ BMC1 Options
% 3.18/1.00  
% 3.18/1.00  --bmc1_incremental                      false
% 3.18/1.00  --bmc1_axioms                           reachable_all
% 3.18/1.00  --bmc1_min_bound                        0
% 3.18/1.00  --bmc1_max_bound                        -1
% 3.18/1.00  --bmc1_max_bound_default                -1
% 3.18/1.00  --bmc1_symbol_reachability              true
% 3.18/1.00  --bmc1_property_lemmas                  false
% 3.18/1.00  --bmc1_k_induction                      false
% 3.18/1.00  --bmc1_non_equiv_states                 false
% 3.18/1.00  --bmc1_deadlock                         false
% 3.18/1.00  --bmc1_ucm                              false
% 3.18/1.00  --bmc1_add_unsat_core                   none
% 3.18/1.00  --bmc1_unsat_core_children              false
% 3.18/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.18/1.00  --bmc1_out_stat                         full
% 3.18/1.00  --bmc1_ground_init                      false
% 3.18/1.00  --bmc1_pre_inst_next_state              false
% 3.18/1.00  --bmc1_pre_inst_state                   false
% 3.18/1.00  --bmc1_pre_inst_reach_state             false
% 3.18/1.00  --bmc1_out_unsat_core                   false
% 3.18/1.00  --bmc1_aig_witness_out                  false
% 3.18/1.00  --bmc1_verbose                          false
% 3.18/1.00  --bmc1_dump_clauses_tptp                false
% 3.18/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.18/1.00  --bmc1_dump_file                        -
% 3.18/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.18/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.18/1.00  --bmc1_ucm_extend_mode                  1
% 3.18/1.00  --bmc1_ucm_init_mode                    2
% 3.18/1.00  --bmc1_ucm_cone_mode                    none
% 3.18/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.18/1.00  --bmc1_ucm_relax_model                  4
% 3.18/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.18/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.18/1.00  --bmc1_ucm_layered_model                none
% 3.18/1.00  --bmc1_ucm_max_lemma_size               10
% 3.18/1.00  
% 3.18/1.00  ------ AIG Options
% 3.18/1.00  
% 3.18/1.00  --aig_mode                              false
% 3.18/1.00  
% 3.18/1.00  ------ Instantiation Options
% 3.18/1.00  
% 3.18/1.00  --instantiation_flag                    true
% 3.18/1.00  --inst_sos_flag                         false
% 3.18/1.00  --inst_sos_phase                        true
% 3.18/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.18/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.18/1.00  --inst_lit_sel_side                     none
% 3.18/1.00  --inst_solver_per_active                1400
% 3.18/1.00  --inst_solver_calls_frac                1.
% 3.18/1.00  --inst_passive_queue_type               priority_queues
% 3.18/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.18/1.00  --inst_passive_queues_freq              [25;2]
% 3.18/1.00  --inst_dismatching                      true
% 3.18/1.00  --inst_eager_unprocessed_to_passive     true
% 3.18/1.00  --inst_prop_sim_given                   true
% 3.18/1.00  --inst_prop_sim_new                     false
% 3.18/1.00  --inst_subs_new                         false
% 3.18/1.00  --inst_eq_res_simp                      false
% 3.18/1.00  --inst_subs_given                       false
% 3.18/1.00  --inst_orphan_elimination               true
% 3.18/1.00  --inst_learning_loop_flag               true
% 3.18/1.00  --inst_learning_start                   3000
% 3.18/1.00  --inst_learning_factor                  2
% 3.18/1.00  --inst_start_prop_sim_after_learn       3
% 3.18/1.00  --inst_sel_renew                        solver
% 3.18/1.00  --inst_lit_activity_flag                true
% 3.18/1.00  --inst_restr_to_given                   false
% 3.18/1.00  --inst_activity_threshold               500
% 3.18/1.00  --inst_out_proof                        true
% 3.18/1.00  
% 3.18/1.00  ------ Resolution Options
% 3.18/1.00  
% 3.18/1.00  --resolution_flag                       false
% 3.18/1.00  --res_lit_sel                           adaptive
% 3.18/1.00  --res_lit_sel_side                      none
% 3.18/1.00  --res_ordering                          kbo
% 3.18/1.00  --res_to_prop_solver                    active
% 3.18/1.00  --res_prop_simpl_new                    false
% 3.18/1.00  --res_prop_simpl_given                  true
% 3.18/1.00  --res_passive_queue_type                priority_queues
% 3.18/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.18/1.00  --res_passive_queues_freq               [15;5]
% 3.18/1.00  --res_forward_subs                      full
% 3.18/1.00  --res_backward_subs                     full
% 3.18/1.00  --res_forward_subs_resolution           true
% 3.18/1.00  --res_backward_subs_resolution          true
% 3.18/1.00  --res_orphan_elimination                true
% 3.18/1.00  --res_time_limit                        2.
% 3.18/1.00  --res_out_proof                         true
% 3.18/1.00  
% 3.18/1.00  ------ Superposition Options
% 3.18/1.00  
% 3.18/1.00  --superposition_flag                    true
% 3.18/1.00  --sup_passive_queue_type                priority_queues
% 3.18/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.18/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.18/1.00  --demod_completeness_check              fast
% 3.18/1.00  --demod_use_ground                      true
% 3.18/1.00  --sup_to_prop_solver                    passive
% 3.18/1.00  --sup_prop_simpl_new                    true
% 3.18/1.00  --sup_prop_simpl_given                  true
% 3.18/1.00  --sup_fun_splitting                     false
% 3.18/1.00  --sup_smt_interval                      50000
% 3.18/1.00  
% 3.18/1.00  ------ Superposition Simplification Setup
% 3.18/1.00  
% 3.18/1.00  --sup_indices_passive                   []
% 3.18/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.18/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/1.00  --sup_full_bw                           [BwDemod]
% 3.18/1.00  --sup_immed_triv                        [TrivRules]
% 3.18/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.18/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/1.00  --sup_immed_bw_main                     []
% 3.18/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.18/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.18/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.18/1.00  
% 3.18/1.00  ------ Combination Options
% 3.18/1.00  
% 3.18/1.00  --comb_res_mult                         3
% 3.18/1.00  --comb_sup_mult                         2
% 3.18/1.00  --comb_inst_mult                        10
% 3.18/1.00  
% 3.18/1.00  ------ Debug Options
% 3.18/1.00  
% 3.18/1.00  --dbg_backtrace                         false
% 3.18/1.00  --dbg_dump_prop_clauses                 false
% 3.18/1.00  --dbg_dump_prop_clauses_file            -
% 3.18/1.00  --dbg_out_stat                          false
% 3.18/1.00  
% 3.18/1.00  
% 3.18/1.00  
% 3.18/1.00  
% 3.18/1.00  ------ Proving...
% 3.18/1.00  
% 3.18/1.00  
% 3.18/1.00  % SZS status Theorem for theBenchmark.p
% 3.18/1.00  
% 3.18/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.18/1.00  
% 3.18/1.00  fof(f14,axiom,(
% 3.18/1.00    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 3.18/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f21,plain,(
% 3.18/1.00    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.18/1.00    inference(pure_predicate_removal,[],[f14])).
% 3.18/1.00  
% 3.18/1.00  fof(f80,plain,(
% 3.18/1.00    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.18/1.00    inference(cnf_transformation,[],[f21])).
% 3.18/1.00  
% 3.18/1.00  fof(f9,axiom,(
% 3.18/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 3.18/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f32,plain,(
% 3.18/1.00    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.18/1.00    inference(ennf_transformation,[],[f9])).
% 3.18/1.00  
% 3.18/1.00  fof(f33,plain,(
% 3.18/1.00    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.18/1.00    inference(flattening,[],[f32])).
% 3.18/1.00  
% 3.18/1.00  fof(f64,plain,(
% 3.18/1.00    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.18/1.00    inference(cnf_transformation,[],[f33])).
% 3.18/1.00  
% 3.18/1.00  fof(f19,conjecture,(
% 3.18/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 3.18/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f20,negated_conjecture,(
% 3.18/1.00    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 3.18/1.00    inference(negated_conjecture,[],[f19])).
% 3.18/1.00  
% 3.18/1.00  fof(f46,plain,(
% 3.18/1.00    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 3.18/1.00    inference(ennf_transformation,[],[f20])).
% 3.18/1.00  
% 3.18/1.00  fof(f47,plain,(
% 3.18/1.00    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 3.18/1.00    inference(flattening,[],[f46])).
% 3.18/1.00  
% 3.18/1.00  fof(f52,plain,(
% 3.18/1.00    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) | ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v3_funct_2(sK2,sK1,sK1) & v1_funct_2(sK2,sK1,sK1) & v1_funct_1(sK2))),
% 3.18/1.00    introduced(choice_axiom,[])).
% 3.18/1.00  
% 3.18/1.00  fof(f53,plain,(
% 3.18/1.00    (~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) | ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v3_funct_2(sK2,sK1,sK1) & v1_funct_2(sK2,sK1,sK1) & v1_funct_1(sK2)),
% 3.18/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f47,f52])).
% 3.18/1.00  
% 3.18/1.00  fof(f93,plain,(
% 3.18/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 3.18/1.00    inference(cnf_transformation,[],[f53])).
% 3.18/1.00  
% 3.18/1.00  fof(f11,axiom,(
% 3.18/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.18/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f36,plain,(
% 3.18/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.18/1.00    inference(ennf_transformation,[],[f11])).
% 3.18/1.00  
% 3.18/1.00  fof(f37,plain,(
% 3.18/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.18/1.00    inference(flattening,[],[f36])).
% 3.18/1.00  
% 3.18/1.00  fof(f48,plain,(
% 3.18/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.18/1.00    inference(nnf_transformation,[],[f37])).
% 3.18/1.00  
% 3.18/1.00  fof(f68,plain,(
% 3.18/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.18/1.00    inference(cnf_transformation,[],[f48])).
% 3.18/1.00  
% 3.18/1.00  fof(f8,axiom,(
% 3.18/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.18/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f31,plain,(
% 3.18/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.18/1.00    inference(ennf_transformation,[],[f8])).
% 3.18/1.00  
% 3.18/1.00  fof(f63,plain,(
% 3.18/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.18/1.00    inference(cnf_transformation,[],[f31])).
% 3.18/1.00  
% 3.18/1.00  fof(f91,plain,(
% 3.18/1.00    v1_funct_2(sK2,sK1,sK1)),
% 3.18/1.00    inference(cnf_transformation,[],[f53])).
% 3.18/1.00  
% 3.18/1.00  fof(f17,axiom,(
% 3.18/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 3.18/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f44,plain,(
% 3.18/1.00    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.18/1.00    inference(ennf_transformation,[],[f17])).
% 3.18/1.00  
% 3.18/1.00  fof(f45,plain,(
% 3.18/1.00    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.18/1.00    inference(flattening,[],[f44])).
% 3.18/1.00  
% 3.18/1.00  fof(f88,plain,(
% 3.18/1.00    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.18/1.00    inference(cnf_transformation,[],[f45])).
% 3.18/1.00  
% 3.18/1.00  fof(f90,plain,(
% 3.18/1.00    v1_funct_1(sK2)),
% 3.18/1.00    inference(cnf_transformation,[],[f53])).
% 3.18/1.00  
% 3.18/1.00  fof(f92,plain,(
% 3.18/1.00    v3_funct_2(sK2,sK1,sK1)),
% 3.18/1.00    inference(cnf_transformation,[],[f53])).
% 3.18/1.00  
% 3.18/1.00  fof(f13,axiom,(
% 3.18/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 3.18/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f40,plain,(
% 3.18/1.00    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.18/1.00    inference(ennf_transformation,[],[f13])).
% 3.18/1.00  
% 3.18/1.00  fof(f41,plain,(
% 3.18/1.00    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.18/1.00    inference(flattening,[],[f40])).
% 3.18/1.00  
% 3.18/1.00  fof(f79,plain,(
% 3.18/1.00    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.18/1.00    inference(cnf_transformation,[],[f41])).
% 3.18/1.00  
% 3.18/1.00  fof(f16,axiom,(
% 3.18/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.18/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f42,plain,(
% 3.18/1.00    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.18/1.00    inference(ennf_transformation,[],[f16])).
% 3.18/1.00  
% 3.18/1.00  fof(f43,plain,(
% 3.18/1.00    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.18/1.00    inference(flattening,[],[f42])).
% 3.18/1.00  
% 3.18/1.00  fof(f87,plain,(
% 3.18/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.18/1.00    inference(cnf_transformation,[],[f43])).
% 3.18/1.00  
% 3.18/1.00  fof(f76,plain,(
% 3.18/1.00    ( ! [X0,X1] : (v1_funct_1(k2_funct_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.18/1.00    inference(cnf_transformation,[],[f41])).
% 3.18/1.00  
% 3.18/1.00  fof(f5,axiom,(
% 3.18/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))))),
% 3.18/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f27,plain,(
% 3.18/1.00    ! [X0] : (((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.18/1.00    inference(ennf_transformation,[],[f5])).
% 3.18/1.00  
% 3.18/1.00  fof(f28,plain,(
% 3.18/1.00    ! [X0] : ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.18/1.00    inference(flattening,[],[f27])).
% 3.18/1.00  
% 3.18/1.00  fof(f59,plain,(
% 3.18/1.00    ( ! [X0] : (k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.18/1.00    inference(cnf_transformation,[],[f28])).
% 3.18/1.00  
% 3.18/1.00  fof(f18,axiom,(
% 3.18/1.00    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.18/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f89,plain,(
% 3.18/1.00    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.18/1.00    inference(cnf_transformation,[],[f18])).
% 3.18/1.00  
% 3.18/1.00  fof(f98,plain,(
% 3.18/1.00    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.18/1.00    inference(definition_unfolding,[],[f59,f89])).
% 3.18/1.00  
% 3.18/1.00  fof(f6,axiom,(
% 3.18/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.18/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f29,plain,(
% 3.18/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.18/1.00    inference(ennf_transformation,[],[f6])).
% 3.18/1.00  
% 3.18/1.00  fof(f61,plain,(
% 3.18/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.18/1.00    inference(cnf_transformation,[],[f29])).
% 3.18/1.00  
% 3.18/1.00  fof(f10,axiom,(
% 3.18/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 3.18/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f34,plain,(
% 3.18/1.00    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.18/1.00    inference(ennf_transformation,[],[f10])).
% 3.18/1.00  
% 3.18/1.00  fof(f35,plain,(
% 3.18/1.00    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.18/1.00    inference(flattening,[],[f34])).
% 3.18/1.00  
% 3.18/1.00  fof(f66,plain,(
% 3.18/1.00    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.18/1.00    inference(cnf_transformation,[],[f35])).
% 3.18/1.00  
% 3.18/1.00  fof(f60,plain,(
% 3.18/1.00    ( ! [X0] : (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.18/1.00    inference(cnf_transformation,[],[f28])).
% 3.18/1.00  
% 3.18/1.00  fof(f97,plain,(
% 3.18/1.00    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.18/1.00    inference(definition_unfolding,[],[f60,f89])).
% 3.18/1.00  
% 3.18/1.00  fof(f67,plain,(
% 3.18/1.00    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.18/1.00    inference(cnf_transformation,[],[f35])).
% 3.18/1.00  
% 3.18/1.00  fof(f12,axiom,(
% 3.18/1.00    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.18/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f38,plain,(
% 3.18/1.00    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.18/1.00    inference(ennf_transformation,[],[f12])).
% 3.18/1.00  
% 3.18/1.00  fof(f39,plain,(
% 3.18/1.00    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.18/1.00    inference(flattening,[],[f38])).
% 3.18/1.00  
% 3.18/1.00  fof(f49,plain,(
% 3.18/1.00    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.18/1.00    inference(nnf_transformation,[],[f39])).
% 3.18/1.00  
% 3.18/1.00  fof(f74,plain,(
% 3.18/1.00    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.18/1.00    inference(cnf_transformation,[],[f49])).
% 3.18/1.00  
% 3.18/1.00  fof(f7,axiom,(
% 3.18/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.18/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f22,plain,(
% 3.18/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.18/1.00    inference(pure_predicate_removal,[],[f7])).
% 3.18/1.00  
% 3.18/1.00  fof(f30,plain,(
% 3.18/1.00    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.18/1.00    inference(ennf_transformation,[],[f22])).
% 3.18/1.00  
% 3.18/1.00  fof(f62,plain,(
% 3.18/1.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.18/1.00    inference(cnf_transformation,[],[f30])).
% 3.18/1.00  
% 3.18/1.00  fof(f94,plain,(
% 3.18/1.00    ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) | ~r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1))),
% 3.18/1.00    inference(cnf_transformation,[],[f53])).
% 3.18/1.00  
% 3.18/1.00  fof(f3,axiom,(
% 3.18/1.00    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 3.18/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f25,plain,(
% 3.18/1.00    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.18/1.00    inference(ennf_transformation,[],[f3])).
% 3.18/1.00  
% 3.18/1.00  fof(f26,plain,(
% 3.18/1.00    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.18/1.00    inference(flattening,[],[f25])).
% 3.18/1.00  
% 3.18/1.00  fof(f56,plain,(
% 3.18/1.00    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.18/1.00    inference(cnf_transformation,[],[f26])).
% 3.18/1.00  
% 3.18/1.00  fof(f4,axiom,(
% 3.18/1.00    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.18/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f57,plain,(
% 3.18/1.00    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 3.18/1.00    inference(cnf_transformation,[],[f4])).
% 3.18/1.00  
% 3.18/1.00  fof(f96,plain,(
% 3.18/1.00    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 3.18/1.00    inference(definition_unfolding,[],[f57,f89])).
% 3.18/1.00  
% 3.18/1.00  fof(f55,plain,(
% 3.18/1.00    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.18/1.00    inference(cnf_transformation,[],[f26])).
% 3.18/1.00  
% 3.18/1.00  fof(f1,axiom,(
% 3.18/1.00    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.18/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f54,plain,(
% 3.18/1.00    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.18/1.00    inference(cnf_transformation,[],[f1])).
% 3.18/1.00  
% 3.18/1.00  cnf(c_26,plain,
% 3.18/1.00      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.18/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1636,plain,
% 3.18/1.00      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_10,plain,
% 3.18/1.00      ( r2_relset_1(X0,X1,X2,X2)
% 3.18/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.18/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.18/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1648,plain,
% 3.18/1.00      ( r2_relset_1(X0,X1,X2,X2) = iProver_top
% 3.18/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.18/1.00      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_4634,plain,
% 3.18/1.00      ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0)) = iProver_top
% 3.18/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_1636,c_1648]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_8871,plain,
% 3.18/1.00      ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0)) = iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_1636,c_4634]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_36,negated_conjecture,
% 3.18/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 3.18/1.00      inference(cnf_transformation,[],[f93]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1627,plain,
% 3.18/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_19,plain,
% 3.18/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.18/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.18/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.18/1.00      | k1_xboole_0 = X2 ),
% 3.18/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1641,plain,
% 3.18/1.00      ( k1_relset_1(X0,X1,X2) = X0
% 3.18/1.00      | k1_xboole_0 = X1
% 3.18/1.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.18/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_4708,plain,
% 3.18/1.00      ( k1_relset_1(sK1,sK1,sK2) = sK1
% 3.18/1.00      | sK1 = k1_xboole_0
% 3.18/1.00      | v1_funct_2(sK2,sK1,sK1) != iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_1627,c_1641]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_9,plain,
% 3.18/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.18/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.18/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1649,plain,
% 3.18/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.18/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2767,plain,
% 3.18/1.00      ( k1_relset_1(sK1,sK1,sK2) = k1_relat_1(sK2) ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_1627,c_1649]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_4712,plain,
% 3.18/1.00      ( k1_relat_1(sK2) = sK1
% 3.18/1.00      | sK1 = k1_xboole_0
% 3.18/1.00      | v1_funct_2(sK2,sK1,sK1) != iProver_top ),
% 3.18/1.00      inference(demodulation,[status(thm)],[c_4708,c_2767]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_38,negated_conjecture,
% 3.18/1.00      ( v1_funct_2(sK2,sK1,sK1) ),
% 3.18/1.00      inference(cnf_transformation,[],[f91]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_41,plain,
% 3.18/1.00      ( v1_funct_2(sK2,sK1,sK1) = iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_4911,plain,
% 3.18/1.00      ( sK1 = k1_xboole_0 | k1_relat_1(sK2) = sK1 ),
% 3.18/1.00      inference(global_propositional_subsumption,
% 3.18/1.00                [status(thm)],
% 3.18/1.00                [c_4712,c_41]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_4912,plain,
% 3.18/1.00      ( k1_relat_1(sK2) = sK1 | sK1 = k1_xboole_0 ),
% 3.18/1.00      inference(renaming,[status(thm)],[c_4911]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_34,plain,
% 3.18/1.00      ( ~ v1_funct_2(X0,X1,X1)
% 3.18/1.00      | ~ v3_funct_2(X0,X1,X1)
% 3.18/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.18/1.00      | ~ v1_funct_1(X0)
% 3.18/1.00      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 3.18/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1629,plain,
% 3.18/1.00      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
% 3.18/1.00      | v1_funct_2(X1,X0,X0) != iProver_top
% 3.18/1.00      | v3_funct_2(X1,X0,X0) != iProver_top
% 3.18/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 3.18/1.00      | v1_funct_1(X1) != iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2513,plain,
% 3.18/1.00      ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2)
% 3.18/1.00      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.18/1.00      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.18/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_1627,c_1629]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_39,negated_conjecture,
% 3.18/1.00      ( v1_funct_1(sK2) ),
% 3.18/1.00      inference(cnf_transformation,[],[f90]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_37,negated_conjecture,
% 3.18/1.00      ( v3_funct_2(sK2,sK1,sK1) ),
% 3.18/1.00      inference(cnf_transformation,[],[f92]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2096,plain,
% 3.18/1.00      ( ~ v1_funct_2(sK2,X0,X0)
% 3.18/1.00      | ~ v3_funct_2(sK2,X0,X0)
% 3.18/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 3.18/1.00      | ~ v1_funct_1(sK2)
% 3.18/1.00      | k2_funct_2(X0,sK2) = k2_funct_1(sK2) ),
% 3.18/1.00      inference(instantiation,[status(thm)],[c_34]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2260,plain,
% 3.18/1.00      ( ~ v1_funct_2(sK2,sK1,sK1)
% 3.18/1.00      | ~ v3_funct_2(sK2,sK1,sK1)
% 3.18/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.18/1.00      | ~ v1_funct_1(sK2)
% 3.18/1.00      | k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
% 3.18/1.00      inference(instantiation,[status(thm)],[c_2096]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2791,plain,
% 3.18/1.00      ( k2_funct_2(sK1,sK2) = k2_funct_1(sK2) ),
% 3.18/1.00      inference(global_propositional_subsumption,
% 3.18/1.00                [status(thm)],
% 3.18/1.00                [c_2513,c_39,c_38,c_37,c_36,c_2260]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_22,plain,
% 3.18/1.00      ( ~ v1_funct_2(X0,X1,X1)
% 3.18/1.00      | ~ v3_funct_2(X0,X1,X1)
% 3.18/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.18/1.00      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.18/1.00      | ~ v1_funct_1(X0) ),
% 3.18/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1640,plain,
% 3.18/1.00      ( v1_funct_2(X0,X1,X1) != iProver_top
% 3.18/1.00      | v3_funct_2(X0,X1,X1) != iProver_top
% 3.18/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 3.18/1.00      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) = iProver_top
% 3.18/1.00      | v1_funct_1(X0) != iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_5304,plain,
% 3.18/1.00      ( v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.18/1.00      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.18/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
% 3.18/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.18/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_2791,c_1640]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_40,plain,
% 3.18/1.00      ( v1_funct_1(sK2) = iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_42,plain,
% 3.18/1.00      ( v3_funct_2(sK2,sK1,sK1) = iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_43,plain,
% 3.18/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_6020,plain,
% 3.18/1.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 3.18/1.00      inference(global_propositional_subsumption,
% 3.18/1.00                [status(thm)],
% 3.18/1.00                [c_5304,c_40,c_41,c_42,c_43]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_33,plain,
% 3.18/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.18/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.18/1.00      | ~ v1_funct_1(X0)
% 3.18/1.00      | ~ v1_funct_1(X3)
% 3.18/1.00      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.18/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1630,plain,
% 3.18/1.00      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 3.18/1.00      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.18/1.00      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.18/1.00      | v1_funct_1(X5) != iProver_top
% 3.18/1.00      | v1_funct_1(X4) != iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_6036,plain,
% 3.18/1.00      ( k1_partfun1(X0,X1,sK1,sK1,X2,k2_funct_1(sK2)) = k5_relat_1(X2,k2_funct_1(sK2))
% 3.18/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.18/1.00      | v1_funct_1(X2) != iProver_top
% 3.18/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_6020,c_1630]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_25,plain,
% 3.18/1.00      ( ~ v1_funct_2(X0,X1,X1)
% 3.18/1.00      | ~ v3_funct_2(X0,X1,X1)
% 3.18/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.18/1.00      | ~ v1_funct_1(X0)
% 3.18/1.00      | v1_funct_1(k2_funct_2(X1,X0)) ),
% 3.18/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1637,plain,
% 3.18/1.00      ( v1_funct_2(X0,X1,X1) != iProver_top
% 3.18/1.00      | v3_funct_2(X0,X1,X1) != iProver_top
% 3.18/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 3.18/1.00      | v1_funct_1(X0) != iProver_top
% 3.18/1.00      | v1_funct_1(k2_funct_2(X1,X0)) = iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_4203,plain,
% 3.18/1.00      ( v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.18/1.00      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.18/1.00      | v1_funct_1(k2_funct_2(sK1,sK2)) = iProver_top
% 3.18/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_1627,c_1637]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_4208,plain,
% 3.18/1.00      ( v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.18/1.00      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.18/1.00      | v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 3.18/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.18/1.00      inference(light_normalisation,[status(thm)],[c_4203,c_2791]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_7861,plain,
% 3.18/1.00      ( v1_funct_1(X2) != iProver_top
% 3.18/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.18/1.00      | k1_partfun1(X0,X1,sK1,sK1,X2,k2_funct_1(sK2)) = k5_relat_1(X2,k2_funct_1(sK2)) ),
% 3.18/1.00      inference(global_propositional_subsumption,
% 3.18/1.00                [status(thm)],
% 3.18/1.00                [c_6036,c_40,c_41,c_42,c_4208]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_7862,plain,
% 3.18/1.00      ( k1_partfun1(X0,X1,sK1,sK1,X2,k2_funct_1(sK2)) = k5_relat_1(X2,k2_funct_1(sK2))
% 3.18/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.18/1.00      | v1_funct_1(X2) != iProver_top ),
% 3.18/1.00      inference(renaming,[status(thm)],[c_7861]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_7874,plain,
% 3.18/1.00      ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2))
% 3.18/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_1627,c_7862]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1624,plain,
% 3.18/1.00      ( v1_funct_1(sK2) = iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_6,plain,
% 3.18/1.00      ( ~ v1_funct_1(X0)
% 3.18/1.00      | ~ v2_funct_1(X0)
% 3.18/1.00      | ~ v1_relat_1(X0)
% 3.18/1.00      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
% 3.18/1.00      inference(cnf_transformation,[],[f98]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1651,plain,
% 3.18/1.00      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
% 3.18/1.00      | v1_funct_1(X0) != iProver_top
% 3.18/1.00      | v2_funct_1(X0) != iProver_top
% 3.18/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_3575,plain,
% 3.18/1.00      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
% 3.18/1.00      | v2_funct_1(sK2) != iProver_top
% 3.18/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_1624,c_1651]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_7,plain,
% 3.18/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.18/1.00      | v1_relat_1(X0) ),
% 3.18/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1936,plain,
% 3.18/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.18/1.00      | v1_relat_1(sK2) ),
% 3.18/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1958,plain,
% 3.18/1.00      ( ~ v1_funct_1(sK2)
% 3.18/1.00      | ~ v2_funct_1(sK2)
% 3.18/1.00      | ~ v1_relat_1(sK2)
% 3.18/1.00      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
% 3.18/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_12,plain,
% 3.18/1.00      ( ~ v3_funct_2(X0,X1,X2)
% 3.18/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.18/1.00      | ~ v1_funct_1(X0)
% 3.18/1.00      | v2_funct_1(X0) ),
% 3.18/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2005,plain,
% 3.18/1.00      ( ~ v3_funct_2(sK2,X0,X1)
% 3.18/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.18/1.00      | ~ v1_funct_1(sK2)
% 3.18/1.00      | v2_funct_1(sK2) ),
% 3.18/1.00      inference(instantiation,[status(thm)],[c_12]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2187,plain,
% 3.18/1.00      ( ~ v3_funct_2(sK2,sK1,sK1)
% 3.18/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 3.18/1.00      | ~ v1_funct_1(sK2)
% 3.18/1.00      | v2_funct_1(sK2) ),
% 3.18/1.00      inference(instantiation,[status(thm)],[c_2005]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_3591,plain,
% 3.18/1.00      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
% 3.18/1.00      inference(global_propositional_subsumption,
% 3.18/1.00                [status(thm)],
% 3.18/1.00                [c_3575,c_39,c_37,c_36,c_1936,c_1958,c_2187]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_7882,plain,
% 3.18/1.00      ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
% 3.18/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.18/1.00      inference(light_normalisation,[status(thm)],[c_7874,c_3591]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_7924,plain,
% 3.18/1.00      ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
% 3.18/1.00      inference(global_propositional_subsumption,
% 3.18/1.00                [status(thm)],
% 3.18/1.00                [c_7882,c_40]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_3259,plain,
% 3.18/1.00      ( k1_partfun1(X0,X1,sK1,sK1,X2,sK2) = k5_relat_1(X2,sK2)
% 3.18/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.18/1.00      | v1_funct_1(X2) != iProver_top
% 3.18/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_1627,c_1630]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_3719,plain,
% 3.18/1.00      ( v1_funct_1(X2) != iProver_top
% 3.18/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.18/1.00      | k1_partfun1(X0,X1,sK1,sK1,X2,sK2) = k5_relat_1(X2,sK2) ),
% 3.18/1.00      inference(global_propositional_subsumption,
% 3.18/1.00                [status(thm)],
% 3.18/1.00                [c_3259,c_40]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_3720,plain,
% 3.18/1.00      ( k1_partfun1(X0,X1,sK1,sK1,X2,sK2) = k5_relat_1(X2,sK2)
% 3.18/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.18/1.00      | v1_funct_1(X2) != iProver_top ),
% 3.18/1.00      inference(renaming,[status(thm)],[c_3719]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_5310,plain,
% 3.18/1.00      ( k1_partfun1(X0,X0,sK1,sK1,k2_funct_2(X0,X1),sK2) = k5_relat_1(k2_funct_2(X0,X1),sK2)
% 3.18/1.00      | v1_funct_2(X1,X0,X0) != iProver_top
% 3.18/1.00      | v3_funct_2(X1,X0,X0) != iProver_top
% 3.18/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 3.18/1.00      | v1_funct_1(X1) != iProver_top
% 3.18/1.00      | v1_funct_1(k2_funct_2(X0,X1)) != iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_1640,c_3720]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_6131,plain,
% 3.18/1.00      ( k1_partfun1(X0,X0,sK1,sK1,k2_funct_2(X0,X1),sK2) = k5_relat_1(k2_funct_2(X0,X1),sK2)
% 3.18/1.00      | v1_funct_2(X1,X0,X0) != iProver_top
% 3.18/1.00      | v3_funct_2(X1,X0,X0) != iProver_top
% 3.18/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 3.18/1.00      | v1_funct_1(X1) != iProver_top ),
% 3.18/1.00      inference(forward_subsumption_resolution,
% 3.18/1.00                [status(thm)],
% 3.18/1.00                [c_5310,c_1637]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_6139,plain,
% 3.18/1.00      ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2) = k5_relat_1(k2_funct_2(sK1,sK2),sK2)
% 3.18/1.00      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.18/1.00      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.18/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_1627,c_6131]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_5,plain,
% 3.18/1.00      ( ~ v1_funct_1(X0)
% 3.18/1.00      | ~ v2_funct_1(X0)
% 3.18/1.00      | ~ v1_relat_1(X0)
% 3.18/1.00      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
% 3.18/1.00      inference(cnf_transformation,[],[f97]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1652,plain,
% 3.18/1.00      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
% 3.18/1.00      | v1_funct_1(X0) != iProver_top
% 3.18/1.00      | v2_funct_1(X0) != iProver_top
% 3.18/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_4613,plain,
% 3.18/1.00      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
% 3.18/1.00      | v2_funct_1(sK2) != iProver_top
% 3.18/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_1624,c_1652]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_11,plain,
% 3.18/1.00      ( ~ v3_funct_2(X0,X1,X2)
% 3.18/1.00      | v2_funct_2(X0,X2)
% 3.18/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.18/1.00      | ~ v1_funct_1(X0) ),
% 3.18/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_21,plain,
% 3.18/1.00      ( ~ v2_funct_2(X0,X1)
% 3.18/1.00      | ~ v5_relat_1(X0,X1)
% 3.18/1.00      | ~ v1_relat_1(X0)
% 3.18/1.00      | k2_relat_1(X0) = X1 ),
% 3.18/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_429,plain,
% 3.18/1.00      ( ~ v3_funct_2(X0,X1,X2)
% 3.18/1.00      | ~ v5_relat_1(X3,X4)
% 3.18/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.18/1.00      | ~ v1_funct_1(X0)
% 3.18/1.00      | ~ v1_relat_1(X3)
% 3.18/1.00      | X3 != X0
% 3.18/1.00      | X4 != X2
% 3.18/1.00      | k2_relat_1(X3) = X4 ),
% 3.18/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_21]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_430,plain,
% 3.18/1.00      ( ~ v3_funct_2(X0,X1,X2)
% 3.18/1.00      | ~ v5_relat_1(X0,X2)
% 3.18/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.18/1.00      | ~ v1_funct_1(X0)
% 3.18/1.00      | ~ v1_relat_1(X0)
% 3.18/1.00      | k2_relat_1(X0) = X2 ),
% 3.18/1.00      inference(unflattening,[status(thm)],[c_429]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_434,plain,
% 3.18/1.00      ( ~ v1_funct_1(X0)
% 3.18/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.18/1.00      | ~ v5_relat_1(X0,X2)
% 3.18/1.00      | ~ v3_funct_2(X0,X1,X2)
% 3.18/1.00      | k2_relat_1(X0) = X2 ),
% 3.18/1.00      inference(global_propositional_subsumption,
% 3.18/1.00                [status(thm)],
% 3.18/1.00                [c_430,c_7]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_435,plain,
% 3.18/1.00      ( ~ v3_funct_2(X0,X1,X2)
% 3.18/1.00      | ~ v5_relat_1(X0,X2)
% 3.18/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.18/1.00      | ~ v1_funct_1(X0)
% 3.18/1.00      | k2_relat_1(X0) = X2 ),
% 3.18/1.00      inference(renaming,[status(thm)],[c_434]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_8,plain,
% 3.18/1.00      ( v5_relat_1(X0,X1)
% 3.18/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.18/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_450,plain,
% 3.18/1.00      ( ~ v3_funct_2(X0,X1,X2)
% 3.18/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.18/1.00      | ~ v1_funct_1(X0)
% 3.18/1.00      | k2_relat_1(X0) = X2 ),
% 3.18/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_435,c_8]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1623,plain,
% 3.18/1.00      ( k2_relat_1(X0) = X1
% 3.18/1.00      | v3_funct_2(X0,X2,X1) != iProver_top
% 3.18/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 3.18/1.00      | v1_funct_1(X0) != iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_450]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2154,plain,
% 3.18/1.00      ( k2_relat_1(sK2) = sK1
% 3.18/1.00      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.18/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_1627,c_1623]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2248,plain,
% 3.18/1.00      ( k2_relat_1(sK2) = sK1 ),
% 3.18/1.00      inference(global_propositional_subsumption,
% 3.18/1.00                [status(thm)],
% 3.18/1.00                [c_2154,c_40,c_42]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_4617,plain,
% 3.18/1.00      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 3.18/1.00      | v2_funct_1(sK2) != iProver_top
% 3.18/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.18/1.00      inference(light_normalisation,[status(thm)],[c_4613,c_2248]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1937,plain,
% 3.18/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.18/1.00      | v1_relat_1(sK2) = iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_1936]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2188,plain,
% 3.18/1.00      ( v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.18/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 3.18/1.00      | v1_funct_1(sK2) != iProver_top
% 3.18/1.00      | v2_funct_1(sK2) = iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_2187]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_4823,plain,
% 3.18/1.00      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
% 3.18/1.00      inference(global_propositional_subsumption,
% 3.18/1.00                [status(thm)],
% 3.18/1.00                [c_4617,c_40,c_42,c_43,c_1937,c_2188]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_6153,plain,
% 3.18/1.00      ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 3.18/1.00      | v1_funct_2(sK2,sK1,sK1) != iProver_top
% 3.18/1.00      | v3_funct_2(sK2,sK1,sK1) != iProver_top
% 3.18/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.18/1.00      inference(light_normalisation,[status(thm)],[c_6139,c_2791,c_4823]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_6030,plain,
% 3.18/1.00      ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k5_relat_1(k2_funct_1(sK2),sK2)
% 3.18/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_6020,c_3720]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_6081,plain,
% 3.18/1.00      ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 3.18/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.18/1.00      inference(light_normalisation,[status(thm)],[c_6030,c_4823]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_6301,plain,
% 3.18/1.00      ( k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
% 3.18/1.00      inference(global_propositional_subsumption,
% 3.18/1.00                [status(thm)],
% 3.18/1.00                [c_6153,c_40,c_41,c_42,c_4208,c_6081]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_35,negated_conjecture,
% 3.18/1.00      ( ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1))
% 3.18/1.00      | ~ r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) ),
% 3.18/1.00      inference(cnf_transformation,[],[f94]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1628,plain,
% 3.18/1.00      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_2(sK1,sK2),sK2),k6_partfun1(sK1)) != iProver_top
% 3.18/1.00      | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_2(sK1,sK2)),k6_partfun1(sK1)) != iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2794,plain,
% 3.18/1.00      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,k2_funct_1(sK2),sK2),k6_partfun1(sK1)) != iProver_top
% 3.18/1.00      | r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)),k6_partfun1(sK1)) != iProver_top ),
% 3.18/1.00      inference(demodulation,[status(thm)],[c_2791,c_1628]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_6304,plain,
% 3.18/1.00      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,k2_funct_1(sK2)),k6_partfun1(sK1)) != iProver_top
% 3.18/1.00      | r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) != iProver_top ),
% 3.18/1.00      inference(demodulation,[status(thm)],[c_6301,c_2794]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_7927,plain,
% 3.18/1.00      ( r2_relset_1(sK1,sK1,k6_partfun1(k1_relat_1(sK2)),k6_partfun1(sK1)) != iProver_top
% 3.18/1.00      | r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) != iProver_top ),
% 3.18/1.00      inference(demodulation,[status(thm)],[c_7924,c_6304]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_8030,plain,
% 3.18/1.00      ( sK1 = k1_xboole_0
% 3.18/1.00      | r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1)) != iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_4912,c_7927]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_9044,plain,
% 3.18/1.00      ( sK1 = k1_xboole_0 ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_8871,c_8030]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_9167,plain,
% 3.18/1.00      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_relat_1(sK2)),k6_partfun1(k1_xboole_0)) != iProver_top
% 3.18/1.00      | r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),k6_partfun1(k1_xboole_0)) != iProver_top ),
% 3.18/1.00      inference(demodulation,[status(thm)],[c_9044,c_7927]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1,plain,
% 3.18/1.00      ( ~ v1_relat_1(X0)
% 3.18/1.00      | k2_relat_1(X0) != k1_xboole_0
% 3.18/1.00      | k1_xboole_0 = X0 ),
% 3.18/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1654,plain,
% 3.18/1.00      ( k2_relat_1(X0) != k1_xboole_0
% 3.18/1.00      | k1_xboole_0 = X0
% 3.18/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2713,plain,
% 3.18/1.00      ( sK2 = k1_xboole_0
% 3.18/1.00      | sK1 != k1_xboole_0
% 3.18/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_2248,c_1654]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2720,plain,
% 3.18/1.00      ( ~ v1_relat_1(sK2) | sK2 = k1_xboole_0 | sK1 != k1_xboole_0 ),
% 3.18/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_2713]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2817,plain,
% 3.18/1.00      ( sK1 != k1_xboole_0 | sK2 = k1_xboole_0 ),
% 3.18/1.00      inference(global_propositional_subsumption,
% 3.18/1.00                [status(thm)],
% 3.18/1.00                [c_2713,c_36,c_1936,c_2720]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2818,plain,
% 3.18/1.00      ( sK2 = k1_xboole_0 | sK1 != k1_xboole_0 ),
% 3.18/1.00      inference(renaming,[status(thm)],[c_2817]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_9191,plain,
% 3.18/1.00      ( sK2 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.18/1.00      inference(demodulation,[status(thm)],[c_9044,c_2818]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_9210,plain,
% 3.18/1.00      ( sK2 = k1_xboole_0 ),
% 3.18/1.00      inference(equality_resolution_simp,[status(thm)],[c_9191]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_9324,plain,
% 3.18/1.00      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_relat_1(k1_xboole_0)),k6_partfun1(k1_xboole_0)) != iProver_top
% 3.18/1.00      | r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),k6_partfun1(k1_xboole_0)) != iProver_top ),
% 3.18/1.00      inference(light_normalisation,[status(thm)],[c_9167,c_9210]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_4,plain,
% 3.18/1.00      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 3.18/1.00      inference(cnf_transformation,[],[f96]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2,plain,
% 3.18/1.00      ( ~ v1_relat_1(X0)
% 3.18/1.00      | k1_relat_1(X0) != k1_xboole_0
% 3.18/1.00      | k1_xboole_0 = X0 ),
% 3.18/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1653,plain,
% 3.18/1.00      ( k1_relat_1(X0) != k1_xboole_0
% 3.18/1.00      | k1_xboole_0 = X0
% 3.18/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2500,plain,
% 3.18/1.00      ( k6_partfun1(X0) = k1_xboole_0
% 3.18/1.00      | k1_xboole_0 != X0
% 3.18/1.00      | v1_relat_1(k6_partfun1(X0)) != iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_4,c_1653]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_69,plain,
% 3.18/1.00      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1930,plain,
% 3.18/1.00      ( ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 3.18/1.00      | v1_relat_1(k6_partfun1(X0)) ),
% 3.18/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1931,plain,
% 3.18/1.00      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 3.18/1.00      | v1_relat_1(k6_partfun1(X0)) = iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_1930]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2722,plain,
% 3.18/1.00      ( k1_xboole_0 != X0 | k6_partfun1(X0) = k1_xboole_0 ),
% 3.18/1.00      inference(global_propositional_subsumption,
% 3.18/1.00                [status(thm)],
% 3.18/1.00                [c_2500,c_69,c_1931]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2723,plain,
% 3.18/1.00      ( k6_partfun1(X0) = k1_xboole_0 | k1_xboole_0 != X0 ),
% 3.18/1.00      inference(renaming,[status(thm)],[c_2722]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2727,plain,
% 3.18/1.00      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 3.18/1.00      inference(equality_resolution,[status(thm)],[c_2723]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_3023,plain,
% 3.18/1.00      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_2727,c_4]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_9327,plain,
% 3.18/1.00      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.18/1.00      inference(light_normalisation,[status(thm)],[c_9324,c_2727,c_3023]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_0,plain,
% 3.18/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.18/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1923,plain,
% 3.18/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.18/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1926,plain,
% 3.18/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_1923]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1928,plain,
% 3.18/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.18/1.00      inference(instantiation,[status(thm)],[c_1926]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_115,plain,
% 3.18/1.00      ( r2_relset_1(X0,X1,X2,X2) = iProver_top
% 3.18/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.18/1.00      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_117,plain,
% 3.18/1.00      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top
% 3.18/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 3.18/1.00      inference(instantiation,[status(thm)],[c_115]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(contradiction,plain,
% 3.18/1.00      ( $false ),
% 3.18/1.00      inference(minisat,[status(thm)],[c_9327,c_1928,c_117]) ).
% 3.18/1.00  
% 3.18/1.00  
% 3.18/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.18/1.00  
% 3.18/1.00  ------                               Statistics
% 3.18/1.00  
% 3.18/1.00  ------ General
% 3.18/1.00  
% 3.18/1.00  abstr_ref_over_cycles:                  0
% 3.18/1.00  abstr_ref_under_cycles:                 0
% 3.18/1.00  gc_basic_clause_elim:                   0
% 3.18/1.00  forced_gc_time:                         0
% 3.18/1.00  parsing_time:                           0.011
% 3.18/1.00  unif_index_cands_time:                  0.
% 3.18/1.00  unif_index_add_time:                    0.
% 3.18/1.00  orderings_time:                         0.
% 3.18/1.00  out_proof_time:                         0.015
% 3.18/1.00  total_time:                             0.282
% 3.18/1.00  num_of_symbols:                         54
% 3.18/1.00  num_of_terms:                           8603
% 3.18/1.00  
% 3.18/1.00  ------ Preprocessing
% 3.18/1.00  
% 3.18/1.00  num_of_splits:                          0
% 3.18/1.00  num_of_split_atoms:                     0
% 3.18/1.00  num_of_reused_defs:                     0
% 3.18/1.00  num_eq_ax_congr_red:                    16
% 3.18/1.00  num_of_sem_filtered_clauses:            1
% 3.18/1.00  num_of_subtypes:                        0
% 3.18/1.00  monotx_restored_types:                  0
% 3.18/1.00  sat_num_of_epr_types:                   0
% 3.18/1.00  sat_num_of_non_cyclic_types:            0
% 3.18/1.00  sat_guarded_non_collapsed_types:        0
% 3.18/1.00  num_pure_diseq_elim:                    0
% 3.18/1.00  simp_replaced_by:                       0
% 3.18/1.00  res_preprocessed:                       179
% 3.18/1.00  prep_upred:                             0
% 3.18/1.00  prep_unflattend:                        12
% 3.18/1.00  smt_new_axioms:                         0
% 3.18/1.00  pred_elim_cands:                        7
% 3.18/1.00  pred_elim:                              2
% 3.18/1.00  pred_elim_cl:                           4
% 3.18/1.00  pred_elim_cycles:                       6
% 3.18/1.00  merged_defs:                            0
% 3.18/1.00  merged_defs_ncl:                        0
% 3.18/1.00  bin_hyper_res:                          0
% 3.18/1.00  prep_cycles:                            4
% 3.18/1.00  pred_elim_time:                         0.008
% 3.18/1.00  splitting_time:                         0.
% 3.18/1.00  sem_filter_time:                        0.
% 3.18/1.00  monotx_time:                            0.001
% 3.18/1.00  subtype_inf_time:                       0.
% 3.18/1.00  
% 3.18/1.00  ------ Problem properties
% 3.18/1.00  
% 3.18/1.00  clauses:                                35
% 3.18/1.00  conjectures:                            5
% 3.18/1.00  epr:                                    3
% 3.18/1.00  horn:                                   31
% 3.18/1.00  ground:                                 5
% 3.18/1.00  unary:                                  13
% 3.18/1.00  binary:                                 3
% 3.18/1.00  lits:                                   95
% 3.18/1.00  lits_eq:                                21
% 3.18/1.00  fd_pure:                                0
% 3.18/1.00  fd_pseudo:                              0
% 3.18/1.00  fd_cond:                                5
% 3.18/1.00  fd_pseudo_cond:                         1
% 3.18/1.00  ac_symbols:                             0
% 3.18/1.00  
% 3.18/1.00  ------ Propositional Solver
% 3.18/1.00  
% 3.18/1.00  prop_solver_calls:                      28
% 3.18/1.00  prop_fast_solver_calls:                 1431
% 3.18/1.00  smt_solver_calls:                       0
% 3.18/1.00  smt_fast_solver_calls:                  0
% 3.18/1.00  prop_num_of_clauses:                    3329
% 3.18/1.00  prop_preprocess_simplified:             10543
% 3.18/1.00  prop_fo_subsumed:                       77
% 3.18/1.00  prop_solver_time:                       0.
% 3.18/1.00  smt_solver_time:                        0.
% 3.18/1.00  smt_fast_solver_time:                   0.
% 3.18/1.00  prop_fast_solver_time:                  0.
% 3.18/1.00  prop_unsat_core_time:                   0.
% 3.18/1.00  
% 3.18/1.00  ------ QBF
% 3.18/1.00  
% 3.18/1.00  qbf_q_res:                              0
% 3.18/1.00  qbf_num_tautologies:                    0
% 3.18/1.00  qbf_prep_cycles:                        0
% 3.18/1.00  
% 3.18/1.00  ------ BMC1
% 3.18/1.00  
% 3.18/1.00  bmc1_current_bound:                     -1
% 3.18/1.00  bmc1_last_solved_bound:                 -1
% 3.18/1.00  bmc1_unsat_core_size:                   -1
% 3.18/1.00  bmc1_unsat_core_parents_size:           -1
% 3.18/1.00  bmc1_merge_next_fun:                    0
% 3.18/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.18/1.00  
% 3.18/1.00  ------ Instantiation
% 3.18/1.00  
% 3.18/1.00  inst_num_of_clauses:                    1021
% 3.18/1.00  inst_num_in_passive:                    490
% 3.18/1.00  inst_num_in_active:                     460
% 3.18/1.00  inst_num_in_unprocessed:                71
% 3.18/1.00  inst_num_of_loops:                      510
% 3.18/1.00  inst_num_of_learning_restarts:          0
% 3.18/1.00  inst_num_moves_active_passive:          46
% 3.18/1.00  inst_lit_activity:                      0
% 3.18/1.00  inst_lit_activity_moves:                0
% 3.18/1.00  inst_num_tautologies:                   0
% 3.18/1.00  inst_num_prop_implied:                  0
% 3.18/1.00  inst_num_existing_simplified:           0
% 3.18/1.00  inst_num_eq_res_simplified:             0
% 3.18/1.00  inst_num_child_elim:                    0
% 3.18/1.00  inst_num_of_dismatching_blockings:      355
% 3.18/1.00  inst_num_of_non_proper_insts:           827
% 3.18/1.00  inst_num_of_duplicates:                 0
% 3.18/1.00  inst_inst_num_from_inst_to_res:         0
% 3.18/1.00  inst_dismatching_checking_time:         0.
% 3.18/1.00  
% 3.18/1.00  ------ Resolution
% 3.18/1.00  
% 3.18/1.00  res_num_of_clauses:                     0
% 3.18/1.00  res_num_in_passive:                     0
% 3.18/1.00  res_num_in_active:                      0
% 3.18/1.00  res_num_of_loops:                       183
% 3.18/1.00  res_forward_subset_subsumed:            96
% 3.18/1.00  res_backward_subset_subsumed:           12
% 3.18/1.00  res_forward_subsumed:                   0
% 3.18/1.00  res_backward_subsumed:                  0
% 3.18/1.00  res_forward_subsumption_resolution:     1
% 3.18/1.00  res_backward_subsumption_resolution:    0
% 3.18/1.00  res_clause_to_clause_subsumption:       273
% 3.18/1.00  res_orphan_elimination:                 0
% 3.18/1.00  res_tautology_del:                      29
% 3.18/1.00  res_num_eq_res_simplified:              0
% 3.18/1.00  res_num_sel_changes:                    0
% 3.18/1.00  res_moves_from_active_to_pass:          0
% 3.18/1.00  
% 3.18/1.00  ------ Superposition
% 3.18/1.00  
% 3.18/1.00  sup_time_total:                         0.
% 3.18/1.00  sup_time_generating:                    0.
% 3.18/1.00  sup_time_sim_full:                      0.
% 3.18/1.00  sup_time_sim_immed:                     0.
% 3.18/1.00  
% 3.18/1.00  sup_num_of_clauses:                     117
% 3.18/1.00  sup_num_in_active:                      59
% 3.18/1.00  sup_num_in_passive:                     58
% 3.18/1.00  sup_num_of_loops:                       101
% 3.18/1.00  sup_fw_superposition:                   103
% 3.18/1.00  sup_bw_superposition:                   55
% 3.18/1.00  sup_immediate_simplified:               38
% 3.18/1.00  sup_given_eliminated:                   0
% 3.18/1.00  comparisons_done:                       0
% 3.18/1.00  comparisons_avoided:                    0
% 3.18/1.00  
% 3.18/1.00  ------ Simplifications
% 3.18/1.00  
% 3.18/1.00  
% 3.18/1.00  sim_fw_subset_subsumed:                 9
% 3.18/1.00  sim_bw_subset_subsumed:                 9
% 3.18/1.00  sim_fw_subsumed:                        7
% 3.18/1.00  sim_bw_subsumed:                        5
% 3.18/1.00  sim_fw_subsumption_res:                 3
% 3.18/1.00  sim_bw_subsumption_res:                 0
% 3.18/1.00  sim_tautology_del:                      0
% 3.18/1.00  sim_eq_tautology_del:                   14
% 3.18/1.00  sim_eq_res_simp:                        2
% 3.18/1.00  sim_fw_demodulated:                     8
% 3.18/1.00  sim_bw_demodulated:                     56
% 3.18/1.00  sim_light_normalised:                   44
% 3.18/1.00  sim_joinable_taut:                      0
% 3.18/1.00  sim_joinable_simp:                      0
% 3.18/1.00  sim_ac_normalised:                      0
% 3.18/1.00  sim_smt_subsumption:                    0
% 3.18/1.00  
%------------------------------------------------------------------------------
