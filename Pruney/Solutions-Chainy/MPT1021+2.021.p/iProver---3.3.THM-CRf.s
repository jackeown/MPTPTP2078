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
% DateTime   : Thu Dec  3 12:07:21 EST 2020

% Result     : Theorem 4.00s
% Output     : CNFRefutation 4.00s
% Verified   : 
% Statistics : Number of formulae       :  216 (7029 expanded)
%              Number of clauses        :  129 (2082 expanded)
%              Number of leaves         :   21 (1376 expanded)
%              Depth                    :   30
%              Number of atoms          :  667 (32979 expanded)
%              Number of equality atoms :  306 (3711 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   13 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f48,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f49,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f48])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f49,f55])).

fof(f94,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f56])).

fof(f14,axiom,(
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
    inference(ennf_transformation,[],[f14])).

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
    inference(flattening,[],[f38])).

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
    inference(nnf_transformation,[],[f39])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f92,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f56])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_1(X1) = k2_funct_2(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f46])).

fof(f89,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f91,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f93,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f56])).

fof(f16,axiom,(
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
    inference(ennf_transformation,[],[f16])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f42])).

fof(f86,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f44])).

fof(f88,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f83,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k2_funct_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f30,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f64,plain,(
    ! [X0] :
      ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f20,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f90,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f20])).

fof(f98,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f64,f90])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f36])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f65,plain,(
    ! [X0] :
      ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f97,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f65,f90])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f40])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f95,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f56])).

fof(f17,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f87,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f12,axiom,(
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
    inference(ennf_transformation,[],[f12])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f34])).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f102,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f71])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f50])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f101,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f59])).

fof(f1,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f57,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f96,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f63,f90])).

fof(f8,axiom,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f99,plain,(
    ! [X0] : k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
    inference(definition_unfolding,[],[f66,f90,f90])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1339,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1348,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_4302,plain,
    ( k1_relset_1(sK0,sK0,sK1) = sK0
    | sK0 = k1_xboole_0
    | v1_funct_2(sK1,sK0,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1339,c_1348])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1357,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2537,plain,
    ( k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_1339,c_1357])).

cnf(c_4312,plain,
    ( k1_relat_1(sK1) = sK0
    | sK0 = k1_xboole_0
    | v1_funct_2(sK1,sK0,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4302,c_2537])).

cnf(c_36,negated_conjecture,
    ( v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_39,plain,
    ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_4573,plain,
    ( sK0 = k1_xboole_0
    | k1_relat_1(sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4312,c_39])).

cnf(c_4574,plain,
    ( k1_relat_1(sK1) = sK0
    | sK0 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_4573])).

cnf(c_32,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1341,plain,
    ( k2_funct_2(X0,X1) = k2_funct_1(X1)
    | v1_funct_2(X1,X0,X0) != iProver_top
    | v3_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_6564,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1339,c_1341])).

cnf(c_37,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_35,negated_conjecture,
    ( v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1713,plain,
    ( ~ v1_funct_2(sK1,X0,X0)
    | ~ v3_funct_2(sK1,X0,X0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v1_funct_1(sK1)
    | k2_funct_2(X0,sK1) = k2_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_1849,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1713])).

cnf(c_6756,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6564,c_37,c_36,c_35,c_34,c_1849])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1347,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_6777,plain,
    ( v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_6756,c_1347])).

cnf(c_38,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_40,plain,
    ( v3_funct_2(sK1,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_41,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_7394,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6777,c_38,c_39,c_40,c_41])).

cnf(c_31,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1342,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_9657,plain,
    ( k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7394,c_1342])).

cnf(c_29,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_2(X1,X0)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1344,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_2(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3020,plain,
    ( v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(k2_funct_2(sK0,sK1)) = iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1339,c_1344])).

cnf(c_1693,plain,
    ( ~ v1_funct_2(sK1,X0,X0)
    | ~ v3_funct_2(sK1,X0,X0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | v1_funct_1(k2_funct_2(X0,sK1))
    | ~ v1_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_1838,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v1_funct_1(k2_funct_2(sK0,sK1))
    | ~ v1_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1693])).

cnf(c_1839,plain,
    ( v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(k2_funct_2(sK0,sK1)) = iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1838])).

cnf(c_3262,plain,
    ( v1_funct_1(k2_funct_2(sK0,sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3020,c_38,c_39,c_40,c_41,c_1839])).

cnf(c_6761,plain,
    ( v1_funct_1(k2_funct_1(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6756,c_3262])).

cnf(c_13666,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9657,c_6761])).

cnf(c_13667,plain,
    ( k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_13666])).

cnf(c_13678,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k5_relat_1(sK1,k2_funct_1(sK1))
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1339,c_13667])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1358,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1997,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1339,c_1358])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1359,plain,
    ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3235,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
    | v1_funct_1(sK1) != iProver_top
    | v2_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1997,c_1359])).

cnf(c_1629,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1740,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_16,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1669,plain,
    ( ~ v3_funct_2(sK1,X0,X1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK1)
    | v2_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1780,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | v2_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1669])).

cnf(c_3431,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3235,c_37,c_35,c_34,c_1629,c_1740,c_1780])).

cnf(c_13700,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
    | v1_funct_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13678,c_3431])).

cnf(c_13739,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13700,c_38])).

cnf(c_9656,plain,
    ( k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1339,c_1342])).

cnf(c_10139,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9656,c_38])).

cnf(c_10140,plain,
    ( k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_10139])).

cnf(c_10149,plain,
    ( k1_partfun1(X0,X0,sK0,sK0,k2_funct_2(X0,X1),sK1) = k5_relat_1(k2_funct_2(X0,X1),sK1)
    | v1_funct_2(X1,X0,X0) != iProver_top
    | v3_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(k2_funct_2(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1347,c_10140])).

cnf(c_11225,plain,
    ( k1_partfun1(X0,X0,sK0,sK0,k2_funct_2(X0,X1),sK1) = k5_relat_1(k2_funct_2(X0,X1),sK1)
    | v1_funct_2(X1,X0,X0) != iProver_top
    | v3_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_10149,c_1344])).

cnf(c_11232,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1) = k5_relat_1(k2_funct_2(sK0,sK1),sK1)
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1339,c_11225])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1360,plain,
    ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3887,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1))
    | v1_funct_1(sK1) != iProver_top
    | v2_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1997,c_1360])).

cnf(c_15,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_11,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_25,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_395,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_11,c_25])).

cnf(c_407,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | k2_relat_1(X0) = X1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_395,c_10])).

cnf(c_480,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | X3 != X0
    | X5 != X2
    | k2_relat_1(X3) = X5 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_407])).

cnf(c_481,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(unflattening,[status(thm)],[c_480])).

cnf(c_1334,plain,
    ( k2_relat_1(X0) = X1
    | v3_funct_2(X0,X2,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_481])).

cnf(c_2169,plain,
    ( k2_relat_1(sK1) = sK0
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1339,c_1334])).

cnf(c_1698,plain,
    ( ~ v3_funct_2(sK1,X0,X1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(sK1)
    | k2_relat_1(sK1) = X1 ),
    inference(instantiation,[status(thm)],[c_481])).

cnf(c_1844,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | k2_relat_1(sK1) = sK0 ),
    inference(instantiation,[status(thm)],[c_1698])).

cnf(c_1972,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | k2_relat_1(sK1) = sK0 ),
    inference(instantiation,[status(thm)],[c_1844])).

cnf(c_2693,plain,
    ( k2_relat_1(sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2169,c_37,c_35,c_34,c_1972])).

cnf(c_3891,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
    | v1_funct_1(sK1) != iProver_top
    | v2_funct_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3887,c_2693])).

cnf(c_1781,plain,
    ( v3_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v2_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1780])).

cnf(c_3915,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3891,c_38,c_40,c_41,c_1781])).

cnf(c_11258,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11232,c_3915,c_6756])).

cnf(c_10152,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k5_relat_1(k2_funct_1(sK1),sK1)
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7394,c_10140])).

cnf(c_10169,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10152,c_3915])).

cnf(c_11371,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11258,c_6761,c_10169])).

cnf(c_33,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1340,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) != iProver_top
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_6762,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) != iProver_top
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6756,c_1340])).

cnf(c_11374,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top
    | r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11371,c_6762])).

cnf(c_30,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1343,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_13,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1356,plain,
    ( r2_relset_1(X0,X1,X2,X2) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2369,plain,
    ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1343,c_1356])).

cnf(c_11379,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_11374,c_2369])).

cnf(c_13742,plain,
    ( r2_relset_1(sK0,sK0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_13739,c_11379])).

cnf(c_13993,plain,
    ( sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4574,c_13742])).

cnf(c_13998,plain,
    ( sK0 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_13993,c_2369])).

cnf(c_14047,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_13998,c_1339])).

cnf(c_2,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_14055,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_14047,c_2])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_380,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X0 != X2
    | k1_xboole_0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_5])).

cnf(c_381,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_380])).

cnf(c_1335,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_381])).

cnf(c_15494,plain,
    ( sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_14055,c_1335])).

cnf(c_13999,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_13998,c_13742])).

cnf(c_6,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_14262,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_relat_1(sK1)),k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13999,c_6])).

cnf(c_17362,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_relat_1(k1_xboole_0)),k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_15494,c_14262])).

cnf(c_14043,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_13998,c_3915])).

cnf(c_14064,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_14043,c_6])).

cnf(c_17370,plain,
    ( k5_relat_1(k2_funct_1(k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_15494,c_14064])).

cnf(c_9,plain,
    ( k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1752,plain,
    ( k2_funct_1(k1_xboole_0) = k6_partfun1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_6,c_9])).

cnf(c_1753,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1752,c_6])).

cnf(c_17405,plain,
    ( k5_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_17370,c_1753])).

cnf(c_17379,plain,
    ( k5_relat_1(k1_xboole_0,k2_funct_1(k1_xboole_0)) = k6_partfun1(k1_relat_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm)],[c_15494,c_3431])).

cnf(c_17385,plain,
    ( k5_relat_1(k1_xboole_0,k1_xboole_0) = k6_partfun1(k1_relat_1(k1_xboole_0)) ),
    inference(light_normalisation,[status(thm)],[c_17379,c_1753])).

cnf(c_17406,plain,
    ( k6_partfun1(k1_relat_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_17405,c_17385])).

cnf(c_17428,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_17362,c_17406])).

cnf(c_4,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1617,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1620,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1617])).

cnf(c_1622,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1620])).

cnf(c_98,plain,
    ( r2_relset_1(X0,X1,X2,X2) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_100,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_98])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_17428,c_1622,c_100])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:12:15 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 4.00/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.00/0.98  
% 4.00/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.00/0.98  
% 4.00/0.98  ------  iProver source info
% 4.00/0.98  
% 4.00/0.98  git: date: 2020-06-30 10:37:57 +0100
% 4.00/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.00/0.98  git: non_committed_changes: false
% 4.00/0.98  git: last_make_outside_of_git: false
% 4.00/0.98  
% 4.00/0.98  ------ 
% 4.00/0.98  
% 4.00/0.98  ------ Input Options
% 4.00/0.98  
% 4.00/0.98  --out_options                           all
% 4.00/0.98  --tptp_safe_out                         true
% 4.00/0.98  --problem_path                          ""
% 4.00/0.98  --include_path                          ""
% 4.00/0.98  --clausifier                            res/vclausify_rel
% 4.00/0.98  --clausifier_options                    --mode clausify
% 4.00/0.98  --stdin                                 false
% 4.00/0.98  --stats_out                             all
% 4.00/0.98  
% 4.00/0.98  ------ General Options
% 4.00/0.98  
% 4.00/0.98  --fof                                   false
% 4.00/0.98  --time_out_real                         305.
% 4.00/0.98  --time_out_virtual                      -1.
% 4.00/0.98  --symbol_type_check                     false
% 4.00/0.98  --clausify_out                          false
% 4.00/0.98  --sig_cnt_out                           false
% 4.00/0.98  --trig_cnt_out                          false
% 4.00/0.98  --trig_cnt_out_tolerance                1.
% 4.00/0.98  --trig_cnt_out_sk_spl                   false
% 4.00/0.98  --abstr_cl_out                          false
% 4.00/0.98  
% 4.00/0.98  ------ Global Options
% 4.00/0.98  
% 4.00/0.98  --schedule                              default
% 4.00/0.98  --add_important_lit                     false
% 4.00/0.98  --prop_solver_per_cl                    1000
% 4.00/0.98  --min_unsat_core                        false
% 4.00/0.98  --soft_assumptions                      false
% 4.00/0.98  --soft_lemma_size                       3
% 4.00/0.98  --prop_impl_unit_size                   0
% 4.00/0.98  --prop_impl_unit                        []
% 4.00/0.98  --share_sel_clauses                     true
% 4.00/0.98  --reset_solvers                         false
% 4.00/0.98  --bc_imp_inh                            [conj_cone]
% 4.00/0.98  --conj_cone_tolerance                   3.
% 4.00/0.98  --extra_neg_conj                        none
% 4.00/0.98  --large_theory_mode                     true
% 4.00/0.98  --prolific_symb_bound                   200
% 4.00/0.98  --lt_threshold                          2000
% 4.00/0.98  --clause_weak_htbl                      true
% 4.00/0.98  --gc_record_bc_elim                     false
% 4.00/0.98  
% 4.00/0.98  ------ Preprocessing Options
% 4.00/0.98  
% 4.00/0.98  --preprocessing_flag                    true
% 4.00/0.98  --time_out_prep_mult                    0.1
% 4.00/0.98  --splitting_mode                        input
% 4.00/0.98  --splitting_grd                         true
% 4.00/0.98  --splitting_cvd                         false
% 4.00/0.98  --splitting_cvd_svl                     false
% 4.00/0.98  --splitting_nvd                         32
% 4.00/0.98  --sub_typing                            true
% 4.00/0.98  --prep_gs_sim                           true
% 4.00/0.98  --prep_unflatten                        true
% 4.00/0.98  --prep_res_sim                          true
% 4.00/0.98  --prep_upred                            true
% 4.00/0.98  --prep_sem_filter                       exhaustive
% 4.00/0.98  --prep_sem_filter_out                   false
% 4.00/0.98  --pred_elim                             true
% 4.00/0.98  --res_sim_input                         true
% 4.00/0.98  --eq_ax_congr_red                       true
% 4.00/0.98  --pure_diseq_elim                       true
% 4.00/0.98  --brand_transform                       false
% 4.00/0.98  --non_eq_to_eq                          false
% 4.00/0.98  --prep_def_merge                        true
% 4.00/0.98  --prep_def_merge_prop_impl              false
% 4.00/0.98  --prep_def_merge_mbd                    true
% 4.00/0.98  --prep_def_merge_tr_red                 false
% 4.00/0.98  --prep_def_merge_tr_cl                  false
% 4.00/0.98  --smt_preprocessing                     true
% 4.00/0.98  --smt_ac_axioms                         fast
% 4.00/0.98  --preprocessed_out                      false
% 4.00/0.98  --preprocessed_stats                    false
% 4.00/0.98  
% 4.00/0.98  ------ Abstraction refinement Options
% 4.00/0.98  
% 4.00/0.98  --abstr_ref                             []
% 4.00/0.98  --abstr_ref_prep                        false
% 4.00/0.98  --abstr_ref_until_sat                   false
% 4.00/0.98  --abstr_ref_sig_restrict                funpre
% 4.00/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 4.00/0.98  --abstr_ref_under                       []
% 4.00/0.98  
% 4.00/0.98  ------ SAT Options
% 4.00/0.98  
% 4.00/0.98  --sat_mode                              false
% 4.00/0.98  --sat_fm_restart_options                ""
% 4.00/0.98  --sat_gr_def                            false
% 4.00/0.98  --sat_epr_types                         true
% 4.00/0.98  --sat_non_cyclic_types                  false
% 4.00/0.98  --sat_finite_models                     false
% 4.00/0.98  --sat_fm_lemmas                         false
% 4.00/0.98  --sat_fm_prep                           false
% 4.00/0.98  --sat_fm_uc_incr                        true
% 4.00/0.98  --sat_out_model                         small
% 4.00/0.98  --sat_out_clauses                       false
% 4.00/0.98  
% 4.00/0.98  ------ QBF Options
% 4.00/0.98  
% 4.00/0.98  --qbf_mode                              false
% 4.00/0.98  --qbf_elim_univ                         false
% 4.00/0.98  --qbf_dom_inst                          none
% 4.00/0.98  --qbf_dom_pre_inst                      false
% 4.00/0.98  --qbf_sk_in                             false
% 4.00/0.98  --qbf_pred_elim                         true
% 4.00/0.98  --qbf_split                             512
% 4.00/0.98  
% 4.00/0.98  ------ BMC1 Options
% 4.00/0.98  
% 4.00/0.98  --bmc1_incremental                      false
% 4.00/0.98  --bmc1_axioms                           reachable_all
% 4.00/0.98  --bmc1_min_bound                        0
% 4.00/0.98  --bmc1_max_bound                        -1
% 4.00/0.98  --bmc1_max_bound_default                -1
% 4.00/0.98  --bmc1_symbol_reachability              true
% 4.00/0.98  --bmc1_property_lemmas                  false
% 4.00/0.98  --bmc1_k_induction                      false
% 4.00/0.98  --bmc1_non_equiv_states                 false
% 4.00/0.98  --bmc1_deadlock                         false
% 4.00/0.98  --bmc1_ucm                              false
% 4.00/0.98  --bmc1_add_unsat_core                   none
% 4.00/0.98  --bmc1_unsat_core_children              false
% 4.00/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 4.00/0.98  --bmc1_out_stat                         full
% 4.00/0.98  --bmc1_ground_init                      false
% 4.00/0.98  --bmc1_pre_inst_next_state              false
% 4.00/0.98  --bmc1_pre_inst_state                   false
% 4.00/0.98  --bmc1_pre_inst_reach_state             false
% 4.00/0.98  --bmc1_out_unsat_core                   false
% 4.00/0.98  --bmc1_aig_witness_out                  false
% 4.00/0.98  --bmc1_verbose                          false
% 4.00/0.98  --bmc1_dump_clauses_tptp                false
% 4.00/0.98  --bmc1_dump_unsat_core_tptp             false
% 4.00/0.98  --bmc1_dump_file                        -
% 4.00/0.98  --bmc1_ucm_expand_uc_limit              128
% 4.00/0.98  --bmc1_ucm_n_expand_iterations          6
% 4.00/0.98  --bmc1_ucm_extend_mode                  1
% 4.00/0.98  --bmc1_ucm_init_mode                    2
% 4.00/0.98  --bmc1_ucm_cone_mode                    none
% 4.00/0.98  --bmc1_ucm_reduced_relation_type        0
% 4.00/0.98  --bmc1_ucm_relax_model                  4
% 4.00/0.98  --bmc1_ucm_full_tr_after_sat            true
% 4.00/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 4.00/0.98  --bmc1_ucm_layered_model                none
% 4.00/0.98  --bmc1_ucm_max_lemma_size               10
% 4.00/0.98  
% 4.00/0.98  ------ AIG Options
% 4.00/0.98  
% 4.00/0.98  --aig_mode                              false
% 4.00/0.98  
% 4.00/0.98  ------ Instantiation Options
% 4.00/0.98  
% 4.00/0.98  --instantiation_flag                    true
% 4.00/0.98  --inst_sos_flag                         false
% 4.00/0.98  --inst_sos_phase                        true
% 4.00/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.00/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.00/0.98  --inst_lit_sel_side                     num_symb
% 4.00/0.98  --inst_solver_per_active                1400
% 4.00/0.98  --inst_solver_calls_frac                1.
% 4.00/0.98  --inst_passive_queue_type               priority_queues
% 4.00/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.00/0.98  --inst_passive_queues_freq              [25;2]
% 4.00/0.98  --inst_dismatching                      true
% 4.00/0.98  --inst_eager_unprocessed_to_passive     true
% 4.00/0.98  --inst_prop_sim_given                   true
% 4.00/0.98  --inst_prop_sim_new                     false
% 4.00/0.98  --inst_subs_new                         false
% 4.00/0.98  --inst_eq_res_simp                      false
% 4.00/0.98  --inst_subs_given                       false
% 4.00/0.98  --inst_orphan_elimination               true
% 4.00/0.98  --inst_learning_loop_flag               true
% 4.00/0.98  --inst_learning_start                   3000
% 4.00/0.98  --inst_learning_factor                  2
% 4.00/0.98  --inst_start_prop_sim_after_learn       3
% 4.00/0.98  --inst_sel_renew                        solver
% 4.00/0.98  --inst_lit_activity_flag                true
% 4.00/0.98  --inst_restr_to_given                   false
% 4.00/0.98  --inst_activity_threshold               500
% 4.00/0.98  --inst_out_proof                        true
% 4.00/0.98  
% 4.00/0.98  ------ Resolution Options
% 4.00/0.98  
% 4.00/0.98  --resolution_flag                       true
% 4.00/0.98  --res_lit_sel                           adaptive
% 4.00/0.98  --res_lit_sel_side                      none
% 4.00/0.98  --res_ordering                          kbo
% 4.00/0.98  --res_to_prop_solver                    active
% 4.00/0.98  --res_prop_simpl_new                    false
% 4.00/0.98  --res_prop_simpl_given                  true
% 4.00/0.98  --res_passive_queue_type                priority_queues
% 4.00/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.00/0.98  --res_passive_queues_freq               [15;5]
% 4.00/0.98  --res_forward_subs                      full
% 4.00/0.98  --res_backward_subs                     full
% 4.00/0.98  --res_forward_subs_resolution           true
% 4.00/0.98  --res_backward_subs_resolution          true
% 4.00/0.98  --res_orphan_elimination                true
% 4.00/0.98  --res_time_limit                        2.
% 4.00/0.98  --res_out_proof                         true
% 4.00/0.98  
% 4.00/0.98  ------ Superposition Options
% 4.00/0.98  
% 4.00/0.98  --superposition_flag                    true
% 4.00/0.98  --sup_passive_queue_type                priority_queues
% 4.00/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.00/0.98  --sup_passive_queues_freq               [8;1;4]
% 4.00/0.98  --demod_completeness_check              fast
% 4.00/0.98  --demod_use_ground                      true
% 4.00/0.98  --sup_to_prop_solver                    passive
% 4.00/0.98  --sup_prop_simpl_new                    true
% 4.00/0.98  --sup_prop_simpl_given                  true
% 4.00/0.98  --sup_fun_splitting                     false
% 4.00/0.98  --sup_smt_interval                      50000
% 4.00/0.98  
% 4.00/0.98  ------ Superposition Simplification Setup
% 4.00/0.98  
% 4.00/0.98  --sup_indices_passive                   []
% 4.00/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.00/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.00/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.00/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 4.00/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.00/0.98  --sup_full_bw                           [BwDemod]
% 4.00/0.98  --sup_immed_triv                        [TrivRules]
% 4.00/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.00/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.00/0.98  --sup_immed_bw_main                     []
% 4.00/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.00/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 4.00/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.00/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.00/0.98  
% 4.00/0.98  ------ Combination Options
% 4.00/0.98  
% 4.00/0.98  --comb_res_mult                         3
% 4.00/0.98  --comb_sup_mult                         2
% 4.00/0.98  --comb_inst_mult                        10
% 4.00/0.98  
% 4.00/0.98  ------ Debug Options
% 4.00/0.98  
% 4.00/0.98  --dbg_backtrace                         false
% 4.00/0.98  --dbg_dump_prop_clauses                 false
% 4.00/0.98  --dbg_dump_prop_clauses_file            -
% 4.00/0.98  --dbg_out_stat                          false
% 4.00/0.98  ------ Parsing...
% 4.00/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.00/0.98  
% 4.00/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 4.00/0.98  
% 4.00/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.00/0.98  
% 4.00/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.00/0.98  ------ Proving...
% 4.00/0.98  ------ Problem Properties 
% 4.00/0.98  
% 4.00/0.98  
% 4.00/0.98  clauses                                 33
% 4.00/0.98  conjectures                             5
% 4.00/0.98  EPR                                     3
% 4.00/0.98  Horn                                    28
% 4.00/0.98  unary                                   10
% 4.00/0.98  binary                                  5
% 4.00/0.98  lits                                    95
% 4.00/0.98  lits eq                                 24
% 4.00/0.98  fd_pure                                 0
% 4.00/0.98  fd_pseudo                               0
% 4.00/0.98  fd_cond                                 5
% 4.00/0.98  fd_pseudo_cond                          2
% 4.00/0.98  AC symbols                              0
% 4.00/0.98  
% 4.00/0.98  ------ Schedule dynamic 5 is on 
% 4.00/0.98  
% 4.00/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 4.00/0.98  
% 4.00/0.98  
% 4.00/0.98  ------ 
% 4.00/0.98  Current options:
% 4.00/0.98  ------ 
% 4.00/0.98  
% 4.00/0.98  ------ Input Options
% 4.00/0.98  
% 4.00/0.98  --out_options                           all
% 4.00/0.98  --tptp_safe_out                         true
% 4.00/0.98  --problem_path                          ""
% 4.00/0.98  --include_path                          ""
% 4.00/0.98  --clausifier                            res/vclausify_rel
% 4.00/0.98  --clausifier_options                    --mode clausify
% 4.00/0.98  --stdin                                 false
% 4.00/0.98  --stats_out                             all
% 4.00/0.98  
% 4.00/0.98  ------ General Options
% 4.00/0.98  
% 4.00/0.98  --fof                                   false
% 4.00/0.98  --time_out_real                         305.
% 4.00/0.98  --time_out_virtual                      -1.
% 4.00/0.98  --symbol_type_check                     false
% 4.00/0.98  --clausify_out                          false
% 4.00/0.98  --sig_cnt_out                           false
% 4.00/0.98  --trig_cnt_out                          false
% 4.00/0.98  --trig_cnt_out_tolerance                1.
% 4.00/0.98  --trig_cnt_out_sk_spl                   false
% 4.00/0.98  --abstr_cl_out                          false
% 4.00/0.98  
% 4.00/0.98  ------ Global Options
% 4.00/0.98  
% 4.00/0.98  --schedule                              default
% 4.00/0.98  --add_important_lit                     false
% 4.00/0.98  --prop_solver_per_cl                    1000
% 4.00/0.98  --min_unsat_core                        false
% 4.00/0.98  --soft_assumptions                      false
% 4.00/0.98  --soft_lemma_size                       3
% 4.00/0.98  --prop_impl_unit_size                   0
% 4.00/0.98  --prop_impl_unit                        []
% 4.00/0.98  --share_sel_clauses                     true
% 4.00/0.98  --reset_solvers                         false
% 4.00/0.98  --bc_imp_inh                            [conj_cone]
% 4.00/0.98  --conj_cone_tolerance                   3.
% 4.00/0.98  --extra_neg_conj                        none
% 4.00/0.98  --large_theory_mode                     true
% 4.00/0.98  --prolific_symb_bound                   200
% 4.00/0.98  --lt_threshold                          2000
% 4.00/0.98  --clause_weak_htbl                      true
% 4.00/0.98  --gc_record_bc_elim                     false
% 4.00/0.98  
% 4.00/0.98  ------ Preprocessing Options
% 4.00/0.98  
% 4.00/0.98  --preprocessing_flag                    true
% 4.00/0.98  --time_out_prep_mult                    0.1
% 4.00/0.98  --splitting_mode                        input
% 4.00/0.98  --splitting_grd                         true
% 4.00/0.98  --splitting_cvd                         false
% 4.00/0.98  --splitting_cvd_svl                     false
% 4.00/0.98  --splitting_nvd                         32
% 4.00/0.98  --sub_typing                            true
% 4.00/0.98  --prep_gs_sim                           true
% 4.00/0.98  --prep_unflatten                        true
% 4.00/0.98  --prep_res_sim                          true
% 4.00/0.98  --prep_upred                            true
% 4.00/0.98  --prep_sem_filter                       exhaustive
% 4.00/0.98  --prep_sem_filter_out                   false
% 4.00/0.98  --pred_elim                             true
% 4.00/0.98  --res_sim_input                         true
% 4.00/0.98  --eq_ax_congr_red                       true
% 4.00/0.98  --pure_diseq_elim                       true
% 4.00/0.98  --brand_transform                       false
% 4.00/0.98  --non_eq_to_eq                          false
% 4.00/0.98  --prep_def_merge                        true
% 4.00/0.98  --prep_def_merge_prop_impl              false
% 4.00/0.98  --prep_def_merge_mbd                    true
% 4.00/0.98  --prep_def_merge_tr_red                 false
% 4.00/0.98  --prep_def_merge_tr_cl                  false
% 4.00/0.98  --smt_preprocessing                     true
% 4.00/0.98  --smt_ac_axioms                         fast
% 4.00/0.98  --preprocessed_out                      false
% 4.00/0.98  --preprocessed_stats                    false
% 4.00/0.98  
% 4.00/0.98  ------ Abstraction refinement Options
% 4.00/0.98  
% 4.00/0.98  --abstr_ref                             []
% 4.00/0.98  --abstr_ref_prep                        false
% 4.00/0.98  --abstr_ref_until_sat                   false
% 4.00/0.98  --abstr_ref_sig_restrict                funpre
% 4.00/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 4.00/0.98  --abstr_ref_under                       []
% 4.00/0.98  
% 4.00/0.98  ------ SAT Options
% 4.00/0.98  
% 4.00/0.98  --sat_mode                              false
% 4.00/0.98  --sat_fm_restart_options                ""
% 4.00/0.98  --sat_gr_def                            false
% 4.00/0.98  --sat_epr_types                         true
% 4.00/0.98  --sat_non_cyclic_types                  false
% 4.00/0.98  --sat_finite_models                     false
% 4.00/0.98  --sat_fm_lemmas                         false
% 4.00/0.98  --sat_fm_prep                           false
% 4.00/0.98  --sat_fm_uc_incr                        true
% 4.00/0.98  --sat_out_model                         small
% 4.00/0.98  --sat_out_clauses                       false
% 4.00/0.98  
% 4.00/0.98  ------ QBF Options
% 4.00/0.98  
% 4.00/0.98  --qbf_mode                              false
% 4.00/0.98  --qbf_elim_univ                         false
% 4.00/0.98  --qbf_dom_inst                          none
% 4.00/0.98  --qbf_dom_pre_inst                      false
% 4.00/0.98  --qbf_sk_in                             false
% 4.00/0.98  --qbf_pred_elim                         true
% 4.00/0.98  --qbf_split                             512
% 4.00/0.98  
% 4.00/0.98  ------ BMC1 Options
% 4.00/0.98  
% 4.00/0.98  --bmc1_incremental                      false
% 4.00/0.98  --bmc1_axioms                           reachable_all
% 4.00/0.98  --bmc1_min_bound                        0
% 4.00/0.98  --bmc1_max_bound                        -1
% 4.00/0.98  --bmc1_max_bound_default                -1
% 4.00/0.98  --bmc1_symbol_reachability              true
% 4.00/0.98  --bmc1_property_lemmas                  false
% 4.00/0.98  --bmc1_k_induction                      false
% 4.00/0.98  --bmc1_non_equiv_states                 false
% 4.00/0.98  --bmc1_deadlock                         false
% 4.00/0.98  --bmc1_ucm                              false
% 4.00/0.98  --bmc1_add_unsat_core                   none
% 4.00/0.98  --bmc1_unsat_core_children              false
% 4.00/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 4.00/0.98  --bmc1_out_stat                         full
% 4.00/0.98  --bmc1_ground_init                      false
% 4.00/0.98  --bmc1_pre_inst_next_state              false
% 4.00/0.98  --bmc1_pre_inst_state                   false
% 4.00/0.98  --bmc1_pre_inst_reach_state             false
% 4.00/0.98  --bmc1_out_unsat_core                   false
% 4.00/0.98  --bmc1_aig_witness_out                  false
% 4.00/0.98  --bmc1_verbose                          false
% 4.00/0.98  --bmc1_dump_clauses_tptp                false
% 4.00/0.98  --bmc1_dump_unsat_core_tptp             false
% 4.00/0.98  --bmc1_dump_file                        -
% 4.00/0.98  --bmc1_ucm_expand_uc_limit              128
% 4.00/0.98  --bmc1_ucm_n_expand_iterations          6
% 4.00/0.98  --bmc1_ucm_extend_mode                  1
% 4.00/0.98  --bmc1_ucm_init_mode                    2
% 4.00/0.98  --bmc1_ucm_cone_mode                    none
% 4.00/0.98  --bmc1_ucm_reduced_relation_type        0
% 4.00/0.98  --bmc1_ucm_relax_model                  4
% 4.00/0.98  --bmc1_ucm_full_tr_after_sat            true
% 4.00/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 4.00/0.98  --bmc1_ucm_layered_model                none
% 4.00/0.98  --bmc1_ucm_max_lemma_size               10
% 4.00/0.98  
% 4.00/0.98  ------ AIG Options
% 4.00/0.98  
% 4.00/0.98  --aig_mode                              false
% 4.00/0.98  
% 4.00/0.98  ------ Instantiation Options
% 4.00/0.98  
% 4.00/0.98  --instantiation_flag                    true
% 4.00/0.98  --inst_sos_flag                         false
% 4.00/0.98  --inst_sos_phase                        true
% 4.00/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.00/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.00/0.98  --inst_lit_sel_side                     none
% 4.00/0.98  --inst_solver_per_active                1400
% 4.00/0.98  --inst_solver_calls_frac                1.
% 4.00/0.98  --inst_passive_queue_type               priority_queues
% 4.00/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.00/0.98  --inst_passive_queues_freq              [25;2]
% 4.00/0.98  --inst_dismatching                      true
% 4.00/0.98  --inst_eager_unprocessed_to_passive     true
% 4.00/0.98  --inst_prop_sim_given                   true
% 4.00/0.98  --inst_prop_sim_new                     false
% 4.00/0.98  --inst_subs_new                         false
% 4.00/0.98  --inst_eq_res_simp                      false
% 4.00/0.98  --inst_subs_given                       false
% 4.00/0.98  --inst_orphan_elimination               true
% 4.00/0.98  --inst_learning_loop_flag               true
% 4.00/0.98  --inst_learning_start                   3000
% 4.00/0.98  --inst_learning_factor                  2
% 4.00/0.98  --inst_start_prop_sim_after_learn       3
% 4.00/0.98  --inst_sel_renew                        solver
% 4.00/0.98  --inst_lit_activity_flag                true
% 4.00/0.98  --inst_restr_to_given                   false
% 4.00/0.98  --inst_activity_threshold               500
% 4.00/0.98  --inst_out_proof                        true
% 4.00/0.98  
% 4.00/0.98  ------ Resolution Options
% 4.00/0.98  
% 4.00/0.98  --resolution_flag                       false
% 4.00/0.98  --res_lit_sel                           adaptive
% 4.00/0.98  --res_lit_sel_side                      none
% 4.00/0.98  --res_ordering                          kbo
% 4.00/0.98  --res_to_prop_solver                    active
% 4.00/0.98  --res_prop_simpl_new                    false
% 4.00/0.98  --res_prop_simpl_given                  true
% 4.00/0.98  --res_passive_queue_type                priority_queues
% 4.00/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.00/0.98  --res_passive_queues_freq               [15;5]
% 4.00/0.98  --res_forward_subs                      full
% 4.00/0.98  --res_backward_subs                     full
% 4.00/0.98  --res_forward_subs_resolution           true
% 4.00/0.98  --res_backward_subs_resolution          true
% 4.00/0.98  --res_orphan_elimination                true
% 4.00/0.98  --res_time_limit                        2.
% 4.00/0.98  --res_out_proof                         true
% 4.00/0.98  
% 4.00/0.98  ------ Superposition Options
% 4.00/0.98  
% 4.00/0.98  --superposition_flag                    true
% 4.00/0.98  --sup_passive_queue_type                priority_queues
% 4.00/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.00/0.98  --sup_passive_queues_freq               [8;1;4]
% 4.00/0.98  --demod_completeness_check              fast
% 4.00/0.98  --demod_use_ground                      true
% 4.00/0.98  --sup_to_prop_solver                    passive
% 4.00/0.98  --sup_prop_simpl_new                    true
% 4.00/0.98  --sup_prop_simpl_given                  true
% 4.00/0.98  --sup_fun_splitting                     false
% 4.00/0.98  --sup_smt_interval                      50000
% 4.00/0.98  
% 4.00/0.98  ------ Superposition Simplification Setup
% 4.00/0.98  
% 4.00/0.98  --sup_indices_passive                   []
% 4.00/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.00/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.00/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.00/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 4.00/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.00/0.98  --sup_full_bw                           [BwDemod]
% 4.00/0.98  --sup_immed_triv                        [TrivRules]
% 4.00/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.00/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.00/0.98  --sup_immed_bw_main                     []
% 4.00/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.00/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 4.00/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.00/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.00/0.98  
% 4.00/0.98  ------ Combination Options
% 4.00/0.98  
% 4.00/0.98  --comb_res_mult                         3
% 4.00/0.98  --comb_sup_mult                         2
% 4.00/0.98  --comb_inst_mult                        10
% 4.00/0.98  
% 4.00/0.98  ------ Debug Options
% 4.00/0.98  
% 4.00/0.98  --dbg_backtrace                         false
% 4.00/0.98  --dbg_dump_prop_clauses                 false
% 4.00/0.98  --dbg_dump_prop_clauses_file            -
% 4.00/0.98  --dbg_out_stat                          false
% 4.00/0.98  
% 4.00/0.98  
% 4.00/0.98  
% 4.00/0.98  
% 4.00/0.98  ------ Proving...
% 4.00/0.98  
% 4.00/0.98  
% 4.00/0.98  % SZS status Theorem for theBenchmark.p
% 4.00/0.98  
% 4.00/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 4.00/0.98  
% 4.00/0.98  fof(f21,conjecture,(
% 4.00/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 4.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.98  
% 4.00/0.98  fof(f22,negated_conjecture,(
% 4.00/0.98    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 4.00/0.98    inference(negated_conjecture,[],[f21])).
% 4.00/0.98  
% 4.00/0.98  fof(f48,plain,(
% 4.00/0.98    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 4.00/0.98    inference(ennf_transformation,[],[f22])).
% 4.00/0.98  
% 4.00/0.98  fof(f49,plain,(
% 4.00/0.98    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 4.00/0.98    inference(flattening,[],[f48])).
% 4.00/0.98  
% 4.00/0.98  fof(f55,plain,(
% 4.00/0.98    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 4.00/0.98    introduced(choice_axiom,[])).
% 4.00/0.98  
% 4.00/0.98  fof(f56,plain,(
% 4.00/0.98    (~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 4.00/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f49,f55])).
% 4.00/0.98  
% 4.00/0.98  fof(f94,plain,(
% 4.00/0.98    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 4.00/0.98    inference(cnf_transformation,[],[f56])).
% 4.00/0.98  
% 4.00/0.98  fof(f14,axiom,(
% 4.00/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 4.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.98  
% 4.00/0.98  fof(f38,plain,(
% 4.00/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.00/0.98    inference(ennf_transformation,[],[f14])).
% 4.00/0.98  
% 4.00/0.98  fof(f39,plain,(
% 4.00/0.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.00/0.98    inference(flattening,[],[f38])).
% 4.00/0.98  
% 4.00/0.98  fof(f53,plain,(
% 4.00/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.00/0.98    inference(nnf_transformation,[],[f39])).
% 4.00/0.98  
% 4.00/0.98  fof(f75,plain,(
% 4.00/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.00/0.98    inference(cnf_transformation,[],[f53])).
% 4.00/0.98  
% 4.00/0.98  fof(f11,axiom,(
% 4.00/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 4.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.98  
% 4.00/0.98  fof(f33,plain,(
% 4.00/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.00/0.98    inference(ennf_transformation,[],[f11])).
% 4.00/0.98  
% 4.00/0.98  fof(f69,plain,(
% 4.00/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.00/0.98    inference(cnf_transformation,[],[f33])).
% 4.00/0.98  
% 4.00/0.98  fof(f92,plain,(
% 4.00/0.98    v1_funct_2(sK1,sK0,sK0)),
% 4.00/0.98    inference(cnf_transformation,[],[f56])).
% 4.00/0.98  
% 4.00/0.98  fof(f19,axiom,(
% 4.00/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 4.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.98  
% 4.00/0.98  fof(f46,plain,(
% 4.00/0.98    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 4.00/0.98    inference(ennf_transformation,[],[f19])).
% 4.00/0.98  
% 4.00/0.98  fof(f47,plain,(
% 4.00/0.98    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 4.00/0.98    inference(flattening,[],[f46])).
% 4.00/0.98  
% 4.00/0.98  fof(f89,plain,(
% 4.00/0.98    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 4.00/0.98    inference(cnf_transformation,[],[f47])).
% 4.00/0.98  
% 4.00/0.98  fof(f91,plain,(
% 4.00/0.98    v1_funct_1(sK1)),
% 4.00/0.98    inference(cnf_transformation,[],[f56])).
% 4.00/0.98  
% 4.00/0.98  fof(f93,plain,(
% 4.00/0.98    v3_funct_2(sK1,sK0,sK0)),
% 4.00/0.98    inference(cnf_transformation,[],[f56])).
% 4.00/0.98  
% 4.00/0.98  fof(f16,axiom,(
% 4.00/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 4.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.98  
% 4.00/0.98  fof(f42,plain,(
% 4.00/0.98    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 4.00/0.98    inference(ennf_transformation,[],[f16])).
% 4.00/0.98  
% 4.00/0.98  fof(f43,plain,(
% 4.00/0.98    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 4.00/0.98    inference(flattening,[],[f42])).
% 4.00/0.98  
% 4.00/0.98  fof(f86,plain,(
% 4.00/0.98    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 4.00/0.98    inference(cnf_transformation,[],[f43])).
% 4.00/0.98  
% 4.00/0.98  fof(f18,axiom,(
% 4.00/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 4.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.98  
% 4.00/0.98  fof(f44,plain,(
% 4.00/0.98    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 4.00/0.98    inference(ennf_transformation,[],[f18])).
% 4.00/0.98  
% 4.00/0.98  fof(f45,plain,(
% 4.00/0.98    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 4.00/0.98    inference(flattening,[],[f44])).
% 4.00/0.98  
% 4.00/0.98  fof(f88,plain,(
% 4.00/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 4.00/0.98    inference(cnf_transformation,[],[f45])).
% 4.00/0.98  
% 4.00/0.98  fof(f83,plain,(
% 4.00/0.98    ( ! [X0,X1] : (v1_funct_1(k2_funct_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 4.00/0.98    inference(cnf_transformation,[],[f43])).
% 4.00/0.98  
% 4.00/0.98  fof(f9,axiom,(
% 4.00/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 4.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.98  
% 4.00/0.98  fof(f31,plain,(
% 4.00/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.00/0.98    inference(ennf_transformation,[],[f9])).
% 4.00/0.98  
% 4.00/0.98  fof(f67,plain,(
% 4.00/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.00/0.98    inference(cnf_transformation,[],[f31])).
% 4.00/0.98  
% 4.00/0.98  fof(f7,axiom,(
% 4.00/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))))),
% 4.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.98  
% 4.00/0.98  fof(f29,plain,(
% 4.00/0.98    ! [X0] : (((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 4.00/0.98    inference(ennf_transformation,[],[f7])).
% 4.00/0.98  
% 4.00/0.98  fof(f30,plain,(
% 4.00/0.98    ! [X0] : ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.00/0.98    inference(flattening,[],[f29])).
% 4.00/0.98  
% 4.00/0.98  fof(f64,plain,(
% 4.00/0.98    ( ! [X0] : (k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.00/0.98    inference(cnf_transformation,[],[f30])).
% 4.00/0.98  
% 4.00/0.98  fof(f20,axiom,(
% 4.00/0.98    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 4.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.98  
% 4.00/0.98  fof(f90,plain,(
% 4.00/0.98    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 4.00/0.98    inference(cnf_transformation,[],[f20])).
% 4.00/0.98  
% 4.00/0.98  fof(f98,plain,(
% 4.00/0.98    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.00/0.98    inference(definition_unfolding,[],[f64,f90])).
% 4.00/0.98  
% 4.00/0.98  fof(f13,axiom,(
% 4.00/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 4.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.98  
% 4.00/0.98  fof(f36,plain,(
% 4.00/0.98    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.00/0.98    inference(ennf_transformation,[],[f13])).
% 4.00/0.98  
% 4.00/0.98  fof(f37,plain,(
% 4.00/0.98    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.00/0.98    inference(flattening,[],[f36])).
% 4.00/0.98  
% 4.00/0.98  fof(f73,plain,(
% 4.00/0.98    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.00/0.98    inference(cnf_transformation,[],[f37])).
% 4.00/0.98  
% 4.00/0.98  fof(f65,plain,(
% 4.00/0.98    ( ! [X0] : (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.00/0.98    inference(cnf_transformation,[],[f30])).
% 4.00/0.98  
% 4.00/0.98  fof(f97,plain,(
% 4.00/0.98    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.00/0.98    inference(definition_unfolding,[],[f65,f90])).
% 4.00/0.98  
% 4.00/0.98  fof(f74,plain,(
% 4.00/0.98    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.00/0.98    inference(cnf_transformation,[],[f37])).
% 4.00/0.98  
% 4.00/0.98  fof(f10,axiom,(
% 4.00/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 4.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.98  
% 4.00/0.98  fof(f25,plain,(
% 4.00/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 4.00/0.98    inference(pure_predicate_removal,[],[f10])).
% 4.00/0.98  
% 4.00/0.98  fof(f32,plain,(
% 4.00/0.98    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.00/0.98    inference(ennf_transformation,[],[f25])).
% 4.00/0.98  
% 4.00/0.98  fof(f68,plain,(
% 4.00/0.98    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.00/0.98    inference(cnf_transformation,[],[f32])).
% 4.00/0.98  
% 4.00/0.98  fof(f15,axiom,(
% 4.00/0.98    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 4.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.98  
% 4.00/0.98  fof(f40,plain,(
% 4.00/0.98    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 4.00/0.98    inference(ennf_transformation,[],[f15])).
% 4.00/0.98  
% 4.00/0.98  fof(f41,plain,(
% 4.00/0.98    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 4.00/0.98    inference(flattening,[],[f40])).
% 4.00/0.98  
% 4.00/0.98  fof(f54,plain,(
% 4.00/0.98    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 4.00/0.98    inference(nnf_transformation,[],[f41])).
% 4.00/0.98  
% 4.00/0.98  fof(f81,plain,(
% 4.00/0.98    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 4.00/0.98    inference(cnf_transformation,[],[f54])).
% 4.00/0.98  
% 4.00/0.98  fof(f95,plain,(
% 4.00/0.98    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))),
% 4.00/0.98    inference(cnf_transformation,[],[f56])).
% 4.00/0.98  
% 4.00/0.98  fof(f17,axiom,(
% 4.00/0.98    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 4.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.98  
% 4.00/0.98  fof(f24,plain,(
% 4.00/0.98    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 4.00/0.98    inference(pure_predicate_removal,[],[f17])).
% 4.00/0.98  
% 4.00/0.98  fof(f87,plain,(
% 4.00/0.98    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 4.00/0.98    inference(cnf_transformation,[],[f24])).
% 4.00/0.98  
% 4.00/0.98  fof(f12,axiom,(
% 4.00/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 4.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.98  
% 4.00/0.98  fof(f34,plain,(
% 4.00/0.98    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 4.00/0.98    inference(ennf_transformation,[],[f12])).
% 4.00/0.98  
% 4.00/0.98  fof(f35,plain,(
% 4.00/0.98    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.00/0.98    inference(flattening,[],[f34])).
% 4.00/0.98  
% 4.00/0.98  fof(f52,plain,(
% 4.00/0.98    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.00/0.98    inference(nnf_transformation,[],[f35])).
% 4.00/0.98  
% 4.00/0.98  fof(f71,plain,(
% 4.00/0.98    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.00/0.98    inference(cnf_transformation,[],[f52])).
% 4.00/0.98  
% 4.00/0.98  fof(f102,plain,(
% 4.00/0.98    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.00/0.98    inference(equality_resolution,[],[f71])).
% 4.00/0.98  
% 4.00/0.98  fof(f2,axiom,(
% 4.00/0.98    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 4.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.98  
% 4.00/0.98  fof(f50,plain,(
% 4.00/0.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 4.00/0.98    inference(nnf_transformation,[],[f2])).
% 4.00/0.98  
% 4.00/0.98  fof(f51,plain,(
% 4.00/0.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 4.00/0.98    inference(flattening,[],[f50])).
% 4.00/0.98  
% 4.00/0.98  fof(f59,plain,(
% 4.00/0.98    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 4.00/0.98    inference(cnf_transformation,[],[f51])).
% 4.00/0.98  
% 4.00/0.98  fof(f101,plain,(
% 4.00/0.98    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 4.00/0.98    inference(equality_resolution,[],[f59])).
% 4.00/0.98  
% 4.00/0.98  fof(f1,axiom,(
% 4.00/0.98    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 4.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.98  
% 4.00/0.98  fof(f27,plain,(
% 4.00/0.98    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 4.00/0.98    inference(ennf_transformation,[],[f1])).
% 4.00/0.98  
% 4.00/0.98  fof(f57,plain,(
% 4.00/0.98    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 4.00/0.98    inference(cnf_transformation,[],[f27])).
% 4.00/0.98  
% 4.00/0.98  fof(f4,axiom,(
% 4.00/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 4.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.98  
% 4.00/0.98  fof(f23,plain,(
% 4.00/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 4.00/0.98    inference(unused_predicate_definition_removal,[],[f4])).
% 4.00/0.98  
% 4.00/0.98  fof(f28,plain,(
% 4.00/0.98    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 4.00/0.98    inference(ennf_transformation,[],[f23])).
% 4.00/0.98  
% 4.00/0.98  fof(f62,plain,(
% 4.00/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 4.00/0.98    inference(cnf_transformation,[],[f28])).
% 4.00/0.98  
% 4.00/0.98  fof(f6,axiom,(
% 4.00/0.98    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 4.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.98  
% 4.00/0.98  fof(f63,plain,(
% 4.00/0.98    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 4.00/0.98    inference(cnf_transformation,[],[f6])).
% 4.00/0.98  
% 4.00/0.98  fof(f96,plain,(
% 4.00/0.98    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 4.00/0.98    inference(definition_unfolding,[],[f63,f90])).
% 4.00/0.98  
% 4.00/0.98  fof(f8,axiom,(
% 4.00/0.98    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))),
% 4.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.98  
% 4.00/0.98  fof(f66,plain,(
% 4.00/0.98    ( ! [X0] : (k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))) )),
% 4.00/0.98    inference(cnf_transformation,[],[f8])).
% 4.00/0.98  
% 4.00/0.98  fof(f99,plain,(
% 4.00/0.98    ( ! [X0] : (k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0)) )),
% 4.00/0.98    inference(definition_unfolding,[],[f66,f90,f90])).
% 4.00/0.98  
% 4.00/0.98  fof(f3,axiom,(
% 4.00/0.98    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 4.00/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.98  
% 4.00/0.98  fof(f61,plain,(
% 4.00/0.98    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 4.00/0.98    inference(cnf_transformation,[],[f3])).
% 4.00/0.98  
% 4.00/0.98  cnf(c_34,negated_conjecture,
% 4.00/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 4.00/0.98      inference(cnf_transformation,[],[f94]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_1339,plain,
% 4.00/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_23,plain,
% 4.00/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 4.00/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.00/0.98      | k1_relset_1(X1,X2,X0) = X1
% 4.00/0.98      | k1_xboole_0 = X2 ),
% 4.00/0.98      inference(cnf_transformation,[],[f75]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_1348,plain,
% 4.00/0.98      ( k1_relset_1(X0,X1,X2) = X0
% 4.00/0.98      | k1_xboole_0 = X1
% 4.00/0.98      | v1_funct_2(X2,X0,X1) != iProver_top
% 4.00/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_4302,plain,
% 4.00/0.98      ( k1_relset_1(sK0,sK0,sK1) = sK0
% 4.00/0.98      | sK0 = k1_xboole_0
% 4.00/0.98      | v1_funct_2(sK1,sK0,sK0) != iProver_top ),
% 4.00/0.98      inference(superposition,[status(thm)],[c_1339,c_1348]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_12,plain,
% 4.00/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.00/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 4.00/0.98      inference(cnf_transformation,[],[f69]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_1357,plain,
% 4.00/0.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 4.00/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_2537,plain,
% 4.00/0.98      ( k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
% 4.00/0.98      inference(superposition,[status(thm)],[c_1339,c_1357]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_4312,plain,
% 4.00/0.98      ( k1_relat_1(sK1) = sK0
% 4.00/0.98      | sK0 = k1_xboole_0
% 4.00/0.98      | v1_funct_2(sK1,sK0,sK0) != iProver_top ),
% 4.00/0.98      inference(demodulation,[status(thm)],[c_4302,c_2537]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_36,negated_conjecture,
% 4.00/0.98      ( v1_funct_2(sK1,sK0,sK0) ),
% 4.00/0.98      inference(cnf_transformation,[],[f92]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_39,plain,
% 4.00/0.98      ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_4573,plain,
% 4.00/0.98      ( sK0 = k1_xboole_0 | k1_relat_1(sK1) = sK0 ),
% 4.00/0.98      inference(global_propositional_subsumption,
% 4.00/0.98                [status(thm)],
% 4.00/0.98                [c_4312,c_39]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_4574,plain,
% 4.00/0.98      ( k1_relat_1(sK1) = sK0 | sK0 = k1_xboole_0 ),
% 4.00/0.98      inference(renaming,[status(thm)],[c_4573]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_32,plain,
% 4.00/0.98      ( ~ v1_funct_2(X0,X1,X1)
% 4.00/0.98      | ~ v3_funct_2(X0,X1,X1)
% 4.00/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 4.00/0.98      | ~ v1_funct_1(X0)
% 4.00/0.98      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 4.00/0.98      inference(cnf_transformation,[],[f89]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_1341,plain,
% 4.00/0.98      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
% 4.00/0.98      | v1_funct_2(X1,X0,X0) != iProver_top
% 4.00/0.98      | v3_funct_2(X1,X0,X0) != iProver_top
% 4.00/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 4.00/0.98      | v1_funct_1(X1) != iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_6564,plain,
% 4.00/0.98      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
% 4.00/0.98      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 4.00/0.98      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 4.00/0.98      | v1_funct_1(sK1) != iProver_top ),
% 4.00/0.98      inference(superposition,[status(thm)],[c_1339,c_1341]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_37,negated_conjecture,
% 4.00/0.98      ( v1_funct_1(sK1) ),
% 4.00/0.98      inference(cnf_transformation,[],[f91]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_35,negated_conjecture,
% 4.00/0.98      ( v3_funct_2(sK1,sK0,sK0) ),
% 4.00/0.98      inference(cnf_transformation,[],[f93]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_1713,plain,
% 4.00/0.98      ( ~ v1_funct_2(sK1,X0,X0)
% 4.00/0.98      | ~ v3_funct_2(sK1,X0,X0)
% 4.00/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 4.00/0.98      | ~ v1_funct_1(sK1)
% 4.00/0.98      | k2_funct_2(X0,sK1) = k2_funct_1(sK1) ),
% 4.00/0.98      inference(instantiation,[status(thm)],[c_32]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_1849,plain,
% 4.00/0.98      ( ~ v1_funct_2(sK1,sK0,sK0)
% 4.00/0.98      | ~ v3_funct_2(sK1,sK0,sK0)
% 4.00/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 4.00/0.98      | ~ v1_funct_1(sK1)
% 4.00/0.98      | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 4.00/0.98      inference(instantiation,[status(thm)],[c_1713]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_6756,plain,
% 4.00/0.98      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 4.00/0.98      inference(global_propositional_subsumption,
% 4.00/0.98                [status(thm)],
% 4.00/0.98                [c_6564,c_37,c_36,c_35,c_34,c_1849]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_26,plain,
% 4.00/0.98      ( ~ v1_funct_2(X0,X1,X1)
% 4.00/0.98      | ~ v3_funct_2(X0,X1,X1)
% 4.00/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 4.00/0.98      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 4.00/0.98      | ~ v1_funct_1(X0) ),
% 4.00/0.98      inference(cnf_transformation,[],[f86]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_1347,plain,
% 4.00/0.98      ( v1_funct_2(X0,X1,X1) != iProver_top
% 4.00/0.98      | v3_funct_2(X0,X1,X1) != iProver_top
% 4.00/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 4.00/0.98      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) = iProver_top
% 4.00/0.98      | v1_funct_1(X0) != iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_6777,plain,
% 4.00/0.98      ( v1_funct_2(sK1,sK0,sK0) != iProver_top
% 4.00/0.98      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 4.00/0.98      | m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 4.00/0.98      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 4.00/0.98      | v1_funct_1(sK1) != iProver_top ),
% 4.00/0.98      inference(superposition,[status(thm)],[c_6756,c_1347]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_38,plain,
% 4.00/0.98      ( v1_funct_1(sK1) = iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_40,plain,
% 4.00/0.98      ( v3_funct_2(sK1,sK0,sK0) = iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_41,plain,
% 4.00/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_7394,plain,
% 4.00/0.98      ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 4.00/0.98      inference(global_propositional_subsumption,
% 4.00/0.98                [status(thm)],
% 4.00/0.98                [c_6777,c_38,c_39,c_40,c_41]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_31,plain,
% 4.00/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.00/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 4.00/0.98      | ~ v1_funct_1(X0)
% 4.00/0.98      | ~ v1_funct_1(X3)
% 4.00/0.98      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 4.00/0.98      inference(cnf_transformation,[],[f88]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_1342,plain,
% 4.00/0.98      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 4.00/0.98      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 4.00/0.98      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 4.00/0.98      | v1_funct_1(X5) != iProver_top
% 4.00/0.98      | v1_funct_1(X4) != iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_9657,plain,
% 4.00/0.98      ( k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1))
% 4.00/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 4.00/0.98      | v1_funct_1(X2) != iProver_top
% 4.00/0.98      | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
% 4.00/0.98      inference(superposition,[status(thm)],[c_7394,c_1342]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_29,plain,
% 4.00/0.98      ( ~ v1_funct_2(X0,X1,X1)
% 4.00/0.98      | ~ v3_funct_2(X0,X1,X1)
% 4.00/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 4.00/0.98      | ~ v1_funct_1(X0)
% 4.00/0.98      | v1_funct_1(k2_funct_2(X1,X0)) ),
% 4.00/0.98      inference(cnf_transformation,[],[f83]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_1344,plain,
% 4.00/0.98      ( v1_funct_2(X0,X1,X1) != iProver_top
% 4.00/0.98      | v3_funct_2(X0,X1,X1) != iProver_top
% 4.00/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 4.00/0.98      | v1_funct_1(X0) != iProver_top
% 4.00/0.98      | v1_funct_1(k2_funct_2(X1,X0)) = iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_3020,plain,
% 4.00/0.98      ( v1_funct_2(sK1,sK0,sK0) != iProver_top
% 4.00/0.98      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 4.00/0.98      | v1_funct_1(k2_funct_2(sK0,sK1)) = iProver_top
% 4.00/0.98      | v1_funct_1(sK1) != iProver_top ),
% 4.00/0.98      inference(superposition,[status(thm)],[c_1339,c_1344]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_1693,plain,
% 4.00/0.98      ( ~ v1_funct_2(sK1,X0,X0)
% 4.00/0.98      | ~ v3_funct_2(sK1,X0,X0)
% 4.00/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 4.00/0.98      | v1_funct_1(k2_funct_2(X0,sK1))
% 4.00/0.98      | ~ v1_funct_1(sK1) ),
% 4.00/0.98      inference(instantiation,[status(thm)],[c_29]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_1838,plain,
% 4.00/0.98      ( ~ v1_funct_2(sK1,sK0,sK0)
% 4.00/0.98      | ~ v3_funct_2(sK1,sK0,sK0)
% 4.00/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 4.00/0.98      | v1_funct_1(k2_funct_2(sK0,sK1))
% 4.00/0.98      | ~ v1_funct_1(sK1) ),
% 4.00/0.98      inference(instantiation,[status(thm)],[c_1693]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_1839,plain,
% 4.00/0.98      ( v1_funct_2(sK1,sK0,sK0) != iProver_top
% 4.00/0.98      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 4.00/0.98      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 4.00/0.98      | v1_funct_1(k2_funct_2(sK0,sK1)) = iProver_top
% 4.00/0.98      | v1_funct_1(sK1) != iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_1838]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_3262,plain,
% 4.00/0.98      ( v1_funct_1(k2_funct_2(sK0,sK1)) = iProver_top ),
% 4.00/0.98      inference(global_propositional_subsumption,
% 4.00/0.98                [status(thm)],
% 4.00/0.98                [c_3020,c_38,c_39,c_40,c_41,c_1839]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_6761,plain,
% 4.00/0.98      ( v1_funct_1(k2_funct_1(sK1)) = iProver_top ),
% 4.00/0.98      inference(demodulation,[status(thm)],[c_6756,c_3262]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_13666,plain,
% 4.00/0.98      ( v1_funct_1(X2) != iProver_top
% 4.00/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 4.00/0.98      | k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1)) ),
% 4.00/0.98      inference(global_propositional_subsumption,
% 4.00/0.98                [status(thm)],
% 4.00/0.98                [c_9657,c_6761]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_13667,plain,
% 4.00/0.98      ( k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1))
% 4.00/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 4.00/0.98      | v1_funct_1(X2) != iProver_top ),
% 4.00/0.98      inference(renaming,[status(thm)],[c_13666]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_13678,plain,
% 4.00/0.98      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k5_relat_1(sK1,k2_funct_1(sK1))
% 4.00/0.98      | v1_funct_1(sK1) != iProver_top ),
% 4.00/0.98      inference(superposition,[status(thm)],[c_1339,c_13667]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_10,plain,
% 4.00/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.00/0.98      | v1_relat_1(X0) ),
% 4.00/0.98      inference(cnf_transformation,[],[f67]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_1358,plain,
% 4.00/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 4.00/0.98      | v1_relat_1(X0) = iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_1997,plain,
% 4.00/0.98      ( v1_relat_1(sK1) = iProver_top ),
% 4.00/0.98      inference(superposition,[status(thm)],[c_1339,c_1358]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_8,plain,
% 4.00/0.98      ( ~ v1_relat_1(X0)
% 4.00/0.98      | ~ v1_funct_1(X0)
% 4.00/0.98      | ~ v2_funct_1(X0)
% 4.00/0.98      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
% 4.00/0.98      inference(cnf_transformation,[],[f98]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_1359,plain,
% 4.00/0.98      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
% 4.00/0.98      | v1_relat_1(X0) != iProver_top
% 4.00/0.98      | v1_funct_1(X0) != iProver_top
% 4.00/0.98      | v2_funct_1(X0) != iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_3235,plain,
% 4.00/0.98      ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
% 4.00/0.98      | v1_funct_1(sK1) != iProver_top
% 4.00/0.98      | v2_funct_1(sK1) != iProver_top ),
% 4.00/0.98      inference(superposition,[status(thm)],[c_1997,c_1359]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_1629,plain,
% 4.00/0.98      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 4.00/0.98      | v1_relat_1(sK1) ),
% 4.00/0.98      inference(instantiation,[status(thm)],[c_10]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_1740,plain,
% 4.00/0.98      ( ~ v1_relat_1(sK1)
% 4.00/0.98      | ~ v1_funct_1(sK1)
% 4.00/0.98      | ~ v2_funct_1(sK1)
% 4.00/0.98      | k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
% 4.00/0.98      inference(instantiation,[status(thm)],[c_8]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_16,plain,
% 4.00/0.98      ( ~ v3_funct_2(X0,X1,X2)
% 4.00/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.00/0.98      | ~ v1_funct_1(X0)
% 4.00/0.98      | v2_funct_1(X0) ),
% 4.00/0.98      inference(cnf_transformation,[],[f73]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_1669,plain,
% 4.00/0.98      ( ~ v3_funct_2(sK1,X0,X1)
% 4.00/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 4.00/0.98      | ~ v1_funct_1(sK1)
% 4.00/0.98      | v2_funct_1(sK1) ),
% 4.00/0.98      inference(instantiation,[status(thm)],[c_16]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_1780,plain,
% 4.00/0.98      ( ~ v3_funct_2(sK1,sK0,sK0)
% 4.00/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 4.00/0.98      | ~ v1_funct_1(sK1)
% 4.00/0.98      | v2_funct_1(sK1) ),
% 4.00/0.98      inference(instantiation,[status(thm)],[c_1669]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_3431,plain,
% 4.00/0.98      ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
% 4.00/0.98      inference(global_propositional_subsumption,
% 4.00/0.98                [status(thm)],
% 4.00/0.98                [c_3235,c_37,c_35,c_34,c_1629,c_1740,c_1780]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_13700,plain,
% 4.00/0.98      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
% 4.00/0.98      | v1_funct_1(sK1) != iProver_top ),
% 4.00/0.98      inference(light_normalisation,[status(thm)],[c_13678,c_3431]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_13739,plain,
% 4.00/0.98      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
% 4.00/0.98      inference(global_propositional_subsumption,
% 4.00/0.98                [status(thm)],
% 4.00/0.98                [c_13700,c_38]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_9656,plain,
% 4.00/0.98      ( k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1)
% 4.00/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 4.00/0.98      | v1_funct_1(X2) != iProver_top
% 4.00/0.98      | v1_funct_1(sK1) != iProver_top ),
% 4.00/0.98      inference(superposition,[status(thm)],[c_1339,c_1342]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_10139,plain,
% 4.00/0.98      ( v1_funct_1(X2) != iProver_top
% 4.00/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 4.00/0.98      | k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1) ),
% 4.00/0.98      inference(global_propositional_subsumption,
% 4.00/0.98                [status(thm)],
% 4.00/0.98                [c_9656,c_38]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_10140,plain,
% 4.00/0.98      ( k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1)
% 4.00/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 4.00/0.98      | v1_funct_1(X2) != iProver_top ),
% 4.00/0.98      inference(renaming,[status(thm)],[c_10139]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_10149,plain,
% 4.00/0.98      ( k1_partfun1(X0,X0,sK0,sK0,k2_funct_2(X0,X1),sK1) = k5_relat_1(k2_funct_2(X0,X1),sK1)
% 4.00/0.98      | v1_funct_2(X1,X0,X0) != iProver_top
% 4.00/0.98      | v3_funct_2(X1,X0,X0) != iProver_top
% 4.00/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 4.00/0.98      | v1_funct_1(X1) != iProver_top
% 4.00/0.98      | v1_funct_1(k2_funct_2(X0,X1)) != iProver_top ),
% 4.00/0.98      inference(superposition,[status(thm)],[c_1347,c_10140]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_11225,plain,
% 4.00/0.98      ( k1_partfun1(X0,X0,sK0,sK0,k2_funct_2(X0,X1),sK1) = k5_relat_1(k2_funct_2(X0,X1),sK1)
% 4.00/0.98      | v1_funct_2(X1,X0,X0) != iProver_top
% 4.00/0.98      | v3_funct_2(X1,X0,X0) != iProver_top
% 4.00/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 4.00/0.98      | v1_funct_1(X1) != iProver_top ),
% 4.00/0.98      inference(forward_subsumption_resolution,
% 4.00/0.98                [status(thm)],
% 4.00/0.98                [c_10149,c_1344]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_11232,plain,
% 4.00/0.98      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1) = k5_relat_1(k2_funct_2(sK0,sK1),sK1)
% 4.00/0.98      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 4.00/0.98      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 4.00/0.98      | v1_funct_1(sK1) != iProver_top ),
% 4.00/0.98      inference(superposition,[status(thm)],[c_1339,c_11225]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_7,plain,
% 4.00/0.98      ( ~ v1_relat_1(X0)
% 4.00/0.98      | ~ v1_funct_1(X0)
% 4.00/0.98      | ~ v2_funct_1(X0)
% 4.00/0.98      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
% 4.00/0.98      inference(cnf_transformation,[],[f97]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_1360,plain,
% 4.00/0.98      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
% 4.00/0.98      | v1_relat_1(X0) != iProver_top
% 4.00/0.98      | v1_funct_1(X0) != iProver_top
% 4.00/0.98      | v2_funct_1(X0) != iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_3887,plain,
% 4.00/0.98      ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1))
% 4.00/0.98      | v1_funct_1(sK1) != iProver_top
% 4.00/0.98      | v2_funct_1(sK1) != iProver_top ),
% 4.00/0.98      inference(superposition,[status(thm)],[c_1997,c_1360]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_15,plain,
% 4.00/0.98      ( ~ v3_funct_2(X0,X1,X2)
% 4.00/0.98      | v2_funct_2(X0,X2)
% 4.00/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.00/0.98      | ~ v1_funct_1(X0) ),
% 4.00/0.98      inference(cnf_transformation,[],[f74]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_11,plain,
% 4.00/0.98      ( v5_relat_1(X0,X1)
% 4.00/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 4.00/0.98      inference(cnf_transformation,[],[f68]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_25,plain,
% 4.00/0.98      ( ~ v2_funct_2(X0,X1)
% 4.00/0.98      | ~ v5_relat_1(X0,X1)
% 4.00/0.98      | ~ v1_relat_1(X0)
% 4.00/0.98      | k2_relat_1(X0) = X1 ),
% 4.00/0.98      inference(cnf_transformation,[],[f81]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_395,plain,
% 4.00/0.98      ( ~ v2_funct_2(X0,X1)
% 4.00/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 4.00/0.98      | ~ v1_relat_1(X0)
% 4.00/0.98      | k2_relat_1(X0) = X1 ),
% 4.00/0.98      inference(resolution,[status(thm)],[c_11,c_25]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_407,plain,
% 4.00/0.98      ( ~ v2_funct_2(X0,X1)
% 4.00/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 4.00/0.98      | k2_relat_1(X0) = X1 ),
% 4.00/0.98      inference(forward_subsumption_resolution,
% 4.00/0.98                [status(thm)],
% 4.00/0.98                [c_395,c_10]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_480,plain,
% 4.00/0.98      ( ~ v3_funct_2(X0,X1,X2)
% 4.00/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.00/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 4.00/0.98      | ~ v1_funct_1(X0)
% 4.00/0.98      | X3 != X0
% 4.00/0.98      | X5 != X2
% 4.00/0.98      | k2_relat_1(X3) = X5 ),
% 4.00/0.98      inference(resolution_lifted,[status(thm)],[c_15,c_407]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_481,plain,
% 4.00/0.98      ( ~ v3_funct_2(X0,X1,X2)
% 4.00/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.00/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 4.00/0.98      | ~ v1_funct_1(X0)
% 4.00/0.98      | k2_relat_1(X0) = X2 ),
% 4.00/0.98      inference(unflattening,[status(thm)],[c_480]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_1334,plain,
% 4.00/0.98      ( k2_relat_1(X0) = X1
% 4.00/0.98      | v3_funct_2(X0,X2,X1) != iProver_top
% 4.00/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 4.00/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
% 4.00/0.98      | v1_funct_1(X0) != iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_481]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_2169,plain,
% 4.00/0.98      ( k2_relat_1(sK1) = sK0
% 4.00/0.98      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 4.00/0.98      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 4.00/0.98      | v1_funct_1(sK1) != iProver_top ),
% 4.00/0.98      inference(superposition,[status(thm)],[c_1339,c_1334]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_1698,plain,
% 4.00/0.98      ( ~ v3_funct_2(sK1,X0,X1)
% 4.00/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 4.00/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 4.00/0.98      | ~ v1_funct_1(sK1)
% 4.00/0.98      | k2_relat_1(sK1) = X1 ),
% 4.00/0.98      inference(instantiation,[status(thm)],[c_481]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_1844,plain,
% 4.00/0.98      ( ~ v3_funct_2(sK1,sK0,sK0)
% 4.00/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
% 4.00/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 4.00/0.98      | ~ v1_funct_1(sK1)
% 4.00/0.98      | k2_relat_1(sK1) = sK0 ),
% 4.00/0.98      inference(instantiation,[status(thm)],[c_1698]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_1972,plain,
% 4.00/0.98      ( ~ v3_funct_2(sK1,sK0,sK0)
% 4.00/0.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 4.00/0.98      | ~ v1_funct_1(sK1)
% 4.00/0.98      | k2_relat_1(sK1) = sK0 ),
% 4.00/0.98      inference(instantiation,[status(thm)],[c_1844]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_2693,plain,
% 4.00/0.98      ( k2_relat_1(sK1) = sK0 ),
% 4.00/0.98      inference(global_propositional_subsumption,
% 4.00/0.98                [status(thm)],
% 4.00/0.98                [c_2169,c_37,c_35,c_34,c_1972]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_3891,plain,
% 4.00/0.98      ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
% 4.00/0.98      | v1_funct_1(sK1) != iProver_top
% 4.00/0.98      | v2_funct_1(sK1) != iProver_top ),
% 4.00/0.98      inference(light_normalisation,[status(thm)],[c_3887,c_2693]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_1781,plain,
% 4.00/0.98      ( v3_funct_2(sK1,sK0,sK0) != iProver_top
% 4.00/0.98      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 4.00/0.98      | v1_funct_1(sK1) != iProver_top
% 4.00/0.98      | v2_funct_1(sK1) = iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_1780]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_3915,plain,
% 4.00/0.98      ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(sK0) ),
% 4.00/0.98      inference(global_propositional_subsumption,
% 4.00/0.98                [status(thm)],
% 4.00/0.98                [c_3891,c_38,c_40,c_41,c_1781]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_11258,plain,
% 4.00/0.98      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
% 4.00/0.98      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 4.00/0.98      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 4.00/0.98      | v1_funct_1(sK1) != iProver_top ),
% 4.00/0.98      inference(light_normalisation,
% 4.00/0.98                [status(thm)],
% 4.00/0.98                [c_11232,c_3915,c_6756]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_10152,plain,
% 4.00/0.98      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k5_relat_1(k2_funct_1(sK1),sK1)
% 4.00/0.98      | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
% 4.00/0.98      inference(superposition,[status(thm)],[c_7394,c_10140]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_10169,plain,
% 4.00/0.98      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
% 4.00/0.98      | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
% 4.00/0.98      inference(light_normalisation,[status(thm)],[c_10152,c_3915]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_11371,plain,
% 4.00/0.98      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0) ),
% 4.00/0.98      inference(global_propositional_subsumption,
% 4.00/0.98                [status(thm)],
% 4.00/0.98                [c_11258,c_6761,c_10169]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_33,negated_conjecture,
% 4.00/0.98      ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
% 4.00/0.98      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
% 4.00/0.98      inference(cnf_transformation,[],[f95]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_1340,plain,
% 4.00/0.98      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) != iProver_top
% 4.00/0.98      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) != iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_6762,plain,
% 4.00/0.98      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) != iProver_top
% 4.00/0.98      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
% 4.00/0.98      inference(demodulation,[status(thm)],[c_6756,c_1340]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_11374,plain,
% 4.00/0.98      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top
% 4.00/0.98      | r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
% 4.00/0.98      inference(demodulation,[status(thm)],[c_11371,c_6762]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_30,plain,
% 4.00/0.98      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 4.00/0.98      inference(cnf_transformation,[],[f87]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_1343,plain,
% 4.00/0.98      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_13,plain,
% 4.00/0.98      ( r2_relset_1(X0,X1,X2,X2)
% 4.00/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 4.00/0.98      inference(cnf_transformation,[],[f102]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_1356,plain,
% 4.00/0.98      ( r2_relset_1(X0,X1,X2,X2) = iProver_top
% 4.00/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_2369,plain,
% 4.00/0.98      ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0)) = iProver_top ),
% 4.00/0.98      inference(superposition,[status(thm)],[c_1343,c_1356]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_11379,plain,
% 4.00/0.98      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
% 4.00/0.98      inference(forward_subsumption_resolution,
% 4.00/0.98                [status(thm)],
% 4.00/0.98                [c_11374,c_2369]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_13742,plain,
% 4.00/0.98      ( r2_relset_1(sK0,sK0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
% 4.00/0.98      inference(demodulation,[status(thm)],[c_13739,c_11379]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_13993,plain,
% 4.00/0.98      ( sK0 = k1_xboole_0
% 4.00/0.98      | r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
% 4.00/0.98      inference(superposition,[status(thm)],[c_4574,c_13742]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_13998,plain,
% 4.00/0.98      ( sK0 = k1_xboole_0 ),
% 4.00/0.98      inference(forward_subsumption_resolution,
% 4.00/0.98                [status(thm)],
% 4.00/0.98                [c_13993,c_2369]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_14047,plain,
% 4.00/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 4.00/0.98      inference(demodulation,[status(thm)],[c_13998,c_1339]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_2,plain,
% 4.00/0.98      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 4.00/0.98      inference(cnf_transformation,[],[f101]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_14055,plain,
% 4.00/0.98      ( m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 4.00/0.98      inference(demodulation,[status(thm)],[c_14047,c_2]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_0,plain,
% 4.00/0.98      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 4.00/0.98      inference(cnf_transformation,[],[f57]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_5,plain,
% 4.00/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 4.00/0.98      inference(cnf_transformation,[],[f62]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_380,plain,
% 4.00/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.00/0.98      | X0 != X2
% 4.00/0.98      | k1_xboole_0 != X1
% 4.00/0.98      | k1_xboole_0 = X2 ),
% 4.00/0.98      inference(resolution_lifted,[status(thm)],[c_0,c_5]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_381,plain,
% 4.00/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0 ),
% 4.00/0.98      inference(unflattening,[status(thm)],[c_380]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_1335,plain,
% 4.00/0.98      ( k1_xboole_0 = X0
% 4.00/0.98      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_381]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_15494,plain,
% 4.00/0.98      ( sK1 = k1_xboole_0 ),
% 4.00/0.98      inference(superposition,[status(thm)],[c_14055,c_1335]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_13999,plain,
% 4.00/0.98      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(k1_xboole_0)) != iProver_top ),
% 4.00/0.98      inference(demodulation,[status(thm)],[c_13998,c_13742]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_6,plain,
% 4.00/0.98      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 4.00/0.98      inference(cnf_transformation,[],[f96]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_14262,plain,
% 4.00/0.98      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_relat_1(sK1)),k1_xboole_0) != iProver_top ),
% 4.00/0.98      inference(light_normalisation,[status(thm)],[c_13999,c_6]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_17362,plain,
% 4.00/0.98      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_relat_1(k1_xboole_0)),k1_xboole_0) != iProver_top ),
% 4.00/0.98      inference(demodulation,[status(thm)],[c_15494,c_14262]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_14043,plain,
% 4.00/0.98      ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k1_xboole_0) ),
% 4.00/0.98      inference(demodulation,[status(thm)],[c_13998,c_3915]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_14064,plain,
% 4.00/0.98      ( k5_relat_1(k2_funct_1(sK1),sK1) = k1_xboole_0 ),
% 4.00/0.98      inference(light_normalisation,[status(thm)],[c_14043,c_6]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_17370,plain,
% 4.00/0.98      ( k5_relat_1(k2_funct_1(k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
% 4.00/0.98      inference(demodulation,[status(thm)],[c_15494,c_14064]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_9,plain,
% 4.00/0.98      ( k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
% 4.00/0.98      inference(cnf_transformation,[],[f99]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_1752,plain,
% 4.00/0.98      ( k2_funct_1(k1_xboole_0) = k6_partfun1(k1_xboole_0) ),
% 4.00/0.98      inference(superposition,[status(thm)],[c_6,c_9]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_1753,plain,
% 4.00/0.98      ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
% 4.00/0.98      inference(light_normalisation,[status(thm)],[c_1752,c_6]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_17405,plain,
% 4.00/0.98      ( k5_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 4.00/0.98      inference(light_normalisation,[status(thm)],[c_17370,c_1753]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_17379,plain,
% 4.00/0.98      ( k5_relat_1(k1_xboole_0,k2_funct_1(k1_xboole_0)) = k6_partfun1(k1_relat_1(k1_xboole_0)) ),
% 4.00/0.98      inference(demodulation,[status(thm)],[c_15494,c_3431]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_17385,plain,
% 4.00/0.98      ( k5_relat_1(k1_xboole_0,k1_xboole_0) = k6_partfun1(k1_relat_1(k1_xboole_0)) ),
% 4.00/0.98      inference(light_normalisation,[status(thm)],[c_17379,c_1753]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_17406,plain,
% 4.00/0.98      ( k6_partfun1(k1_relat_1(k1_xboole_0)) = k1_xboole_0 ),
% 4.00/0.98      inference(demodulation,[status(thm)],[c_17405,c_17385]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_17428,plain,
% 4.00/0.98      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 4.00/0.98      inference(light_normalisation,[status(thm)],[c_17362,c_17406]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_4,plain,
% 4.00/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 4.00/0.98      inference(cnf_transformation,[],[f61]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_1617,plain,
% 4.00/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 4.00/0.98      inference(instantiation,[status(thm)],[c_4]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_1620,plain,
% 4.00/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_1617]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_1622,plain,
% 4.00/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 4.00/0.98      inference(instantiation,[status(thm)],[c_1620]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_98,plain,
% 4.00/0.98      ( r2_relset_1(X0,X1,X2,X2) = iProver_top
% 4.00/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 4.00/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(c_100,plain,
% 4.00/0.98      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top
% 4.00/0.98      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 4.00/0.98      inference(instantiation,[status(thm)],[c_98]) ).
% 4.00/0.98  
% 4.00/0.98  cnf(contradiction,plain,
% 4.00/0.98      ( $false ),
% 4.00/0.98      inference(minisat,[status(thm)],[c_17428,c_1622,c_100]) ).
% 4.00/0.98  
% 4.00/0.98  
% 4.00/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 4.00/0.98  
% 4.00/0.98  ------                               Statistics
% 4.00/0.98  
% 4.00/0.98  ------ General
% 4.00/0.98  
% 4.00/0.98  abstr_ref_over_cycles:                  0
% 4.00/0.98  abstr_ref_under_cycles:                 0
% 4.00/0.98  gc_basic_clause_elim:                   0
% 4.00/0.98  forced_gc_time:                         0
% 4.00/0.98  parsing_time:                           0.01
% 4.00/0.98  unif_index_cands_time:                  0.
% 4.00/0.98  unif_index_add_time:                    0.
% 4.00/0.98  orderings_time:                         0.
% 4.00/0.98  out_proof_time:                         0.012
% 4.00/0.98  total_time:                             0.461
% 4.00/0.98  num_of_symbols:                         54
% 4.00/0.98  num_of_terms:                           14878
% 4.00/0.98  
% 4.00/0.98  ------ Preprocessing
% 4.00/0.98  
% 4.00/0.98  num_of_splits:                          0
% 4.00/0.98  num_of_split_atoms:                     0
% 4.00/0.98  num_of_reused_defs:                     0
% 4.00/0.98  num_eq_ax_congr_red:                    21
% 4.00/0.98  num_of_sem_filtered_clauses:            1
% 4.00/0.98  num_of_subtypes:                        0
% 4.00/0.98  monotx_restored_types:                  0
% 4.00/0.98  sat_num_of_epr_types:                   0
% 4.00/0.98  sat_num_of_non_cyclic_types:            0
% 4.00/0.98  sat_guarded_non_collapsed_types:        0
% 4.00/0.98  num_pure_diseq_elim:                    0
% 4.00/0.98  simp_replaced_by:                       0
% 4.00/0.98  res_preprocessed:                       167
% 4.00/0.98  prep_upred:                             0
% 4.00/0.98  prep_unflattend:                        8
% 4.00/0.98  smt_new_axioms:                         0
% 4.00/0.98  pred_elim_cands:                        7
% 4.00/0.98  pred_elim:                              3
% 4.00/0.98  pred_elim_cl:                           4
% 4.00/0.98  pred_elim_cycles:                       7
% 4.00/0.98  merged_defs:                            0
% 4.00/0.98  merged_defs_ncl:                        0
% 4.00/0.98  bin_hyper_res:                          0
% 4.00/0.98  prep_cycles:                            4
% 4.00/0.98  pred_elim_time:                         0.006
% 4.00/0.98  splitting_time:                         0.
% 4.00/0.98  sem_filter_time:                        0.
% 4.00/0.98  monotx_time:                            0.001
% 4.00/0.98  subtype_inf_time:                       0.
% 4.00/0.98  
% 4.00/0.98  ------ Problem properties
% 4.00/0.98  
% 4.00/0.98  clauses:                                33
% 4.00/0.98  conjectures:                            5
% 4.00/0.98  epr:                                    3
% 4.00/0.98  horn:                                   28
% 4.00/0.98  ground:                                 6
% 4.00/0.98  unary:                                  10
% 4.00/0.98  binary:                                 5
% 4.00/0.98  lits:                                   95
% 4.00/0.98  lits_eq:                                24
% 4.00/0.98  fd_pure:                                0
% 4.00/0.98  fd_pseudo:                              0
% 4.00/0.98  fd_cond:                                5
% 4.00/0.98  fd_pseudo_cond:                         2
% 4.00/0.98  ac_symbols:                             0
% 4.00/0.98  
% 4.00/0.98  ------ Propositional Solver
% 4.00/0.98  
% 4.00/0.98  prop_solver_calls:                      30
% 4.00/0.98  prop_fast_solver_calls:                 1602
% 4.00/0.98  smt_solver_calls:                       0
% 4.00/0.98  smt_fast_solver_calls:                  0
% 4.00/0.98  prop_num_of_clauses:                    5799
% 4.00/0.98  prop_preprocess_simplified:             15355
% 4.00/0.98  prop_fo_subsumed:                       61
% 4.00/0.98  prop_solver_time:                       0.
% 4.00/0.98  smt_solver_time:                        0.
% 4.00/0.98  smt_fast_solver_time:                   0.
% 4.00/0.98  prop_fast_solver_time:                  0.
% 4.00/0.98  prop_unsat_core_time:                   0.
% 4.00/0.98  
% 4.00/0.98  ------ QBF
% 4.00/0.98  
% 4.00/0.98  qbf_q_res:                              0
% 4.00/0.98  qbf_num_tautologies:                    0
% 4.00/0.98  qbf_prep_cycles:                        0
% 4.00/0.98  
% 4.00/0.98  ------ BMC1
% 4.00/0.98  
% 4.00/0.98  bmc1_current_bound:                     -1
% 4.00/0.98  bmc1_last_solved_bound:                 -1
% 4.00/0.98  bmc1_unsat_core_size:                   -1
% 4.00/0.98  bmc1_unsat_core_parents_size:           -1
% 4.00/0.98  bmc1_merge_next_fun:                    0
% 4.00/0.98  bmc1_unsat_core_clauses_time:           0.
% 4.00/0.98  
% 4.00/0.98  ------ Instantiation
% 4.00/0.98  
% 4.00/0.98  inst_num_of_clauses:                    2011
% 4.00/0.98  inst_num_in_passive:                    1099
% 4.00/0.98  inst_num_in_active:                     559
% 4.00/0.98  inst_num_in_unprocessed:                355
% 4.00/0.98  inst_num_of_loops:                      830
% 4.00/0.98  inst_num_of_learning_restarts:          0
% 4.00/0.98  inst_num_moves_active_passive:          269
% 4.00/0.98  inst_lit_activity:                      0
% 4.00/0.98  inst_lit_activity_moves:                0
% 4.00/0.98  inst_num_tautologies:                   0
% 4.00/0.98  inst_num_prop_implied:                  0
% 4.00/0.98  inst_num_existing_simplified:           0
% 4.00/0.98  inst_num_eq_res_simplified:             0
% 4.00/0.98  inst_num_child_elim:                    0
% 4.00/0.98  inst_num_of_dismatching_blockings:      680
% 4.00/0.98  inst_num_of_non_proper_insts:           1614
% 4.00/0.98  inst_num_of_duplicates:                 0
% 4.00/0.98  inst_inst_num_from_inst_to_res:         0
% 4.00/0.98  inst_dismatching_checking_time:         0.
% 4.00/0.98  
% 4.00/0.98  ------ Resolution
% 4.00/0.98  
% 4.00/0.98  res_num_of_clauses:                     0
% 4.00/0.98  res_num_in_passive:                     0
% 4.00/0.98  res_num_in_active:                      0
% 4.00/0.98  res_num_of_loops:                       171
% 4.00/0.98  res_forward_subset_subsumed:            79
% 4.00/0.98  res_backward_subset_subsumed:           4
% 4.00/0.98  res_forward_subsumed:                   0
% 4.00/0.98  res_backward_subsumed:                  0
% 4.00/0.98  res_forward_subsumption_resolution:     2
% 4.00/0.98  res_backward_subsumption_resolution:    0
% 4.00/0.98  res_clause_to_clause_subsumption:       1046
% 4.00/0.98  res_orphan_elimination:                 0
% 4.00/0.98  res_tautology_del:                      53
% 4.00/0.98  res_num_eq_res_simplified:              0
% 4.00/0.98  res_num_sel_changes:                    0
% 4.00/0.98  res_moves_from_active_to_pass:          0
% 4.00/0.98  
% 4.00/0.98  ------ Superposition
% 4.00/0.98  
% 4.00/0.98  sup_time_total:                         0.
% 4.00/0.98  sup_time_generating:                    0.
% 4.00/0.98  sup_time_sim_full:                      0.
% 4.00/0.98  sup_time_sim_immed:                     0.
% 4.00/0.98  
% 4.00/0.98  sup_num_of_clauses:                     214
% 4.00/0.98  sup_num_in_active:                      74
% 4.00/0.98  sup_num_in_passive:                     140
% 4.00/0.98  sup_num_of_loops:                       164
% 4.00/0.98  sup_fw_superposition:                   224
% 4.00/0.98  sup_bw_superposition:                   87
% 4.00/0.98  sup_immediate_simplified:               109
% 4.00/0.98  sup_given_eliminated:                   4
% 4.00/0.98  comparisons_done:                       0
% 4.00/0.98  comparisons_avoided:                    0
% 4.00/0.98  
% 4.00/0.98  ------ Simplifications
% 4.00/0.98  
% 4.00/0.98  
% 4.00/0.98  sim_fw_subset_subsumed:                 26
% 4.00/0.98  sim_bw_subset_subsumed:                 10
% 4.00/0.98  sim_fw_subsumed:                        32
% 4.00/0.98  sim_bw_subsumed:                        4
% 4.00/0.98  sim_fw_subsumption_res:                 7
% 4.00/0.98  sim_bw_subsumption_res:                 0
% 4.00/0.98  sim_tautology_del:                      0
% 4.00/0.98  sim_eq_tautology_del:                   20
% 4.00/0.98  sim_eq_res_simp:                        0
% 4.00/0.98  sim_fw_demodulated:                     21
% 4.00/0.98  sim_bw_demodulated:                     98
% 4.00/0.98  sim_light_normalised:                   51
% 4.00/0.98  sim_joinable_taut:                      0
% 4.00/0.98  sim_joinable_simp:                      0
% 4.00/0.98  sim_ac_normalised:                      0
% 4.00/0.98  sim_smt_subsumption:                    0
% 4.00/0.98  
%------------------------------------------------------------------------------
