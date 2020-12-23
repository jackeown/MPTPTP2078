%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:21 EST 2020

% Result     : Theorem 7.04s
% Output     : CNFRefutation 7.04s
% Verified   : 
% Statistics : Number of formulae       :  210 (3143 expanded)
%              Number of clauses        :  127 ( 973 expanded)
%              Number of leaves         :   22 ( 622 expanded)
%              Depth                    :   28
%              Number of atoms          :  668 (14569 expanded)
%              Number of equality atoms :  311 (1719 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   13 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f44,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f45,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f44])).

fof(f51,plain,
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

fof(f52,plain,
    ( ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) )
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK1,sK0,sK0)
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f45,f51])).

fof(f89,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f52])).

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

fof(f34,plain,(
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

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f49,plain,(
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
    inference(nnf_transformation,[],[f35])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f87,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_1(X1) = k2_funct_2(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f42])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f86,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f88,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f52])).

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

fof(f38,plain,(
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

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f81,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f40])).

fof(f83,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f78,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k2_funct_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f60,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f17,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f85,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f92,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f60,f85])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f32])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f61,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f91,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f61,f85])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

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

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f90,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f52])).

fof(f14,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f82,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f30])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f95,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f66])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f46])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f93,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f56])).

fof(f1,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f53,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f94,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f55])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1305,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1314,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_5202,plain,
    ( k1_relset_1(sK0,sK0,sK1) = sK0
    | sK0 = k1_xboole_0
    | v1_funct_2(sK1,sK0,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1305,c_1314])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1323,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2777,plain,
    ( k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_1305,c_1323])).

cnf(c_5212,plain,
    ( k1_relat_1(sK1) = sK0
    | sK0 = k1_xboole_0
    | v1_funct_2(sK1,sK0,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5202,c_2777])).

cnf(c_35,negated_conjecture,
    ( v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_38,plain,
    ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_5522,plain,
    ( sK0 = k1_xboole_0
    | k1_relat_1(sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5212,c_38])).

cnf(c_5523,plain,
    ( k1_relat_1(sK1) = sK0
    | sK0 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_5522])).

cnf(c_31,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1307,plain,
    ( k2_funct_2(X0,X1) = k2_funct_1(X1)
    | v1_funct_2(X1,X0,X0) != iProver_top
    | v3_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_7534,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1305,c_1307])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_34,negated_conjecture,
    ( v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1650,plain,
    ( ~ v1_funct_2(sK1,X0,X0)
    | ~ v3_funct_2(sK1,X0,X0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v1_funct_1(sK1)
    | k2_funct_2(X0,sK1) = k2_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_1813,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1650])).

cnf(c_7803,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7534,c_36,c_35,c_34,c_33,c_1813])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1313,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_7824,plain,
    ( v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_7803,c_1313])).

cnf(c_37,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_39,plain,
    ( v3_funct_2(sK1,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_40,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_8277,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7824,c_37,c_38,c_39,c_40])).

cnf(c_30,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1308,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_8832,plain,
    ( k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8277,c_1308])).

cnf(c_28,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_2(X1,X0)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1635,plain,
    ( ~ v1_funct_2(sK1,X0,X0)
    | ~ v3_funct_2(sK1,X0,X0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | v1_funct_1(k2_funct_2(X0,sK1))
    | ~ v1_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_1803,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v1_funct_1(k2_funct_2(sK0,sK1))
    | ~ v1_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1635])).

cnf(c_1804,plain,
    ( v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(k2_funct_2(sK0,sK1)) = iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1803])).

cnf(c_816,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2347,plain,
    ( X0 != X1
    | X0 = k2_funct_2(sK0,sK1)
    | k2_funct_2(sK0,sK1) != X1 ),
    inference(instantiation,[status(thm)],[c_816])).

cnf(c_3149,plain,
    ( X0 = k2_funct_2(sK0,sK1)
    | X0 != k2_funct_1(sK1)
    | k2_funct_2(sK0,sK1) != k2_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_2347])).

cnf(c_4066,plain,
    ( k2_funct_2(sK0,sK1) != k2_funct_1(sK1)
    | k2_funct_1(sK1) = k2_funct_2(sK0,sK1)
    | k2_funct_1(sK1) != k2_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_3149])).

cnf(c_815,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_4067,plain,
    ( k2_funct_1(sK1) = k2_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_815])).

cnf(c_824,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1875,plain,
    ( v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_2(sK0,sK1))
    | X0 != k2_funct_2(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_824])).

cnf(c_7621,plain,
    ( ~ v1_funct_1(k2_funct_2(sK0,sK1))
    | v1_funct_1(k2_funct_1(sK1))
    | k2_funct_1(sK1) != k2_funct_2(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_1875])).

cnf(c_7622,plain,
    ( k2_funct_1(sK1) != k2_funct_2(sK0,sK1)
    | v1_funct_1(k2_funct_2(sK0,sK1)) != iProver_top
    | v1_funct_1(k2_funct_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7621])).

cnf(c_13521,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8832,c_36,c_37,c_35,c_38,c_34,c_39,c_33,c_40,c_1804,c_1813,c_4066,c_4067,c_7622])).

cnf(c_13522,plain,
    ( k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_13521])).

cnf(c_13532,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k5_relat_1(sK1,k2_funct_1(sK1))
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1305,c_13522])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1324,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1965,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1305,c_1324])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1325,plain,
    ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3792,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
    | v1_funct_1(sK1) != iProver_top
    | v2_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1965,c_1325])).

cnf(c_1582,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1677,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_15,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1616,plain,
    ( ~ v3_funct_2(sK1,X0,X1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK1)
    | v2_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1739,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | v2_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1616])).

cnf(c_3818,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3792,c_36,c_34,c_33,c_1582,c_1677,c_1739])).

cnf(c_13554,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
    | v1_funct_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13532,c_3818])).

cnf(c_13586,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13554,c_37])).

cnf(c_8831,plain,
    ( k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1305,c_1308])).

cnf(c_9376,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8831,c_37])).

cnf(c_9377,plain,
    ( k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_9376])).

cnf(c_9385,plain,
    ( k1_partfun1(X0,X0,sK0,sK0,k2_funct_2(X0,X1),sK1) = k5_relat_1(k2_funct_2(X0,X1),sK1)
    | v1_funct_2(X1,X0,X0) != iProver_top
    | v3_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(k2_funct_2(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1313,c_9377])).

cnf(c_1310,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_2(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_11079,plain,
    ( k1_partfun1(X0,X0,sK0,sK0,k2_funct_2(X0,X1),sK1) = k5_relat_1(k2_funct_2(X0,X1),sK1)
    | v1_funct_2(X1,X0,X0) != iProver_top
    | v3_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_9385,c_1310])).

cnf(c_11085,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1) = k5_relat_1(k2_funct_2(sK0,sK1),sK1)
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1305,c_11079])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1326,plain,
    ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4100,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1))
    | v1_funct_1(sK1) != iProver_top
    | v2_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1965,c_1326])).

cnf(c_14,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_10,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_24,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_384,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_10,c_24])).

cnf(c_394,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | k2_relat_1(X0) = X1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_384,c_9])).

cnf(c_465,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | X3 != X0
    | X5 != X2
    | k2_relat_1(X3) = X5 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_394])).

cnf(c_466,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(unflattening,[status(thm)],[c_465])).

cnf(c_1300,plain,
    ( k2_relat_1(X0) = X1
    | v3_funct_2(X0,X2,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_466])).

cnf(c_2244,plain,
    ( k2_relat_1(sK1) = sK0
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1305,c_1300])).

cnf(c_2604,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | k2_relat_1(sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2244,c_37,c_39])).

cnf(c_2605,plain,
    ( k2_relat_1(sK1) = sK0
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2604])).

cnf(c_2612,plain,
    ( k2_relat_1(sK1) = sK0 ),
    inference(superposition,[status(thm)],[c_1305,c_2605])).

cnf(c_4104,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
    | v1_funct_1(sK1) != iProver_top
    | v2_funct_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4100,c_2612])).

cnf(c_1740,plain,
    ( v3_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v2_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1739])).

cnf(c_4260,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4104,c_37,c_39,c_40,c_1740])).

cnf(c_11111,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11085,c_4260,c_7803])).

cnf(c_9388,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k5_relat_1(k2_funct_1(sK1),sK1)
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8277,c_9377])).

cnf(c_9405,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9388,c_4260])).

cnf(c_11359,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11111,c_36,c_37,c_35,c_38,c_34,c_39,c_33,c_40,c_1804,c_1813,c_4066,c_4067,c_7622,c_9405])).

cnf(c_32,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1306,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) != iProver_top
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_7809,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) != iProver_top
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7803,c_1306])).

cnf(c_11362,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top
    | r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11359,c_7809])).

cnf(c_29,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_4079,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_4080,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4079])).

cnf(c_12,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1608,plain,
    ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0))
    | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_6664,plain,
    ( r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_1608])).

cnf(c_6665,plain,
    ( r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) = iProver_top
    | m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6664])).

cnf(c_11365,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11362,c_4080,c_6665])).

cnf(c_13589,plain,
    ( r2_relset_1(sK0,sK0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_13586,c_11365])).

cnf(c_13942,plain,
    ( sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5523,c_13589])).

cnf(c_15005,plain,
    ( sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_13942,c_4080,c_6665])).

cnf(c_15011,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_15005,c_13589])).

cnf(c_1,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1309,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_1808,plain,
    ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_1309])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_369,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X0 != X2
    | k1_xboole_0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_4])).

cnf(c_370,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_369])).

cnf(c_1301,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_370])).

cnf(c_1915,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1808,c_1301])).

cnf(c_15271,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_relat_1(sK1)),k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_15011,c_1915])).

cnf(c_6,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_15057,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_15005,c_1305])).

cnf(c_2,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_15065,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_15057,c_2])).

cnf(c_15585,plain,
    ( sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_15065,c_1301])).

cnf(c_24173,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_15271,c_6,c_1915,c_15585])).

cnf(c_1322,plain,
    ( r2_relset_1(X0,X1,X2,X2) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2381,plain,
    ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1309,c_1322])).

cnf(c_2735,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1915,c_2381])).

cnf(c_24175,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_24173,c_2735])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:53:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.04/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.04/1.49  
% 7.04/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.04/1.49  
% 7.04/1.49  ------  iProver source info
% 7.04/1.49  
% 7.04/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.04/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.04/1.49  git: non_committed_changes: false
% 7.04/1.49  git: last_make_outside_of_git: false
% 7.04/1.49  
% 7.04/1.49  ------ 
% 7.04/1.49  
% 7.04/1.49  ------ Input Options
% 7.04/1.49  
% 7.04/1.49  --out_options                           all
% 7.04/1.49  --tptp_safe_out                         true
% 7.04/1.49  --problem_path                          ""
% 7.04/1.49  --include_path                          ""
% 7.04/1.49  --clausifier                            res/vclausify_rel
% 7.04/1.49  --clausifier_options                    --mode clausify
% 7.04/1.49  --stdin                                 false
% 7.04/1.49  --stats_out                             all
% 7.04/1.49  
% 7.04/1.49  ------ General Options
% 7.04/1.49  
% 7.04/1.49  --fof                                   false
% 7.04/1.49  --time_out_real                         305.
% 7.04/1.49  --time_out_virtual                      -1.
% 7.04/1.49  --symbol_type_check                     false
% 7.04/1.49  --clausify_out                          false
% 7.04/1.49  --sig_cnt_out                           false
% 7.04/1.49  --trig_cnt_out                          false
% 7.04/1.49  --trig_cnt_out_tolerance                1.
% 7.04/1.49  --trig_cnt_out_sk_spl                   false
% 7.04/1.49  --abstr_cl_out                          false
% 7.04/1.49  
% 7.04/1.49  ------ Global Options
% 7.04/1.49  
% 7.04/1.49  --schedule                              default
% 7.04/1.49  --add_important_lit                     false
% 7.04/1.49  --prop_solver_per_cl                    1000
% 7.04/1.49  --min_unsat_core                        false
% 7.04/1.49  --soft_assumptions                      false
% 7.04/1.49  --soft_lemma_size                       3
% 7.04/1.49  --prop_impl_unit_size                   0
% 7.04/1.49  --prop_impl_unit                        []
% 7.04/1.49  --share_sel_clauses                     true
% 7.04/1.49  --reset_solvers                         false
% 7.04/1.49  --bc_imp_inh                            [conj_cone]
% 7.04/1.49  --conj_cone_tolerance                   3.
% 7.04/1.49  --extra_neg_conj                        none
% 7.04/1.49  --large_theory_mode                     true
% 7.04/1.49  --prolific_symb_bound                   200
% 7.04/1.49  --lt_threshold                          2000
% 7.04/1.49  --clause_weak_htbl                      true
% 7.04/1.49  --gc_record_bc_elim                     false
% 7.04/1.49  
% 7.04/1.49  ------ Preprocessing Options
% 7.04/1.49  
% 7.04/1.49  --preprocessing_flag                    true
% 7.04/1.49  --time_out_prep_mult                    0.1
% 7.04/1.49  --splitting_mode                        input
% 7.04/1.49  --splitting_grd                         true
% 7.04/1.49  --splitting_cvd                         false
% 7.04/1.49  --splitting_cvd_svl                     false
% 7.04/1.49  --splitting_nvd                         32
% 7.04/1.49  --sub_typing                            true
% 7.04/1.49  --prep_gs_sim                           true
% 7.04/1.49  --prep_unflatten                        true
% 7.04/1.49  --prep_res_sim                          true
% 7.04/1.49  --prep_upred                            true
% 7.04/1.49  --prep_sem_filter                       exhaustive
% 7.04/1.49  --prep_sem_filter_out                   false
% 7.04/1.49  --pred_elim                             true
% 7.04/1.49  --res_sim_input                         true
% 7.04/1.49  --eq_ax_congr_red                       true
% 7.04/1.49  --pure_diseq_elim                       true
% 7.04/1.49  --brand_transform                       false
% 7.04/1.49  --non_eq_to_eq                          false
% 7.04/1.49  --prep_def_merge                        true
% 7.04/1.49  --prep_def_merge_prop_impl              false
% 7.04/1.49  --prep_def_merge_mbd                    true
% 7.04/1.49  --prep_def_merge_tr_red                 false
% 7.04/1.49  --prep_def_merge_tr_cl                  false
% 7.04/1.49  --smt_preprocessing                     true
% 7.04/1.49  --smt_ac_axioms                         fast
% 7.04/1.49  --preprocessed_out                      false
% 7.04/1.49  --preprocessed_stats                    false
% 7.04/1.49  
% 7.04/1.49  ------ Abstraction refinement Options
% 7.04/1.49  
% 7.04/1.49  --abstr_ref                             []
% 7.04/1.49  --abstr_ref_prep                        false
% 7.04/1.49  --abstr_ref_until_sat                   false
% 7.04/1.49  --abstr_ref_sig_restrict                funpre
% 7.04/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.04/1.49  --abstr_ref_under                       []
% 7.04/1.49  
% 7.04/1.49  ------ SAT Options
% 7.04/1.49  
% 7.04/1.49  --sat_mode                              false
% 7.04/1.49  --sat_fm_restart_options                ""
% 7.04/1.49  --sat_gr_def                            false
% 7.04/1.49  --sat_epr_types                         true
% 7.04/1.49  --sat_non_cyclic_types                  false
% 7.04/1.49  --sat_finite_models                     false
% 7.04/1.49  --sat_fm_lemmas                         false
% 7.04/1.49  --sat_fm_prep                           false
% 7.04/1.49  --sat_fm_uc_incr                        true
% 7.04/1.49  --sat_out_model                         small
% 7.04/1.49  --sat_out_clauses                       false
% 7.04/1.49  
% 7.04/1.49  ------ QBF Options
% 7.04/1.49  
% 7.04/1.49  --qbf_mode                              false
% 7.04/1.49  --qbf_elim_univ                         false
% 7.04/1.49  --qbf_dom_inst                          none
% 7.04/1.49  --qbf_dom_pre_inst                      false
% 7.04/1.49  --qbf_sk_in                             false
% 7.04/1.49  --qbf_pred_elim                         true
% 7.04/1.49  --qbf_split                             512
% 7.04/1.49  
% 7.04/1.49  ------ BMC1 Options
% 7.04/1.49  
% 7.04/1.49  --bmc1_incremental                      false
% 7.04/1.49  --bmc1_axioms                           reachable_all
% 7.04/1.49  --bmc1_min_bound                        0
% 7.04/1.49  --bmc1_max_bound                        -1
% 7.04/1.49  --bmc1_max_bound_default                -1
% 7.04/1.49  --bmc1_symbol_reachability              true
% 7.04/1.49  --bmc1_property_lemmas                  false
% 7.04/1.49  --bmc1_k_induction                      false
% 7.04/1.49  --bmc1_non_equiv_states                 false
% 7.04/1.49  --bmc1_deadlock                         false
% 7.04/1.49  --bmc1_ucm                              false
% 7.04/1.49  --bmc1_add_unsat_core                   none
% 7.04/1.49  --bmc1_unsat_core_children              false
% 7.04/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.04/1.49  --bmc1_out_stat                         full
% 7.04/1.49  --bmc1_ground_init                      false
% 7.04/1.49  --bmc1_pre_inst_next_state              false
% 7.04/1.49  --bmc1_pre_inst_state                   false
% 7.04/1.49  --bmc1_pre_inst_reach_state             false
% 7.04/1.49  --bmc1_out_unsat_core                   false
% 7.04/1.49  --bmc1_aig_witness_out                  false
% 7.04/1.49  --bmc1_verbose                          false
% 7.04/1.49  --bmc1_dump_clauses_tptp                false
% 7.04/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.04/1.49  --bmc1_dump_file                        -
% 7.04/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.04/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.04/1.49  --bmc1_ucm_extend_mode                  1
% 7.04/1.49  --bmc1_ucm_init_mode                    2
% 7.04/1.49  --bmc1_ucm_cone_mode                    none
% 7.04/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.04/1.49  --bmc1_ucm_relax_model                  4
% 7.04/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.04/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.04/1.49  --bmc1_ucm_layered_model                none
% 7.04/1.49  --bmc1_ucm_max_lemma_size               10
% 7.04/1.49  
% 7.04/1.49  ------ AIG Options
% 7.04/1.49  
% 7.04/1.49  --aig_mode                              false
% 7.04/1.49  
% 7.04/1.49  ------ Instantiation Options
% 7.04/1.49  
% 7.04/1.49  --instantiation_flag                    true
% 7.04/1.49  --inst_sos_flag                         false
% 7.04/1.49  --inst_sos_phase                        true
% 7.04/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.04/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.04/1.49  --inst_lit_sel_side                     num_symb
% 7.04/1.49  --inst_solver_per_active                1400
% 7.04/1.49  --inst_solver_calls_frac                1.
% 7.04/1.49  --inst_passive_queue_type               priority_queues
% 7.04/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.04/1.49  --inst_passive_queues_freq              [25;2]
% 7.04/1.49  --inst_dismatching                      true
% 7.04/1.49  --inst_eager_unprocessed_to_passive     true
% 7.04/1.49  --inst_prop_sim_given                   true
% 7.04/1.49  --inst_prop_sim_new                     false
% 7.04/1.49  --inst_subs_new                         false
% 7.04/1.49  --inst_eq_res_simp                      false
% 7.04/1.49  --inst_subs_given                       false
% 7.04/1.49  --inst_orphan_elimination               true
% 7.04/1.49  --inst_learning_loop_flag               true
% 7.04/1.49  --inst_learning_start                   3000
% 7.04/1.49  --inst_learning_factor                  2
% 7.04/1.49  --inst_start_prop_sim_after_learn       3
% 7.04/1.49  --inst_sel_renew                        solver
% 7.04/1.49  --inst_lit_activity_flag                true
% 7.04/1.49  --inst_restr_to_given                   false
% 7.04/1.49  --inst_activity_threshold               500
% 7.04/1.49  --inst_out_proof                        true
% 7.04/1.49  
% 7.04/1.49  ------ Resolution Options
% 7.04/1.49  
% 7.04/1.49  --resolution_flag                       true
% 7.04/1.49  --res_lit_sel                           adaptive
% 7.04/1.49  --res_lit_sel_side                      none
% 7.04/1.49  --res_ordering                          kbo
% 7.04/1.49  --res_to_prop_solver                    active
% 7.04/1.49  --res_prop_simpl_new                    false
% 7.04/1.49  --res_prop_simpl_given                  true
% 7.04/1.49  --res_passive_queue_type                priority_queues
% 7.04/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.04/1.49  --res_passive_queues_freq               [15;5]
% 7.04/1.49  --res_forward_subs                      full
% 7.04/1.49  --res_backward_subs                     full
% 7.04/1.49  --res_forward_subs_resolution           true
% 7.04/1.49  --res_backward_subs_resolution          true
% 7.04/1.49  --res_orphan_elimination                true
% 7.04/1.49  --res_time_limit                        2.
% 7.04/1.49  --res_out_proof                         true
% 7.04/1.49  
% 7.04/1.49  ------ Superposition Options
% 7.04/1.49  
% 7.04/1.49  --superposition_flag                    true
% 7.04/1.49  --sup_passive_queue_type                priority_queues
% 7.04/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.04/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.04/1.49  --demod_completeness_check              fast
% 7.04/1.49  --demod_use_ground                      true
% 7.04/1.49  --sup_to_prop_solver                    passive
% 7.04/1.49  --sup_prop_simpl_new                    true
% 7.04/1.49  --sup_prop_simpl_given                  true
% 7.04/1.49  --sup_fun_splitting                     false
% 7.04/1.49  --sup_smt_interval                      50000
% 7.04/1.49  
% 7.04/1.49  ------ Superposition Simplification Setup
% 7.04/1.49  
% 7.04/1.49  --sup_indices_passive                   []
% 7.04/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.04/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.04/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.04/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.04/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.04/1.49  --sup_full_bw                           [BwDemod]
% 7.04/1.49  --sup_immed_triv                        [TrivRules]
% 7.04/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.04/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.04/1.49  --sup_immed_bw_main                     []
% 7.04/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.04/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.04/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.04/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.04/1.49  
% 7.04/1.49  ------ Combination Options
% 7.04/1.49  
% 7.04/1.49  --comb_res_mult                         3
% 7.04/1.49  --comb_sup_mult                         2
% 7.04/1.49  --comb_inst_mult                        10
% 7.04/1.49  
% 7.04/1.49  ------ Debug Options
% 7.04/1.49  
% 7.04/1.49  --dbg_backtrace                         false
% 7.04/1.49  --dbg_dump_prop_clauses                 false
% 7.04/1.49  --dbg_dump_prop_clauses_file            -
% 7.04/1.49  --dbg_out_stat                          false
% 7.04/1.49  ------ Parsing...
% 7.04/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.04/1.49  
% 7.04/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 7.04/1.49  
% 7.04/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.04/1.49  
% 7.04/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.04/1.49  ------ Proving...
% 7.04/1.49  ------ Problem Properties 
% 7.04/1.49  
% 7.04/1.49  
% 7.04/1.49  clauses                                 32
% 7.04/1.49  conjectures                             5
% 7.04/1.49  EPR                                     3
% 7.04/1.49  Horn                                    27
% 7.04/1.49  unary                                   9
% 7.04/1.49  binary                                  5
% 7.04/1.49  lits                                    94
% 7.04/1.49  lits eq                                 24
% 7.04/1.49  fd_pure                                 0
% 7.04/1.49  fd_pseudo                               0
% 7.04/1.49  fd_cond                                 5
% 7.04/1.49  fd_pseudo_cond                          2
% 7.04/1.49  AC symbols                              0
% 7.04/1.49  
% 7.04/1.49  ------ Schedule dynamic 5 is on 
% 7.04/1.49  
% 7.04/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.04/1.49  
% 7.04/1.49  
% 7.04/1.49  ------ 
% 7.04/1.49  Current options:
% 7.04/1.49  ------ 
% 7.04/1.49  
% 7.04/1.49  ------ Input Options
% 7.04/1.49  
% 7.04/1.49  --out_options                           all
% 7.04/1.49  --tptp_safe_out                         true
% 7.04/1.49  --problem_path                          ""
% 7.04/1.49  --include_path                          ""
% 7.04/1.49  --clausifier                            res/vclausify_rel
% 7.04/1.49  --clausifier_options                    --mode clausify
% 7.04/1.49  --stdin                                 false
% 7.04/1.49  --stats_out                             all
% 7.04/1.49  
% 7.04/1.49  ------ General Options
% 7.04/1.49  
% 7.04/1.49  --fof                                   false
% 7.04/1.49  --time_out_real                         305.
% 7.04/1.49  --time_out_virtual                      -1.
% 7.04/1.49  --symbol_type_check                     false
% 7.04/1.49  --clausify_out                          false
% 7.04/1.49  --sig_cnt_out                           false
% 7.04/1.49  --trig_cnt_out                          false
% 7.04/1.49  --trig_cnt_out_tolerance                1.
% 7.04/1.49  --trig_cnt_out_sk_spl                   false
% 7.04/1.49  --abstr_cl_out                          false
% 7.04/1.49  
% 7.04/1.49  ------ Global Options
% 7.04/1.49  
% 7.04/1.49  --schedule                              default
% 7.04/1.49  --add_important_lit                     false
% 7.04/1.49  --prop_solver_per_cl                    1000
% 7.04/1.49  --min_unsat_core                        false
% 7.04/1.49  --soft_assumptions                      false
% 7.04/1.49  --soft_lemma_size                       3
% 7.04/1.49  --prop_impl_unit_size                   0
% 7.04/1.49  --prop_impl_unit                        []
% 7.04/1.49  --share_sel_clauses                     true
% 7.04/1.49  --reset_solvers                         false
% 7.04/1.49  --bc_imp_inh                            [conj_cone]
% 7.04/1.49  --conj_cone_tolerance                   3.
% 7.04/1.49  --extra_neg_conj                        none
% 7.04/1.49  --large_theory_mode                     true
% 7.04/1.49  --prolific_symb_bound                   200
% 7.04/1.49  --lt_threshold                          2000
% 7.04/1.49  --clause_weak_htbl                      true
% 7.04/1.49  --gc_record_bc_elim                     false
% 7.04/1.49  
% 7.04/1.49  ------ Preprocessing Options
% 7.04/1.49  
% 7.04/1.49  --preprocessing_flag                    true
% 7.04/1.49  --time_out_prep_mult                    0.1
% 7.04/1.49  --splitting_mode                        input
% 7.04/1.49  --splitting_grd                         true
% 7.04/1.49  --splitting_cvd                         false
% 7.04/1.49  --splitting_cvd_svl                     false
% 7.04/1.49  --splitting_nvd                         32
% 7.04/1.49  --sub_typing                            true
% 7.04/1.49  --prep_gs_sim                           true
% 7.04/1.49  --prep_unflatten                        true
% 7.04/1.49  --prep_res_sim                          true
% 7.04/1.49  --prep_upred                            true
% 7.04/1.49  --prep_sem_filter                       exhaustive
% 7.04/1.49  --prep_sem_filter_out                   false
% 7.04/1.49  --pred_elim                             true
% 7.04/1.49  --res_sim_input                         true
% 7.04/1.49  --eq_ax_congr_red                       true
% 7.04/1.49  --pure_diseq_elim                       true
% 7.04/1.49  --brand_transform                       false
% 7.04/1.49  --non_eq_to_eq                          false
% 7.04/1.49  --prep_def_merge                        true
% 7.04/1.49  --prep_def_merge_prop_impl              false
% 7.04/1.49  --prep_def_merge_mbd                    true
% 7.04/1.49  --prep_def_merge_tr_red                 false
% 7.04/1.49  --prep_def_merge_tr_cl                  false
% 7.04/1.49  --smt_preprocessing                     true
% 7.04/1.49  --smt_ac_axioms                         fast
% 7.04/1.49  --preprocessed_out                      false
% 7.04/1.49  --preprocessed_stats                    false
% 7.04/1.49  
% 7.04/1.49  ------ Abstraction refinement Options
% 7.04/1.49  
% 7.04/1.49  --abstr_ref                             []
% 7.04/1.49  --abstr_ref_prep                        false
% 7.04/1.49  --abstr_ref_until_sat                   false
% 7.04/1.49  --abstr_ref_sig_restrict                funpre
% 7.04/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.04/1.49  --abstr_ref_under                       []
% 7.04/1.49  
% 7.04/1.49  ------ SAT Options
% 7.04/1.49  
% 7.04/1.49  --sat_mode                              false
% 7.04/1.49  --sat_fm_restart_options                ""
% 7.04/1.49  --sat_gr_def                            false
% 7.04/1.49  --sat_epr_types                         true
% 7.04/1.49  --sat_non_cyclic_types                  false
% 7.04/1.49  --sat_finite_models                     false
% 7.04/1.49  --sat_fm_lemmas                         false
% 7.04/1.49  --sat_fm_prep                           false
% 7.04/1.49  --sat_fm_uc_incr                        true
% 7.04/1.49  --sat_out_model                         small
% 7.04/1.49  --sat_out_clauses                       false
% 7.04/1.49  
% 7.04/1.49  ------ QBF Options
% 7.04/1.49  
% 7.04/1.49  --qbf_mode                              false
% 7.04/1.49  --qbf_elim_univ                         false
% 7.04/1.49  --qbf_dom_inst                          none
% 7.04/1.49  --qbf_dom_pre_inst                      false
% 7.04/1.49  --qbf_sk_in                             false
% 7.04/1.49  --qbf_pred_elim                         true
% 7.04/1.49  --qbf_split                             512
% 7.04/1.49  
% 7.04/1.49  ------ BMC1 Options
% 7.04/1.49  
% 7.04/1.49  --bmc1_incremental                      false
% 7.04/1.49  --bmc1_axioms                           reachable_all
% 7.04/1.49  --bmc1_min_bound                        0
% 7.04/1.49  --bmc1_max_bound                        -1
% 7.04/1.49  --bmc1_max_bound_default                -1
% 7.04/1.49  --bmc1_symbol_reachability              true
% 7.04/1.49  --bmc1_property_lemmas                  false
% 7.04/1.49  --bmc1_k_induction                      false
% 7.04/1.49  --bmc1_non_equiv_states                 false
% 7.04/1.49  --bmc1_deadlock                         false
% 7.04/1.49  --bmc1_ucm                              false
% 7.04/1.49  --bmc1_add_unsat_core                   none
% 7.04/1.49  --bmc1_unsat_core_children              false
% 7.04/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.04/1.49  --bmc1_out_stat                         full
% 7.04/1.49  --bmc1_ground_init                      false
% 7.04/1.49  --bmc1_pre_inst_next_state              false
% 7.04/1.49  --bmc1_pre_inst_state                   false
% 7.04/1.49  --bmc1_pre_inst_reach_state             false
% 7.04/1.49  --bmc1_out_unsat_core                   false
% 7.04/1.49  --bmc1_aig_witness_out                  false
% 7.04/1.49  --bmc1_verbose                          false
% 7.04/1.49  --bmc1_dump_clauses_tptp                false
% 7.04/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.04/1.49  --bmc1_dump_file                        -
% 7.04/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.04/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.04/1.49  --bmc1_ucm_extend_mode                  1
% 7.04/1.49  --bmc1_ucm_init_mode                    2
% 7.04/1.49  --bmc1_ucm_cone_mode                    none
% 7.04/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.04/1.49  --bmc1_ucm_relax_model                  4
% 7.04/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.04/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.04/1.49  --bmc1_ucm_layered_model                none
% 7.04/1.49  --bmc1_ucm_max_lemma_size               10
% 7.04/1.49  
% 7.04/1.49  ------ AIG Options
% 7.04/1.49  
% 7.04/1.49  --aig_mode                              false
% 7.04/1.49  
% 7.04/1.49  ------ Instantiation Options
% 7.04/1.49  
% 7.04/1.49  --instantiation_flag                    true
% 7.04/1.49  --inst_sos_flag                         false
% 7.04/1.49  --inst_sos_phase                        true
% 7.04/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.04/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.04/1.49  --inst_lit_sel_side                     none
% 7.04/1.49  --inst_solver_per_active                1400
% 7.04/1.49  --inst_solver_calls_frac                1.
% 7.04/1.49  --inst_passive_queue_type               priority_queues
% 7.04/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.04/1.49  --inst_passive_queues_freq              [25;2]
% 7.04/1.49  --inst_dismatching                      true
% 7.04/1.49  --inst_eager_unprocessed_to_passive     true
% 7.04/1.49  --inst_prop_sim_given                   true
% 7.04/1.49  --inst_prop_sim_new                     false
% 7.04/1.49  --inst_subs_new                         false
% 7.04/1.49  --inst_eq_res_simp                      false
% 7.04/1.49  --inst_subs_given                       false
% 7.04/1.49  --inst_orphan_elimination               true
% 7.04/1.49  --inst_learning_loop_flag               true
% 7.04/1.49  --inst_learning_start                   3000
% 7.04/1.49  --inst_learning_factor                  2
% 7.04/1.49  --inst_start_prop_sim_after_learn       3
% 7.04/1.49  --inst_sel_renew                        solver
% 7.04/1.49  --inst_lit_activity_flag                true
% 7.04/1.49  --inst_restr_to_given                   false
% 7.04/1.49  --inst_activity_threshold               500
% 7.04/1.49  --inst_out_proof                        true
% 7.04/1.49  
% 7.04/1.49  ------ Resolution Options
% 7.04/1.49  
% 7.04/1.49  --resolution_flag                       false
% 7.04/1.49  --res_lit_sel                           adaptive
% 7.04/1.49  --res_lit_sel_side                      none
% 7.04/1.49  --res_ordering                          kbo
% 7.04/1.49  --res_to_prop_solver                    active
% 7.04/1.49  --res_prop_simpl_new                    false
% 7.04/1.49  --res_prop_simpl_given                  true
% 7.04/1.49  --res_passive_queue_type                priority_queues
% 7.04/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.04/1.49  --res_passive_queues_freq               [15;5]
% 7.04/1.49  --res_forward_subs                      full
% 7.04/1.49  --res_backward_subs                     full
% 7.04/1.49  --res_forward_subs_resolution           true
% 7.04/1.49  --res_backward_subs_resolution          true
% 7.04/1.49  --res_orphan_elimination                true
% 7.04/1.49  --res_time_limit                        2.
% 7.04/1.49  --res_out_proof                         true
% 7.04/1.49  
% 7.04/1.49  ------ Superposition Options
% 7.04/1.49  
% 7.04/1.49  --superposition_flag                    true
% 7.04/1.49  --sup_passive_queue_type                priority_queues
% 7.04/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.04/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.04/1.49  --demod_completeness_check              fast
% 7.04/1.49  --demod_use_ground                      true
% 7.04/1.49  --sup_to_prop_solver                    passive
% 7.04/1.49  --sup_prop_simpl_new                    true
% 7.04/1.49  --sup_prop_simpl_given                  true
% 7.04/1.49  --sup_fun_splitting                     false
% 7.04/1.49  --sup_smt_interval                      50000
% 7.04/1.49  
% 7.04/1.49  ------ Superposition Simplification Setup
% 7.04/1.49  
% 7.04/1.49  --sup_indices_passive                   []
% 7.04/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.04/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.04/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.04/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.04/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.04/1.49  --sup_full_bw                           [BwDemod]
% 7.04/1.49  --sup_immed_triv                        [TrivRules]
% 7.04/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.04/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.04/1.49  --sup_immed_bw_main                     []
% 7.04/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.04/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.04/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.04/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.04/1.49  
% 7.04/1.49  ------ Combination Options
% 7.04/1.49  
% 7.04/1.49  --comb_res_mult                         3
% 7.04/1.49  --comb_sup_mult                         2
% 7.04/1.49  --comb_inst_mult                        10
% 7.04/1.49  
% 7.04/1.49  ------ Debug Options
% 7.04/1.49  
% 7.04/1.49  --dbg_backtrace                         false
% 7.04/1.49  --dbg_dump_prop_clauses                 false
% 7.04/1.49  --dbg_dump_prop_clauses_file            -
% 7.04/1.49  --dbg_out_stat                          false
% 7.04/1.49  
% 7.04/1.49  
% 7.04/1.49  
% 7.04/1.49  
% 7.04/1.49  ------ Proving...
% 7.04/1.49  
% 7.04/1.49  
% 7.04/1.49  % SZS status Theorem for theBenchmark.p
% 7.04/1.49  
% 7.04/1.49   Resolution empty clause
% 7.04/1.49  
% 7.04/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.04/1.49  
% 7.04/1.49  fof(f18,conjecture,(
% 7.04/1.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 7.04/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.04/1.49  
% 7.04/1.49  fof(f19,negated_conjecture,(
% 7.04/1.49    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 7.04/1.49    inference(negated_conjecture,[],[f18])).
% 7.04/1.49  
% 7.04/1.49  fof(f44,plain,(
% 7.04/1.49    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 7.04/1.49    inference(ennf_transformation,[],[f19])).
% 7.04/1.49  
% 7.04/1.49  fof(f45,plain,(
% 7.04/1.49    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 7.04/1.49    inference(flattening,[],[f44])).
% 7.04/1.49  
% 7.04/1.49  fof(f51,plain,(
% 7.04/1.49    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 7.04/1.49    introduced(choice_axiom,[])).
% 7.04/1.49  
% 7.04/1.49  fof(f52,plain,(
% 7.04/1.49    (~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 7.04/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f45,f51])).
% 7.04/1.49  
% 7.04/1.49  fof(f89,plain,(
% 7.04/1.49    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 7.04/1.49    inference(cnf_transformation,[],[f52])).
% 7.04/1.49  
% 7.04/1.49  fof(f11,axiom,(
% 7.04/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 7.04/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.04/1.49  
% 7.04/1.49  fof(f34,plain,(
% 7.04/1.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.04/1.49    inference(ennf_transformation,[],[f11])).
% 7.04/1.49  
% 7.04/1.49  fof(f35,plain,(
% 7.04/1.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.04/1.49    inference(flattening,[],[f34])).
% 7.04/1.49  
% 7.04/1.49  fof(f49,plain,(
% 7.04/1.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.04/1.49    inference(nnf_transformation,[],[f35])).
% 7.04/1.49  
% 7.04/1.49  fof(f70,plain,(
% 7.04/1.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.04/1.49    inference(cnf_transformation,[],[f49])).
% 7.04/1.49  
% 7.04/1.49  fof(f8,axiom,(
% 7.04/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 7.04/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.04/1.49  
% 7.04/1.49  fof(f29,plain,(
% 7.04/1.49    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.04/1.49    inference(ennf_transformation,[],[f8])).
% 7.04/1.49  
% 7.04/1.49  fof(f64,plain,(
% 7.04/1.49    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.04/1.49    inference(cnf_transformation,[],[f29])).
% 7.04/1.49  
% 7.04/1.49  fof(f87,plain,(
% 7.04/1.49    v1_funct_2(sK1,sK0,sK0)),
% 7.04/1.49    inference(cnf_transformation,[],[f52])).
% 7.04/1.49  
% 7.04/1.49  fof(f16,axiom,(
% 7.04/1.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 7.04/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.04/1.49  
% 7.04/1.49  fof(f42,plain,(
% 7.04/1.49    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 7.04/1.49    inference(ennf_transformation,[],[f16])).
% 7.04/1.49  
% 7.04/1.49  fof(f43,plain,(
% 7.04/1.49    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 7.04/1.49    inference(flattening,[],[f42])).
% 7.04/1.49  
% 7.04/1.49  fof(f84,plain,(
% 7.04/1.49    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 7.04/1.49    inference(cnf_transformation,[],[f43])).
% 7.04/1.49  
% 7.04/1.49  fof(f86,plain,(
% 7.04/1.49    v1_funct_1(sK1)),
% 7.04/1.49    inference(cnf_transformation,[],[f52])).
% 7.04/1.49  
% 7.04/1.49  fof(f88,plain,(
% 7.04/1.49    v3_funct_2(sK1,sK0,sK0)),
% 7.04/1.49    inference(cnf_transformation,[],[f52])).
% 7.04/1.49  
% 7.04/1.49  fof(f13,axiom,(
% 7.04/1.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 7.04/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.04/1.49  
% 7.04/1.49  fof(f38,plain,(
% 7.04/1.49    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 7.04/1.49    inference(ennf_transformation,[],[f13])).
% 7.04/1.49  
% 7.04/1.49  fof(f39,plain,(
% 7.04/1.49    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 7.04/1.49    inference(flattening,[],[f38])).
% 7.04/1.49  
% 7.04/1.49  fof(f81,plain,(
% 7.04/1.49    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 7.04/1.49    inference(cnf_transformation,[],[f39])).
% 7.04/1.49  
% 7.04/1.49  fof(f15,axiom,(
% 7.04/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 7.04/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.04/1.49  
% 7.04/1.49  fof(f40,plain,(
% 7.04/1.49    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 7.04/1.49    inference(ennf_transformation,[],[f15])).
% 7.04/1.49  
% 7.04/1.49  fof(f41,plain,(
% 7.04/1.49    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 7.04/1.49    inference(flattening,[],[f40])).
% 7.04/1.49  
% 7.04/1.49  fof(f83,plain,(
% 7.04/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 7.04/1.49    inference(cnf_transformation,[],[f41])).
% 7.04/1.49  
% 7.04/1.49  fof(f78,plain,(
% 7.04/1.49    ( ! [X0,X1] : (v1_funct_1(k2_funct_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 7.04/1.49    inference(cnf_transformation,[],[f39])).
% 7.04/1.49  
% 7.04/1.49  fof(f6,axiom,(
% 7.04/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.04/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.04/1.49  
% 7.04/1.49  fof(f27,plain,(
% 7.04/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.04/1.49    inference(ennf_transformation,[],[f6])).
% 7.04/1.49  
% 7.04/1.49  fof(f62,plain,(
% 7.04/1.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.04/1.49    inference(cnf_transformation,[],[f27])).
% 7.04/1.49  
% 7.04/1.49  fof(f5,axiom,(
% 7.04/1.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 7.04/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.04/1.49  
% 7.04/1.49  fof(f25,plain,(
% 7.04/1.49    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.04/1.49    inference(ennf_transformation,[],[f5])).
% 7.04/1.49  
% 7.04/1.49  fof(f26,plain,(
% 7.04/1.49    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.04/1.49    inference(flattening,[],[f25])).
% 7.04/1.49  
% 7.04/1.49  fof(f60,plain,(
% 7.04/1.49    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.04/1.49    inference(cnf_transformation,[],[f26])).
% 7.04/1.49  
% 7.04/1.49  fof(f17,axiom,(
% 7.04/1.49    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 7.04/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.04/1.49  
% 7.04/1.49  fof(f85,plain,(
% 7.04/1.49    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 7.04/1.49    inference(cnf_transformation,[],[f17])).
% 7.04/1.49  
% 7.04/1.49  fof(f92,plain,(
% 7.04/1.49    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.04/1.49    inference(definition_unfolding,[],[f60,f85])).
% 7.04/1.49  
% 7.04/1.49  fof(f10,axiom,(
% 7.04/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 7.04/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.04/1.49  
% 7.04/1.49  fof(f32,plain,(
% 7.04/1.49    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.04/1.49    inference(ennf_transformation,[],[f10])).
% 7.04/1.49  
% 7.04/1.49  fof(f33,plain,(
% 7.04/1.49    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.04/1.49    inference(flattening,[],[f32])).
% 7.04/1.49  
% 7.04/1.49  fof(f68,plain,(
% 7.04/1.49    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.04/1.49    inference(cnf_transformation,[],[f33])).
% 7.04/1.49  
% 7.04/1.49  fof(f61,plain,(
% 7.04/1.49    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.04/1.49    inference(cnf_transformation,[],[f26])).
% 7.04/1.49  
% 7.04/1.49  fof(f91,plain,(
% 7.04/1.49    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.04/1.49    inference(definition_unfolding,[],[f61,f85])).
% 7.04/1.49  
% 7.04/1.49  fof(f69,plain,(
% 7.04/1.49    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.04/1.49    inference(cnf_transformation,[],[f33])).
% 7.04/1.49  
% 7.04/1.49  fof(f7,axiom,(
% 7.04/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.04/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.04/1.49  
% 7.04/1.49  fof(f22,plain,(
% 7.04/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 7.04/1.49    inference(pure_predicate_removal,[],[f7])).
% 7.04/1.49  
% 7.04/1.49  fof(f28,plain,(
% 7.04/1.49    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.04/1.49    inference(ennf_transformation,[],[f22])).
% 7.04/1.49  
% 7.04/1.49  fof(f63,plain,(
% 7.04/1.49    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.04/1.49    inference(cnf_transformation,[],[f28])).
% 7.04/1.49  
% 7.04/1.49  fof(f12,axiom,(
% 7.04/1.49    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 7.04/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.04/1.49  
% 7.04/1.49  fof(f36,plain,(
% 7.04/1.49    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 7.04/1.49    inference(ennf_transformation,[],[f12])).
% 7.04/1.49  
% 7.04/1.49  fof(f37,plain,(
% 7.04/1.49    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.04/1.49    inference(flattening,[],[f36])).
% 7.04/1.49  
% 7.04/1.49  fof(f50,plain,(
% 7.04/1.49    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.04/1.49    inference(nnf_transformation,[],[f37])).
% 7.04/1.49  
% 7.04/1.49  fof(f76,plain,(
% 7.04/1.49    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.04/1.49    inference(cnf_transformation,[],[f50])).
% 7.04/1.49  
% 7.04/1.49  fof(f90,plain,(
% 7.04/1.49    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))),
% 7.04/1.49    inference(cnf_transformation,[],[f52])).
% 7.04/1.49  
% 7.04/1.49  fof(f14,axiom,(
% 7.04/1.49    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 7.04/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.04/1.49  
% 7.04/1.49  fof(f21,plain,(
% 7.04/1.49    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 7.04/1.49    inference(pure_predicate_removal,[],[f14])).
% 7.04/1.49  
% 7.04/1.49  fof(f82,plain,(
% 7.04/1.49    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 7.04/1.49    inference(cnf_transformation,[],[f21])).
% 7.04/1.49  
% 7.04/1.49  fof(f9,axiom,(
% 7.04/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 7.04/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.04/1.49  
% 7.04/1.49  fof(f30,plain,(
% 7.04/1.49    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 7.04/1.49    inference(ennf_transformation,[],[f9])).
% 7.04/1.49  
% 7.04/1.49  fof(f31,plain,(
% 7.04/1.49    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.04/1.49    inference(flattening,[],[f30])).
% 7.04/1.49  
% 7.04/1.49  fof(f48,plain,(
% 7.04/1.49    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.04/1.49    inference(nnf_transformation,[],[f31])).
% 7.04/1.49  
% 7.04/1.49  fof(f66,plain,(
% 7.04/1.49    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.04/1.49    inference(cnf_transformation,[],[f48])).
% 7.04/1.49  
% 7.04/1.49  fof(f95,plain,(
% 7.04/1.49    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.04/1.49    inference(equality_resolution,[],[f66])).
% 7.04/1.49  
% 7.04/1.49  fof(f2,axiom,(
% 7.04/1.49    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.04/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.04/1.49  
% 7.04/1.49  fof(f46,plain,(
% 7.04/1.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.04/1.49    inference(nnf_transformation,[],[f2])).
% 7.04/1.49  
% 7.04/1.49  fof(f47,plain,(
% 7.04/1.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.04/1.49    inference(flattening,[],[f46])).
% 7.04/1.49  
% 7.04/1.49  fof(f56,plain,(
% 7.04/1.49    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 7.04/1.49    inference(cnf_transformation,[],[f47])).
% 7.04/1.49  
% 7.04/1.49  fof(f93,plain,(
% 7.04/1.49    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 7.04/1.49    inference(equality_resolution,[],[f56])).
% 7.04/1.49  
% 7.04/1.49  fof(f1,axiom,(
% 7.04/1.49    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 7.04/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.04/1.49  
% 7.04/1.49  fof(f23,plain,(
% 7.04/1.49    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 7.04/1.49    inference(ennf_transformation,[],[f1])).
% 7.04/1.49  
% 7.04/1.49  fof(f53,plain,(
% 7.04/1.49    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 7.04/1.49    inference(cnf_transformation,[],[f23])).
% 7.04/1.49  
% 7.04/1.49  fof(f3,axiom,(
% 7.04/1.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.04/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.04/1.49  
% 7.04/1.49  fof(f20,plain,(
% 7.04/1.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 7.04/1.49    inference(unused_predicate_definition_removal,[],[f3])).
% 7.04/1.49  
% 7.04/1.49  fof(f24,plain,(
% 7.04/1.49    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 7.04/1.49    inference(ennf_transformation,[],[f20])).
% 7.04/1.49  
% 7.04/1.49  fof(f57,plain,(
% 7.04/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.04/1.49    inference(cnf_transformation,[],[f24])).
% 7.04/1.49  
% 7.04/1.49  fof(f4,axiom,(
% 7.04/1.49    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 7.04/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.04/1.49  
% 7.04/1.49  fof(f58,plain,(
% 7.04/1.49    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 7.04/1.49    inference(cnf_transformation,[],[f4])).
% 7.04/1.49  
% 7.04/1.49  fof(f55,plain,(
% 7.04/1.49    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 7.04/1.49    inference(cnf_transformation,[],[f47])).
% 7.04/1.49  
% 7.04/1.49  fof(f94,plain,(
% 7.04/1.49    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 7.04/1.49    inference(equality_resolution,[],[f55])).
% 7.04/1.49  
% 7.04/1.49  cnf(c_33,negated_conjecture,
% 7.04/1.49      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 7.04/1.49      inference(cnf_transformation,[],[f89]) ).
% 7.04/1.49  
% 7.04/1.49  cnf(c_1305,plain,
% 7.04/1.49      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 7.04/1.49      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.04/1.49  
% 7.04/1.49  cnf(c_22,plain,
% 7.04/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.04/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.04/1.49      | k1_relset_1(X1,X2,X0) = X1
% 7.04/1.49      | k1_xboole_0 = X2 ),
% 7.04/1.49      inference(cnf_transformation,[],[f70]) ).
% 7.04/1.49  
% 7.04/1.49  cnf(c_1314,plain,
% 7.04/1.49      ( k1_relset_1(X0,X1,X2) = X0
% 7.04/1.49      | k1_xboole_0 = X1
% 7.04/1.49      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.04/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.04/1.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.04/1.49  
% 7.04/1.49  cnf(c_5202,plain,
% 7.04/1.49      ( k1_relset_1(sK0,sK0,sK1) = sK0
% 7.04/1.49      | sK0 = k1_xboole_0
% 7.04/1.49      | v1_funct_2(sK1,sK0,sK0) != iProver_top ),
% 7.04/1.49      inference(superposition,[status(thm)],[c_1305,c_1314]) ).
% 7.04/1.49  
% 7.04/1.49  cnf(c_11,plain,
% 7.04/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.04/1.49      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.04/1.49      inference(cnf_transformation,[],[f64]) ).
% 7.04/1.49  
% 7.04/1.49  cnf(c_1323,plain,
% 7.04/1.49      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.04/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.04/1.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.04/1.49  
% 7.04/1.49  cnf(c_2777,plain,
% 7.04/1.49      ( k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
% 7.04/1.49      inference(superposition,[status(thm)],[c_1305,c_1323]) ).
% 7.04/1.49  
% 7.04/1.49  cnf(c_5212,plain,
% 7.04/1.49      ( k1_relat_1(sK1) = sK0
% 7.04/1.49      | sK0 = k1_xboole_0
% 7.04/1.49      | v1_funct_2(sK1,sK0,sK0) != iProver_top ),
% 7.04/1.49      inference(demodulation,[status(thm)],[c_5202,c_2777]) ).
% 7.04/1.49  
% 7.04/1.49  cnf(c_35,negated_conjecture,
% 7.04/1.49      ( v1_funct_2(sK1,sK0,sK0) ),
% 7.04/1.49      inference(cnf_transformation,[],[f87]) ).
% 7.04/1.49  
% 7.04/1.49  cnf(c_38,plain,
% 7.04/1.49      ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
% 7.04/1.49      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.04/1.49  
% 7.04/1.49  cnf(c_5522,plain,
% 7.04/1.49      ( sK0 = k1_xboole_0 | k1_relat_1(sK1) = sK0 ),
% 7.04/1.49      inference(global_propositional_subsumption,[status(thm)],[c_5212,c_38]) ).
% 7.04/1.49  
% 7.04/1.49  cnf(c_5523,plain,
% 7.04/1.49      ( k1_relat_1(sK1) = sK0 | sK0 = k1_xboole_0 ),
% 7.04/1.49      inference(renaming,[status(thm)],[c_5522]) ).
% 7.04/1.49  
% 7.04/1.49  cnf(c_31,plain,
% 7.04/1.49      ( ~ v1_funct_2(X0,X1,X1)
% 7.04/1.49      | ~ v3_funct_2(X0,X1,X1)
% 7.04/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 7.04/1.49      | ~ v1_funct_1(X0)
% 7.04/1.49      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 7.04/1.49      inference(cnf_transformation,[],[f84]) ).
% 7.04/1.49  
% 7.04/1.49  cnf(c_1307,plain,
% 7.04/1.49      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
% 7.04/1.49      | v1_funct_2(X1,X0,X0) != iProver_top
% 7.04/1.49      | v3_funct_2(X1,X0,X0) != iProver_top
% 7.04/1.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 7.04/1.49      | v1_funct_1(X1) != iProver_top ),
% 7.04/1.49      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.04/1.49  
% 7.04/1.49  cnf(c_7534,plain,
% 7.04/1.49      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
% 7.04/1.49      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 7.04/1.49      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 7.04/1.49      | v1_funct_1(sK1) != iProver_top ),
% 7.04/1.49      inference(superposition,[status(thm)],[c_1305,c_1307]) ).
% 7.04/1.49  
% 7.04/1.49  cnf(c_36,negated_conjecture,
% 7.04/1.49      ( v1_funct_1(sK1) ),
% 7.04/1.49      inference(cnf_transformation,[],[f86]) ).
% 7.04/1.49  
% 7.04/1.49  cnf(c_34,negated_conjecture,
% 7.04/1.49      ( v3_funct_2(sK1,sK0,sK0) ),
% 7.04/1.49      inference(cnf_transformation,[],[f88]) ).
% 7.04/1.49  
% 7.04/1.49  cnf(c_1650,plain,
% 7.04/1.49      ( ~ v1_funct_2(sK1,X0,X0)
% 7.04/1.49      | ~ v3_funct_2(sK1,X0,X0)
% 7.04/1.49      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 7.04/1.49      | ~ v1_funct_1(sK1)
% 7.04/1.49      | k2_funct_2(X0,sK1) = k2_funct_1(sK1) ),
% 7.04/1.49      inference(instantiation,[status(thm)],[c_31]) ).
% 7.04/1.49  
% 7.04/1.49  cnf(c_1813,plain,
% 7.04/1.49      ( ~ v1_funct_2(sK1,sK0,sK0)
% 7.04/1.49      | ~ v3_funct_2(sK1,sK0,sK0)
% 7.04/1.49      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.04/1.49      | ~ v1_funct_1(sK1)
% 7.04/1.49      | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 7.04/1.49      inference(instantiation,[status(thm)],[c_1650]) ).
% 7.04/1.49  
% 7.04/1.49  cnf(c_7803,plain,
% 7.04/1.49      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 7.04/1.49      inference(global_propositional_subsumption,
% 7.04/1.49                [status(thm)],
% 7.04/1.49                [c_7534,c_36,c_35,c_34,c_33,c_1813]) ).
% 7.04/1.49  
% 7.04/1.49  cnf(c_25,plain,
% 7.04/1.49      ( ~ v1_funct_2(X0,X1,X1)
% 7.04/1.49      | ~ v3_funct_2(X0,X1,X1)
% 7.04/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 7.04/1.49      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 7.04/1.49      | ~ v1_funct_1(X0) ),
% 7.04/1.49      inference(cnf_transformation,[],[f81]) ).
% 7.04/1.49  
% 7.04/1.49  cnf(c_1313,plain,
% 7.04/1.49      ( v1_funct_2(X0,X1,X1) != iProver_top
% 7.04/1.49      | v3_funct_2(X0,X1,X1) != iProver_top
% 7.04/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 7.04/1.49      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) = iProver_top
% 7.04/1.49      | v1_funct_1(X0) != iProver_top ),
% 7.04/1.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.04/1.49  
% 7.04/1.49  cnf(c_7824,plain,
% 7.04/1.49      ( v1_funct_2(sK1,sK0,sK0) != iProver_top
% 7.04/1.49      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 7.04/1.49      | m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 7.04/1.49      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 7.04/1.49      | v1_funct_1(sK1) != iProver_top ),
% 7.04/1.49      inference(superposition,[status(thm)],[c_7803,c_1313]) ).
% 7.04/1.49  
% 7.04/1.49  cnf(c_37,plain,
% 7.04/1.49      ( v1_funct_1(sK1) = iProver_top ),
% 7.04/1.49      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.04/1.49  
% 7.04/1.49  cnf(c_39,plain,
% 7.04/1.49      ( v3_funct_2(sK1,sK0,sK0) = iProver_top ),
% 7.04/1.49      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.04/1.49  
% 7.04/1.49  cnf(c_40,plain,
% 7.04/1.49      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 7.04/1.49      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.04/1.49  
% 7.04/1.49  cnf(c_8277,plain,
% 7.04/1.49      ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 7.04/1.49      inference(global_propositional_subsumption,
% 7.04/1.49                [status(thm)],
% 7.04/1.49                [c_7824,c_37,c_38,c_39,c_40]) ).
% 7.04/1.49  
% 7.04/1.49  cnf(c_30,plain,
% 7.04/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.04/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.04/1.49      | ~ v1_funct_1(X0)
% 7.04/1.49      | ~ v1_funct_1(X3)
% 7.04/1.49      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 7.04/1.49      inference(cnf_transformation,[],[f83]) ).
% 7.04/1.49  
% 7.04/1.49  cnf(c_1308,plain,
% 7.04/1.49      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 7.04/1.49      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 7.04/1.49      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.04/1.49      | v1_funct_1(X5) != iProver_top
% 7.04/1.49      | v1_funct_1(X4) != iProver_top ),
% 7.04/1.49      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.04/1.49  
% 7.04/1.49  cnf(c_8832,plain,
% 7.04/1.49      ( k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1))
% 7.04/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.04/1.49      | v1_funct_1(X2) != iProver_top
% 7.04/1.49      | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
% 7.04/1.49      inference(superposition,[status(thm)],[c_8277,c_1308]) ).
% 7.04/1.49  
% 7.04/1.49  cnf(c_28,plain,
% 7.04/1.49      ( ~ v1_funct_2(X0,X1,X1)
% 7.04/1.49      | ~ v3_funct_2(X0,X1,X1)
% 7.04/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 7.04/1.49      | ~ v1_funct_1(X0)
% 7.04/1.49      | v1_funct_1(k2_funct_2(X1,X0)) ),
% 7.04/1.49      inference(cnf_transformation,[],[f78]) ).
% 7.04/1.49  
% 7.04/1.49  cnf(c_1635,plain,
% 7.04/1.49      ( ~ v1_funct_2(sK1,X0,X0)
% 7.04/1.49      | ~ v3_funct_2(sK1,X0,X0)
% 7.04/1.49      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 7.04/1.49      | v1_funct_1(k2_funct_2(X0,sK1))
% 7.04/1.49      | ~ v1_funct_1(sK1) ),
% 7.04/1.49      inference(instantiation,[status(thm)],[c_28]) ).
% 7.04/1.49  
% 7.04/1.49  cnf(c_1803,plain,
% 7.04/1.49      ( ~ v1_funct_2(sK1,sK0,sK0)
% 7.04/1.49      | ~ v3_funct_2(sK1,sK0,sK0)
% 7.04/1.49      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.04/1.49      | v1_funct_1(k2_funct_2(sK0,sK1))
% 7.04/1.49      | ~ v1_funct_1(sK1) ),
% 7.04/1.49      inference(instantiation,[status(thm)],[c_1635]) ).
% 7.04/1.49  
% 7.04/1.49  cnf(c_1804,plain,
% 7.04/1.49      ( v1_funct_2(sK1,sK0,sK0) != iProver_top
% 7.04/1.49      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 7.04/1.49      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 7.04/1.49      | v1_funct_1(k2_funct_2(sK0,sK1)) = iProver_top
% 7.04/1.49      | v1_funct_1(sK1) != iProver_top ),
% 7.04/1.49      inference(predicate_to_equality,[status(thm)],[c_1803]) ).
% 7.04/1.49  
% 7.04/1.49  cnf(c_816,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.04/1.49  
% 7.04/1.49  cnf(c_2347,plain,
% 7.04/1.49      ( X0 != X1 | X0 = k2_funct_2(sK0,sK1) | k2_funct_2(sK0,sK1) != X1 ),
% 7.04/1.49      inference(instantiation,[status(thm)],[c_816]) ).
% 7.04/1.49  
% 7.04/1.49  cnf(c_3149,plain,
% 7.04/1.49      ( X0 = k2_funct_2(sK0,sK1)
% 7.04/1.49      | X0 != k2_funct_1(sK1)
% 7.04/1.49      | k2_funct_2(sK0,sK1) != k2_funct_1(sK1) ),
% 7.04/1.49      inference(instantiation,[status(thm)],[c_2347]) ).
% 7.04/1.49  
% 7.04/1.49  cnf(c_4066,plain,
% 7.04/1.49      ( k2_funct_2(sK0,sK1) != k2_funct_1(sK1)
% 7.04/1.49      | k2_funct_1(sK1) = k2_funct_2(sK0,sK1)
% 7.04/1.49      | k2_funct_1(sK1) != k2_funct_1(sK1) ),
% 7.04/1.49      inference(instantiation,[status(thm)],[c_3149]) ).
% 7.04/1.49  
% 7.04/1.49  cnf(c_815,plain,( X0 = X0 ),theory(equality) ).
% 7.04/1.49  
% 7.04/1.49  cnf(c_4067,plain,
% 7.04/1.49      ( k2_funct_1(sK1) = k2_funct_1(sK1) ),
% 7.04/1.49      inference(instantiation,[status(thm)],[c_815]) ).
% 7.04/1.49  
% 7.04/1.49  cnf(c_824,plain,
% 7.04/1.49      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 7.04/1.49      theory(equality) ).
% 7.04/1.49  
% 7.04/1.49  cnf(c_1875,plain,
% 7.04/1.49      ( v1_funct_1(X0)
% 7.04/1.49      | ~ v1_funct_1(k2_funct_2(sK0,sK1))
% 7.04/1.49      | X0 != k2_funct_2(sK0,sK1) ),
% 7.04/1.49      inference(instantiation,[status(thm)],[c_824]) ).
% 7.04/1.49  
% 7.04/1.49  cnf(c_7621,plain,
% 7.04/1.49      ( ~ v1_funct_1(k2_funct_2(sK0,sK1))
% 7.04/1.49      | v1_funct_1(k2_funct_1(sK1))
% 7.04/1.49      | k2_funct_1(sK1) != k2_funct_2(sK0,sK1) ),
% 7.04/1.49      inference(instantiation,[status(thm)],[c_1875]) ).
% 7.04/1.49  
% 7.04/1.49  cnf(c_7622,plain,
% 7.04/1.49      ( k2_funct_1(sK1) != k2_funct_2(sK0,sK1)
% 7.04/1.49      | v1_funct_1(k2_funct_2(sK0,sK1)) != iProver_top
% 7.04/1.49      | v1_funct_1(k2_funct_1(sK1)) = iProver_top ),
% 7.04/1.49      inference(predicate_to_equality,[status(thm)],[c_7621]) ).
% 7.04/1.49  
% 7.04/1.49  cnf(c_13521,plain,
% 7.04/1.49      ( v1_funct_1(X2) != iProver_top
% 7.04/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.04/1.49      | k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1)) ),
% 7.04/1.49      inference(global_propositional_subsumption,
% 7.04/1.49                [status(thm)],
% 7.04/1.49                [c_8832,c_36,c_37,c_35,c_38,c_34,c_39,c_33,c_40,c_1804,
% 7.04/1.49                 c_1813,c_4066,c_4067,c_7622]) ).
% 7.04/1.49  
% 7.04/1.49  cnf(c_13522,plain,
% 7.04/1.49      ( k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1))
% 7.04/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.04/1.49      | v1_funct_1(X2) != iProver_top ),
% 7.04/1.49      inference(renaming,[status(thm)],[c_13521]) ).
% 7.04/1.49  
% 7.04/1.49  cnf(c_13532,plain,
% 7.04/1.49      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k5_relat_1(sK1,k2_funct_1(sK1))
% 7.04/1.49      | v1_funct_1(sK1) != iProver_top ),
% 7.04/1.49      inference(superposition,[status(thm)],[c_1305,c_13522]) ).
% 7.04/1.49  
% 7.04/1.49  cnf(c_9,plain,
% 7.04/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 7.04/1.49      inference(cnf_transformation,[],[f62]) ).
% 7.04/1.49  
% 7.04/1.49  cnf(c_1324,plain,
% 7.04/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.04/1.49      | v1_relat_1(X0) = iProver_top ),
% 7.04/1.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.04/1.49  
% 7.04/1.49  cnf(c_1965,plain,
% 7.04/1.49      ( v1_relat_1(sK1) = iProver_top ),
% 7.04/1.49      inference(superposition,[status(thm)],[c_1305,c_1324]) ).
% 7.04/1.49  
% 7.04/1.49  cnf(c_8,plain,
% 7.04/1.49      ( ~ v1_relat_1(X0)
% 7.04/1.49      | ~ v1_funct_1(X0)
% 7.04/1.49      | ~ v2_funct_1(X0)
% 7.04/1.49      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
% 7.04/1.49      inference(cnf_transformation,[],[f92]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_1325,plain,
% 7.04/1.50      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
% 7.04/1.50      | v1_relat_1(X0) != iProver_top
% 7.04/1.50      | v1_funct_1(X0) != iProver_top
% 7.04/1.50      | v2_funct_1(X0) != iProver_top ),
% 7.04/1.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_3792,plain,
% 7.04/1.50      ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
% 7.04/1.50      | v1_funct_1(sK1) != iProver_top
% 7.04/1.50      | v2_funct_1(sK1) != iProver_top ),
% 7.04/1.50      inference(superposition,[status(thm)],[c_1965,c_1325]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_1582,plain,
% 7.04/1.50      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.04/1.50      | v1_relat_1(sK1) ),
% 7.04/1.50      inference(instantiation,[status(thm)],[c_9]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_1677,plain,
% 7.04/1.50      ( ~ v1_relat_1(sK1)
% 7.04/1.50      | ~ v1_funct_1(sK1)
% 7.04/1.50      | ~ v2_funct_1(sK1)
% 7.04/1.50      | k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
% 7.04/1.50      inference(instantiation,[status(thm)],[c_8]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_15,plain,
% 7.04/1.50      ( ~ v3_funct_2(X0,X1,X2)
% 7.04/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.04/1.50      | ~ v1_funct_1(X0)
% 7.04/1.50      | v2_funct_1(X0) ),
% 7.04/1.50      inference(cnf_transformation,[],[f68]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_1616,plain,
% 7.04/1.50      ( ~ v3_funct_2(sK1,X0,X1)
% 7.04/1.50      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.04/1.50      | ~ v1_funct_1(sK1)
% 7.04/1.50      | v2_funct_1(sK1) ),
% 7.04/1.50      inference(instantiation,[status(thm)],[c_15]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_1739,plain,
% 7.04/1.50      ( ~ v3_funct_2(sK1,sK0,sK0)
% 7.04/1.50      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.04/1.50      | ~ v1_funct_1(sK1)
% 7.04/1.50      | v2_funct_1(sK1) ),
% 7.04/1.50      inference(instantiation,[status(thm)],[c_1616]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_3818,plain,
% 7.04/1.50      ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
% 7.04/1.50      inference(global_propositional_subsumption,
% 7.04/1.50                [status(thm)],
% 7.04/1.50                [c_3792,c_36,c_34,c_33,c_1582,c_1677,c_1739]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_13554,plain,
% 7.04/1.50      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
% 7.04/1.50      | v1_funct_1(sK1) != iProver_top ),
% 7.04/1.50      inference(light_normalisation,[status(thm)],[c_13532,c_3818]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_13586,plain,
% 7.04/1.50      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
% 7.04/1.50      inference(global_propositional_subsumption,[status(thm)],[c_13554,c_37]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_8831,plain,
% 7.04/1.50      ( k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1)
% 7.04/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.04/1.50      | v1_funct_1(X2) != iProver_top
% 7.04/1.50      | v1_funct_1(sK1) != iProver_top ),
% 7.04/1.50      inference(superposition,[status(thm)],[c_1305,c_1308]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_9376,plain,
% 7.04/1.50      ( v1_funct_1(X2) != iProver_top
% 7.04/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.04/1.50      | k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1) ),
% 7.04/1.50      inference(global_propositional_subsumption,[status(thm)],[c_8831,c_37]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_9377,plain,
% 7.04/1.50      ( k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1)
% 7.04/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.04/1.50      | v1_funct_1(X2) != iProver_top ),
% 7.04/1.50      inference(renaming,[status(thm)],[c_9376]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_9385,plain,
% 7.04/1.50      ( k1_partfun1(X0,X0,sK0,sK0,k2_funct_2(X0,X1),sK1) = k5_relat_1(k2_funct_2(X0,X1),sK1)
% 7.04/1.50      | v1_funct_2(X1,X0,X0) != iProver_top
% 7.04/1.50      | v3_funct_2(X1,X0,X0) != iProver_top
% 7.04/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 7.04/1.50      | v1_funct_1(X1) != iProver_top
% 7.04/1.50      | v1_funct_1(k2_funct_2(X0,X1)) != iProver_top ),
% 7.04/1.50      inference(superposition,[status(thm)],[c_1313,c_9377]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_1310,plain,
% 7.04/1.50      ( v1_funct_2(X0,X1,X1) != iProver_top
% 7.04/1.50      | v3_funct_2(X0,X1,X1) != iProver_top
% 7.04/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 7.04/1.50      | v1_funct_1(X0) != iProver_top
% 7.04/1.50      | v1_funct_1(k2_funct_2(X1,X0)) = iProver_top ),
% 7.04/1.50      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_11079,plain,
% 7.04/1.50      ( k1_partfun1(X0,X0,sK0,sK0,k2_funct_2(X0,X1),sK1) = k5_relat_1(k2_funct_2(X0,X1),sK1)
% 7.04/1.50      | v1_funct_2(X1,X0,X0) != iProver_top
% 7.04/1.50      | v3_funct_2(X1,X0,X0) != iProver_top
% 7.04/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 7.04/1.50      | v1_funct_1(X1) != iProver_top ),
% 7.04/1.50      inference(forward_subsumption_resolution,[status(thm)],[c_9385,c_1310]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_11085,plain,
% 7.04/1.50      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1) = k5_relat_1(k2_funct_2(sK0,sK1),sK1)
% 7.04/1.50      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 7.04/1.50      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 7.04/1.50      | v1_funct_1(sK1) != iProver_top ),
% 7.04/1.50      inference(superposition,[status(thm)],[c_1305,c_11079]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_7,plain,
% 7.04/1.50      ( ~ v1_relat_1(X0)
% 7.04/1.50      | ~ v1_funct_1(X0)
% 7.04/1.50      | ~ v2_funct_1(X0)
% 7.04/1.50      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
% 7.04/1.50      inference(cnf_transformation,[],[f91]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_1326,plain,
% 7.04/1.50      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
% 7.04/1.50      | v1_relat_1(X0) != iProver_top
% 7.04/1.50      | v1_funct_1(X0) != iProver_top
% 7.04/1.50      | v2_funct_1(X0) != iProver_top ),
% 7.04/1.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_4100,plain,
% 7.04/1.50      ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1))
% 7.04/1.50      | v1_funct_1(sK1) != iProver_top
% 7.04/1.50      | v2_funct_1(sK1) != iProver_top ),
% 7.04/1.50      inference(superposition,[status(thm)],[c_1965,c_1326]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_14,plain,
% 7.04/1.50      ( ~ v3_funct_2(X0,X1,X2)
% 7.04/1.50      | v2_funct_2(X0,X2)
% 7.04/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.04/1.50      | ~ v1_funct_1(X0) ),
% 7.04/1.50      inference(cnf_transformation,[],[f69]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_10,plain,
% 7.04/1.50      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 7.04/1.50      inference(cnf_transformation,[],[f63]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_24,plain,
% 7.04/1.50      ( ~ v2_funct_2(X0,X1)
% 7.04/1.50      | ~ v5_relat_1(X0,X1)
% 7.04/1.50      | ~ v1_relat_1(X0)
% 7.04/1.50      | k2_relat_1(X0) = X1 ),
% 7.04/1.50      inference(cnf_transformation,[],[f76]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_384,plain,
% 7.04/1.50      ( ~ v2_funct_2(X0,X1)
% 7.04/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 7.04/1.50      | ~ v1_relat_1(X0)
% 7.04/1.50      | k2_relat_1(X0) = X1 ),
% 7.04/1.50      inference(resolution,[status(thm)],[c_10,c_24]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_394,plain,
% 7.04/1.50      ( ~ v2_funct_2(X0,X1)
% 7.04/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 7.04/1.50      | k2_relat_1(X0) = X1 ),
% 7.04/1.50      inference(forward_subsumption_resolution,[status(thm)],[c_384,c_9]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_465,plain,
% 7.04/1.50      ( ~ v3_funct_2(X0,X1,X2)
% 7.04/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.04/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.04/1.50      | ~ v1_funct_1(X0)
% 7.04/1.50      | X3 != X0
% 7.04/1.50      | X5 != X2
% 7.04/1.50      | k2_relat_1(X3) = X5 ),
% 7.04/1.50      inference(resolution_lifted,[status(thm)],[c_14,c_394]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_466,plain,
% 7.04/1.50      ( ~ v3_funct_2(X0,X1,X2)
% 7.04/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.04/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 7.04/1.50      | ~ v1_funct_1(X0)
% 7.04/1.50      | k2_relat_1(X0) = X2 ),
% 7.04/1.50      inference(unflattening,[status(thm)],[c_465]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_1300,plain,
% 7.04/1.50      ( k2_relat_1(X0) = X1
% 7.04/1.50      | v3_funct_2(X0,X2,X1) != iProver_top
% 7.04/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 7.04/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
% 7.04/1.50      | v1_funct_1(X0) != iProver_top ),
% 7.04/1.50      inference(predicate_to_equality,[status(thm)],[c_466]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_2244,plain,
% 7.04/1.50      ( k2_relat_1(sK1) = sK0
% 7.04/1.50      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 7.04/1.50      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 7.04/1.50      | v1_funct_1(sK1) != iProver_top ),
% 7.04/1.50      inference(superposition,[status(thm)],[c_1305,c_1300]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_2604,plain,
% 7.04/1.50      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 7.04/1.50      | k2_relat_1(sK1) = sK0 ),
% 7.04/1.50      inference(global_propositional_subsumption,
% 7.04/1.50                [status(thm)],
% 7.04/1.50                [c_2244,c_37,c_39]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_2605,plain,
% 7.04/1.50      ( k2_relat_1(sK1) = sK0
% 7.04/1.50      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top ),
% 7.04/1.50      inference(renaming,[status(thm)],[c_2604]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_2612,plain,
% 7.04/1.50      ( k2_relat_1(sK1) = sK0 ),
% 7.04/1.50      inference(superposition,[status(thm)],[c_1305,c_2605]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_4104,plain,
% 7.04/1.50      ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
% 7.04/1.50      | v1_funct_1(sK1) != iProver_top
% 7.04/1.50      | v2_funct_1(sK1) != iProver_top ),
% 7.04/1.50      inference(light_normalisation,[status(thm)],[c_4100,c_2612]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_1740,plain,
% 7.04/1.50      ( v3_funct_2(sK1,sK0,sK0) != iProver_top
% 7.04/1.50      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 7.04/1.50      | v1_funct_1(sK1) != iProver_top
% 7.04/1.50      | v2_funct_1(sK1) = iProver_top ),
% 7.04/1.50      inference(predicate_to_equality,[status(thm)],[c_1739]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_4260,plain,
% 7.04/1.50      ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(sK0) ),
% 7.04/1.50      inference(global_propositional_subsumption,
% 7.04/1.50                [status(thm)],
% 7.04/1.50                [c_4104,c_37,c_39,c_40,c_1740]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_11111,plain,
% 7.04/1.50      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
% 7.04/1.50      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 7.04/1.50      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 7.04/1.50      | v1_funct_1(sK1) != iProver_top ),
% 7.04/1.50      inference(light_normalisation,[status(thm)],[c_11085,c_4260,c_7803]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_9388,plain,
% 7.04/1.50      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k5_relat_1(k2_funct_1(sK1),sK1)
% 7.04/1.50      | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
% 7.04/1.50      inference(superposition,[status(thm)],[c_8277,c_9377]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_9405,plain,
% 7.04/1.50      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
% 7.04/1.50      | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
% 7.04/1.50      inference(light_normalisation,[status(thm)],[c_9388,c_4260]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_11359,plain,
% 7.04/1.50      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0) ),
% 7.04/1.50      inference(global_propositional_subsumption,
% 7.04/1.50                [status(thm)],
% 7.04/1.50                [c_11111,c_36,c_37,c_35,c_38,c_34,c_39,c_33,c_40,c_1804,
% 7.04/1.50                 c_1813,c_4066,c_4067,c_7622,c_9405]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_32,negated_conjecture,
% 7.04/1.50      ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
% 7.04/1.50      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
% 7.04/1.50      inference(cnf_transformation,[],[f90]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_1306,plain,
% 7.04/1.50      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) != iProver_top
% 7.04/1.50      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) != iProver_top ),
% 7.04/1.50      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_7809,plain,
% 7.04/1.50      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) != iProver_top
% 7.04/1.50      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
% 7.04/1.50      inference(demodulation,[status(thm)],[c_7803,c_1306]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_11362,plain,
% 7.04/1.50      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top
% 7.04/1.50      | r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
% 7.04/1.50      inference(demodulation,[status(thm)],[c_11359,c_7809]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_29,plain,
% 7.04/1.50      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 7.04/1.50      inference(cnf_transformation,[],[f82]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_4079,plain,
% 7.04/1.50      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 7.04/1.50      inference(instantiation,[status(thm)],[c_29]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_4080,plain,
% 7.04/1.50      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 7.04/1.50      inference(predicate_to_equality,[status(thm)],[c_4079]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_12,plain,
% 7.04/1.50      ( r2_relset_1(X0,X1,X2,X2)
% 7.04/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 7.04/1.50      inference(cnf_transformation,[],[f95]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_1608,plain,
% 7.04/1.50      ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0))
% 7.04/1.50      | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 7.04/1.50      inference(instantiation,[status(thm)],[c_12]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_6664,plain,
% 7.04/1.50      ( r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
% 7.04/1.50      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 7.04/1.50      inference(instantiation,[status(thm)],[c_1608]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_6665,plain,
% 7.04/1.50      ( r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) = iProver_top
% 7.04/1.50      | m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 7.04/1.50      inference(predicate_to_equality,[status(thm)],[c_6664]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_11365,plain,
% 7.04/1.50      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
% 7.04/1.50      inference(global_propositional_subsumption,
% 7.04/1.50                [status(thm)],
% 7.04/1.50                [c_11362,c_4080,c_6665]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_13589,plain,
% 7.04/1.50      ( r2_relset_1(sK0,sK0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
% 7.04/1.50      inference(demodulation,[status(thm)],[c_13586,c_11365]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_13942,plain,
% 7.04/1.50      ( sK0 = k1_xboole_0
% 7.04/1.50      | r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
% 7.04/1.50      inference(superposition,[status(thm)],[c_5523,c_13589]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_15005,plain,
% 7.04/1.50      ( sK0 = k1_xboole_0 ),
% 7.04/1.50      inference(global_propositional_subsumption,
% 7.04/1.50                [status(thm)],
% 7.04/1.50                [c_13942,c_4080,c_6665]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_15011,plain,
% 7.04/1.50      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(k1_xboole_0)) != iProver_top ),
% 7.04/1.50      inference(demodulation,[status(thm)],[c_15005,c_13589]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_1,plain,
% 7.04/1.50      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.04/1.50      inference(cnf_transformation,[],[f93]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_1309,plain,
% 7.04/1.50      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 7.04/1.50      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_1808,plain,
% 7.04/1.50      ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 7.04/1.50      inference(superposition,[status(thm)],[c_1,c_1309]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_0,plain,
% 7.04/1.50      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 7.04/1.50      inference(cnf_transformation,[],[f53]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_4,plain,
% 7.04/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.04/1.50      inference(cnf_transformation,[],[f57]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_369,plain,
% 7.04/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.04/1.50      | X0 != X2
% 7.04/1.50      | k1_xboole_0 != X1
% 7.04/1.50      | k1_xboole_0 = X2 ),
% 7.04/1.50      inference(resolution_lifted,[status(thm)],[c_0,c_4]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_370,plain,
% 7.04/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0 ),
% 7.04/1.50      inference(unflattening,[status(thm)],[c_369]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_1301,plain,
% 7.04/1.50      ( k1_xboole_0 = X0
% 7.04/1.50      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 7.04/1.50      inference(predicate_to_equality,[status(thm)],[c_370]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_1915,plain,
% 7.04/1.50      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 7.04/1.50      inference(superposition,[status(thm)],[c_1808,c_1301]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_15271,plain,
% 7.04/1.50      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_relat_1(sK1)),k1_xboole_0) != iProver_top ),
% 7.04/1.50      inference(light_normalisation,[status(thm)],[c_15011,c_1915]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_6,plain,
% 7.04/1.50      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.04/1.50      inference(cnf_transformation,[],[f58]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_15057,plain,
% 7.04/1.50      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 7.04/1.50      inference(demodulation,[status(thm)],[c_15005,c_1305]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_2,plain,
% 7.04/1.50      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.04/1.50      inference(cnf_transformation,[],[f94]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_15065,plain,
% 7.04/1.50      ( m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 7.04/1.50      inference(demodulation,[status(thm)],[c_15057,c_2]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_15585,plain,
% 7.04/1.50      ( sK1 = k1_xboole_0 ),
% 7.04/1.50      inference(superposition,[status(thm)],[c_15065,c_1301]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_24173,plain,
% 7.04/1.50      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 7.04/1.50      inference(light_normalisation,[status(thm)],[c_15271,c_6,c_1915,c_15585]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_1322,plain,
% 7.04/1.50      ( r2_relset_1(X0,X1,X2,X2) = iProver_top
% 7.04/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.04/1.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_2381,plain,
% 7.04/1.50      ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0)) = iProver_top ),
% 7.04/1.50      inference(superposition,[status(thm)],[c_1309,c_1322]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_2735,plain,
% 7.04/1.50      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 7.04/1.50      inference(superposition,[status(thm)],[c_1915,c_2381]) ).
% 7.04/1.50  
% 7.04/1.50  cnf(c_24175,plain,
% 7.04/1.50      ( $false ),
% 7.04/1.50      inference(forward_subsumption_resolution,[status(thm)],[c_24173,c_2735]) ).
% 7.04/1.50  
% 7.04/1.50  
% 7.04/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.04/1.50  
% 7.04/1.50  ------                               Statistics
% 7.04/1.50  
% 7.04/1.50  ------ General
% 7.04/1.50  
% 7.04/1.50  abstr_ref_over_cycles:                  0
% 7.04/1.50  abstr_ref_under_cycles:                 0
% 7.04/1.50  gc_basic_clause_elim:                   0
% 7.04/1.50  forced_gc_time:                         0
% 7.04/1.50  parsing_time:                           0.009
% 7.04/1.50  unif_index_cands_time:                  0.
% 7.04/1.50  unif_index_add_time:                    0.
% 7.04/1.50  orderings_time:                         0.
% 7.04/1.50  out_proof_time:                         0.014
% 7.04/1.50  total_time:                             0.691
% 7.04/1.50  num_of_symbols:                         54
% 7.04/1.50  num_of_terms:                           22714
% 7.04/1.50  
% 7.04/1.50  ------ Preprocessing
% 7.04/1.50  
% 7.04/1.50  num_of_splits:                          0
% 7.04/1.50  num_of_split_atoms:                     0
% 7.04/1.50  num_of_reused_defs:                     0
% 7.04/1.50  num_eq_ax_congr_red:                    18
% 7.04/1.50  num_of_sem_filtered_clauses:            1
% 7.04/1.50  num_of_subtypes:                        0
% 7.04/1.50  monotx_restored_types:                  0
% 7.04/1.50  sat_num_of_epr_types:                   0
% 7.04/1.50  sat_num_of_non_cyclic_types:            0
% 7.04/1.50  sat_guarded_non_collapsed_types:        0
% 7.04/1.50  num_pure_diseq_elim:                    0
% 7.04/1.50  simp_replaced_by:                       0
% 7.04/1.50  res_preprocessed:                       165
% 7.04/1.50  prep_upred:                             0
% 7.04/1.50  prep_unflattend:                        8
% 7.04/1.50  smt_new_axioms:                         0
% 7.04/1.50  pred_elim_cands:                        7
% 7.04/1.50  pred_elim:                              3
% 7.04/1.50  pred_elim_cl:                           4
% 7.04/1.50  pred_elim_cycles:                       7
% 7.04/1.50  merged_defs:                            0
% 7.04/1.50  merged_defs_ncl:                        0
% 7.04/1.50  bin_hyper_res:                          0
% 7.04/1.50  prep_cycles:                            4
% 7.04/1.50  pred_elim_time:                         0.006
% 7.04/1.50  splitting_time:                         0.
% 7.04/1.50  sem_filter_time:                        0.
% 7.04/1.50  monotx_time:                            0.001
% 7.04/1.50  subtype_inf_time:                       0.
% 7.04/1.50  
% 7.04/1.50  ------ Problem properties
% 7.04/1.50  
% 7.04/1.50  clauses:                                32
% 7.04/1.50  conjectures:                            5
% 7.04/1.50  epr:                                    3
% 7.04/1.50  horn:                                   27
% 7.04/1.50  ground:                                 7
% 7.04/1.50  unary:                                  9
% 7.04/1.50  binary:                                 5
% 7.04/1.50  lits:                                   94
% 7.04/1.50  lits_eq:                                24
% 7.04/1.50  fd_pure:                                0
% 7.04/1.50  fd_pseudo:                              0
% 7.04/1.50  fd_cond:                                5
% 7.04/1.50  fd_pseudo_cond:                         2
% 7.04/1.50  ac_symbols:                             0
% 7.04/1.50  
% 7.04/1.50  ------ Propositional Solver
% 7.04/1.50  
% 7.04/1.50  prop_solver_calls:                      30
% 7.04/1.50  prop_fast_solver_calls:                 2244
% 7.04/1.50  smt_solver_calls:                       0
% 7.04/1.50  smt_fast_solver_calls:                  0
% 7.04/1.50  prop_num_of_clauses:                    8527
% 7.04/1.50  prop_preprocess_simplified:             17728
% 7.04/1.50  prop_fo_subsumed:                       152
% 7.04/1.50  prop_solver_time:                       0.
% 7.04/1.50  smt_solver_time:                        0.
% 7.04/1.50  smt_fast_solver_time:                   0.
% 7.04/1.50  prop_fast_solver_time:                  0.
% 7.04/1.50  prop_unsat_core_time:                   0.
% 7.04/1.50  
% 7.04/1.50  ------ QBF
% 7.04/1.50  
% 7.04/1.50  qbf_q_res:                              0
% 7.04/1.50  qbf_num_tautologies:                    0
% 7.04/1.50  qbf_prep_cycles:                        0
% 7.04/1.50  
% 7.04/1.50  ------ BMC1
% 7.04/1.50  
% 7.04/1.50  bmc1_current_bound:                     -1
% 7.04/1.50  bmc1_last_solved_bound:                 -1
% 7.04/1.50  bmc1_unsat_core_size:                   -1
% 7.04/1.50  bmc1_unsat_core_parents_size:           -1
% 7.04/1.50  bmc1_merge_next_fun:                    0
% 7.04/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.04/1.50  
% 7.04/1.50  ------ Instantiation
% 7.04/1.50  
% 7.04/1.50  inst_num_of_clauses:                    2978
% 7.04/1.50  inst_num_in_passive:                    554
% 7.04/1.50  inst_num_in_active:                     1091
% 7.04/1.50  inst_num_in_unprocessed:                1333
% 7.04/1.50  inst_num_of_loops:                      1130
% 7.04/1.50  inst_num_of_learning_restarts:          0
% 7.04/1.50  inst_num_moves_active_passive:          36
% 7.04/1.50  inst_lit_activity:                      0
% 7.04/1.50  inst_lit_activity_moves:                0
% 7.04/1.50  inst_num_tautologies:                   0
% 7.04/1.50  inst_num_prop_implied:                  0
% 7.04/1.50  inst_num_existing_simplified:           0
% 7.04/1.50  inst_num_eq_res_simplified:             0
% 7.04/1.50  inst_num_child_elim:                    0
% 7.04/1.50  inst_num_of_dismatching_blockings:      810
% 7.04/1.50  inst_num_of_non_proper_insts:           2791
% 7.04/1.50  inst_num_of_duplicates:                 0
% 7.04/1.50  inst_inst_num_from_inst_to_res:         0
% 7.04/1.50  inst_dismatching_checking_time:         0.
% 7.04/1.50  
% 7.04/1.50  ------ Resolution
% 7.04/1.50  
% 7.04/1.50  res_num_of_clauses:                     0
% 7.04/1.50  res_num_in_passive:                     0
% 7.04/1.50  res_num_in_active:                      0
% 7.04/1.50  res_num_of_loops:                       169
% 7.04/1.50  res_forward_subset_subsumed:            62
% 7.04/1.50  res_backward_subset_subsumed:           2
% 7.04/1.50  res_forward_subsumed:                   0
% 7.04/1.50  res_backward_subsumed:                  0
% 7.04/1.50  res_forward_subsumption_resolution:     2
% 7.04/1.50  res_backward_subsumption_resolution:    0
% 7.04/1.50  res_clause_to_clause_subsumption:       2359
% 7.04/1.50  res_orphan_elimination:                 0
% 7.04/1.50  res_tautology_del:                      57
% 7.04/1.50  res_num_eq_res_simplified:              0
% 7.04/1.50  res_num_sel_changes:                    0
% 7.04/1.50  res_moves_from_active_to_pass:          0
% 7.04/1.50  
% 7.04/1.50  ------ Superposition
% 7.04/1.50  
% 7.04/1.50  sup_time_total:                         0.
% 7.04/1.50  sup_time_generating:                    0.
% 7.04/1.50  sup_time_sim_full:                      0.
% 7.04/1.50  sup_time_sim_immed:                     0.
% 7.04/1.50  
% 7.04/1.50  sup_num_of_clauses:                     229
% 7.04/1.50  sup_num_in_active:                      123
% 7.04/1.50  sup_num_in_passive:                     106
% 7.04/1.50  sup_num_of_loops:                       224
% 7.04/1.50  sup_fw_superposition:                   323
% 7.04/1.50  sup_bw_superposition:                   108
% 7.04/1.50  sup_immediate_simplified:               152
% 7.04/1.50  sup_given_eliminated:                   11
% 7.04/1.50  comparisons_done:                       0
% 7.04/1.50  comparisons_avoided:                    0
% 7.04/1.50  
% 7.04/1.50  ------ Simplifications
% 7.04/1.50  
% 7.04/1.50  
% 7.04/1.50  sim_fw_subset_subsumed:                 31
% 7.04/1.50  sim_bw_subset_subsumed:                 25
% 7.04/1.50  sim_fw_subsumed:                        33
% 7.04/1.50  sim_bw_subsumed:                        11
% 7.04/1.50  sim_fw_subsumption_res:                 11
% 7.04/1.50  sim_bw_subsumption_res:                 0
% 7.04/1.50  sim_tautology_del:                      7
% 7.04/1.50  sim_eq_tautology_del:                   86
% 7.04/1.50  sim_eq_res_simp:                        1
% 7.04/1.50  sim_fw_demodulated:                     36
% 7.04/1.50  sim_bw_demodulated:                     99
% 7.04/1.50  sim_light_normalised:                   163
% 7.04/1.50  sim_joinable_taut:                      0
% 7.04/1.50  sim_joinable_simp:                      0
% 7.04/1.50  sim_ac_normalised:                      0
% 7.04/1.50  sim_smt_subsumption:                    0
% 7.04/1.50  
%------------------------------------------------------------------------------
