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
% DateTime   : Thu Dec  3 12:07:22 EST 2020

% Result     : Theorem 3.23s
% Output     : CNFRefutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :  195 (3475 expanded)
%              Number of clauses        :  120 (1030 expanded)
%              Number of leaves         :   17 ( 679 expanded)
%              Depth                    :   27
%              Number of atoms          :  645 (16205 expanded)
%              Number of equality atoms :  304 (1892 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   13 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f41,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f42,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f41])).

fof(f46,plain,
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

fof(f47,plain,
    ( ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) )
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK1,sK0,sK0)
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f42,f46])).

fof(f81,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f47])).

fof(f9,axiom,(
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

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f79,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_1(X1) = k2_funct_2(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f78,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f80,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f11,axiom,(
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

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f75,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k2_funct_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f23,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f52,plain,(
    ! [X0] :
      ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f15,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f86,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f52,f77])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f29])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f53,plain,(
    ! [X0] :
      ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f85,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f53,f77])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f82,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f47])).

fof(f12,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f74,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f27])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f87,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f58])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_relat_1(X0) = k1_xboole_0 )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f49,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f84,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f50,f77])).

fof(f48,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_relat_1(X0) != k1_xboole_0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1370,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1379,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4492,plain,
    ( k1_relset_1(sK0,sK0,sK1) = sK0
    | sK0 = k1_xboole_0
    | v1_funct_2(sK1,sK0,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1370,c_1379])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1388,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2902,plain,
    ( k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_1370,c_1388])).

cnf(c_4497,plain,
    ( k1_relat_1(sK1) = sK0
    | sK0 = k1_xboole_0
    | v1_funct_2(sK1,sK0,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4492,c_2902])).

cnf(c_32,negated_conjecture,
    ( v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_35,plain,
    ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_5810,plain,
    ( sK0 = k1_xboole_0
    | k1_relat_1(sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4497,c_35])).

cnf(c_5811,plain,
    ( k1_relat_1(sK1) = sK0
    | sK0 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_5810])).

cnf(c_28,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1372,plain,
    ( k2_funct_2(X0,X1) = k2_funct_1(X1)
    | v1_funct_2(X1,X0,X0) != iProver_top
    | v3_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2649,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1370,c_1372])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_31,negated_conjecture,
    ( v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1729,plain,
    ( ~ v1_funct_2(sK1,X0,X0)
    | ~ v3_funct_2(sK1,X0,X0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v1_funct_1(sK1)
    | k2_funct_2(X0,sK1) = k2_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_1919,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1729])).

cnf(c_3146,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2649,c_33,c_32,c_31,c_30,c_1919])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1378,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_6156,plain,
    ( v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3146,c_1378])).

cnf(c_34,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_36,plain,
    ( v3_funct_2(sK1,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_37,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_7367,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6156,c_34,c_35,c_36,c_37])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1373,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_7383,plain,
    ( k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7367,c_1373])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_2(X1,X0)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1375,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_2(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_4454,plain,
    ( v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(k2_funct_2(sK0,sK1)) = iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1370,c_1375])).

cnf(c_4468,plain,
    ( v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(k2_funct_1(sK1)) = iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4454,c_3146])).

cnf(c_9021,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7383,c_34,c_35,c_36,c_4468])).

cnf(c_9022,plain,
    ( k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_9021])).

cnf(c_9032,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k5_relat_1(sK1,k2_funct_1(sK1))
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1370,c_9022])).

cnf(c_1367,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_5,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1390,plain,
    ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3622,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
    | v2_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1367,c_1390])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1646,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1661,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_12,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1690,plain,
    ( ~ v3_funct_2(sK1,X0,X1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK1)
    | v2_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1829,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | v2_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_1690])).

cnf(c_3801,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3622,c_33,c_31,c_30,c_1646,c_1661,c_1829])).

cnf(c_9045,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
    | v1_funct_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9032,c_3801])).

cnf(c_9074,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9045,c_34])).

cnf(c_3439,plain,
    ( k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1370,c_1373])).

cnf(c_3805,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3439,c_34])).

cnf(c_3806,plain,
    ( k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_3805])).

cnf(c_6161,plain,
    ( k1_partfun1(X0,X0,sK0,sK0,k2_funct_2(X0,X1),sK1) = k5_relat_1(k2_funct_2(X0,X1),sK1)
    | v1_funct_2(X1,X0,X0) != iProver_top
    | v3_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(k2_funct_2(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1378,c_3806])).

cnf(c_7643,plain,
    ( k1_partfun1(X0,X0,sK0,sK0,k2_funct_2(X0,X1),sK1) = k5_relat_1(k2_funct_2(X0,X1),sK1)
    | v1_funct_2(X1,X0,X0) != iProver_top
    | v3_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6161,c_1375])).

cnf(c_7649,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1) = k5_relat_1(k2_funct_2(sK0,sK1),sK1)
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1370,c_7643])).

cnf(c_4,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1391,plain,
    ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4293,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1))
    | v2_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1367,c_1391])).

cnf(c_11,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_7,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_21,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_363,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_7,c_21])).

cnf(c_375,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | k2_relat_1(X0) = X1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_363,c_6])).

cnf(c_406,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | X3 != X0
    | X5 != X2
    | k2_relat_1(X3) = X5 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_375])).

cnf(c_407,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(unflattening,[status(thm)],[c_406])).

cnf(c_1366,plain,
    ( k2_relat_1(X0) = X1
    | v3_funct_2(X0,X2,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_407])).

cnf(c_1764,plain,
    ( k2_relat_1(sK1) = sK0
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1370,c_1366])).

cnf(c_1710,plain,
    ( ~ v3_funct_2(sK1,X0,X1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(sK1)
    | k2_relat_1(sK1) = X1 ),
    inference(instantiation,[status(thm)],[c_407])).

cnf(c_1915,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | k2_relat_1(sK1) = sK0 ),
    inference(instantiation,[status(thm)],[c_1710])).

cnf(c_2036,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | k2_relat_1(sK1) = sK0 ),
    inference(instantiation,[status(thm)],[c_1915])).

cnf(c_2198,plain,
    ( k2_relat_1(sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1764,c_33,c_31,c_30,c_2036])).

cnf(c_4294,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
    | v2_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4293,c_2198])).

cnf(c_1647,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1646])).

cnf(c_1830,plain,
    ( v3_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v2_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1829])).

cnf(c_5445,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4294,c_34,c_36,c_37,c_1647,c_1830])).

cnf(c_7672,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7649,c_3146,c_5445])).

cnf(c_7376,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k5_relat_1(k2_funct_1(sK1),sK1)
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7367,c_3806])).

cnf(c_7442,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7376,c_5445])).

cnf(c_7823,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7672,c_34,c_35,c_36,c_4468,c_7442])).

cnf(c_29,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1371,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) != iProver_top
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3149,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) != iProver_top
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3146,c_1371])).

cnf(c_7826,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top
    | r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7823,c_3149])).

cnf(c_26,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1374,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_9,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1387,plain,
    ( r2_relset_1(X0,X1,X2,X2) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2888,plain,
    ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1374,c_1387])).

cnf(c_7831,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7826,c_2888])).

cnf(c_9077,plain,
    ( r2_relset_1(sK0,sK0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9074,c_7831])).

cnf(c_9261,plain,
    ( sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5811,c_9077])).

cnf(c_9266,plain,
    ( sK0 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_9261,c_2888])).

cnf(c_9267,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9266,c_9077])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1393,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2201,plain,
    ( sK1 = k1_xboole_0
    | sK0 != k1_xboole_0
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2198,c_1393])).

cnf(c_2202,plain,
    ( ~ v1_relat_1(sK1)
    | sK1 = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2201])).

cnf(c_2204,plain,
    ( sK0 != k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2201,c_30,c_1646,c_2202])).

cnf(c_2205,plain,
    ( sK1 = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_2204])).

cnf(c_9298,plain,
    ( sK1 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9266,c_2205])).

cnf(c_9311,plain,
    ( sK1 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_9298])).

cnf(c_9454,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_relat_1(k1_xboole_0)),k6_partfun1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9267,c_9311])).

cnf(c_3,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1392,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1906,plain,
    ( k6_partfun1(X0) = k1_xboole_0
    | k1_xboole_0 != X0
    | v1_relat_1(k6_partfun1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_1392])).

cnf(c_45,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_1641,plain,
    ( ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | v1_relat_1(k6_partfun1(X0)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1642,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_relat_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1641])).

cnf(c_2023,plain,
    ( k1_xboole_0 != X0
    | k6_partfun1(X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1906,c_45,c_1642])).

cnf(c_2024,plain,
    ( k6_partfun1(X0) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(renaming,[status(thm)],[c_2023])).

cnf(c_2028,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_2024])).

cnf(c_2317,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2028,c_3])).

cnf(c_9456,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9454,c_2028,c_2317])).

cnf(c_2316,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2028,c_1374])).

cnf(c_94,plain,
    ( r2_relset_1(X0,X1,X2,X2) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_96,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_94])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9456,c_2316,c_96])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.32  % Computer   : n009.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % WCLimit    : 600
% 0.13/0.32  % DateTime   : Tue Dec  1 12:40:26 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 3.23/0.97  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/0.97  
% 3.23/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.23/0.97  
% 3.23/0.97  ------  iProver source info
% 3.23/0.97  
% 3.23/0.97  git: date: 2020-06-30 10:37:57 +0100
% 3.23/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.23/0.97  git: non_committed_changes: false
% 3.23/0.97  git: last_make_outside_of_git: false
% 3.23/0.97  
% 3.23/0.97  ------ 
% 3.23/0.97  
% 3.23/0.97  ------ Input Options
% 3.23/0.97  
% 3.23/0.97  --out_options                           all
% 3.23/0.97  --tptp_safe_out                         true
% 3.23/0.97  --problem_path                          ""
% 3.23/0.97  --include_path                          ""
% 3.23/0.97  --clausifier                            res/vclausify_rel
% 3.23/0.97  --clausifier_options                    --mode clausify
% 3.23/0.97  --stdin                                 false
% 3.23/0.97  --stats_out                             all
% 3.23/0.97  
% 3.23/0.97  ------ General Options
% 3.23/0.97  
% 3.23/0.97  --fof                                   false
% 3.23/0.97  --time_out_real                         305.
% 3.23/0.97  --time_out_virtual                      -1.
% 3.23/0.97  --symbol_type_check                     false
% 3.23/0.97  --clausify_out                          false
% 3.23/0.97  --sig_cnt_out                           false
% 3.23/0.97  --trig_cnt_out                          false
% 3.23/0.97  --trig_cnt_out_tolerance                1.
% 3.23/0.97  --trig_cnt_out_sk_spl                   false
% 3.23/0.97  --abstr_cl_out                          false
% 3.23/0.97  
% 3.23/0.97  ------ Global Options
% 3.23/0.97  
% 3.23/0.97  --schedule                              default
% 3.23/0.97  --add_important_lit                     false
% 3.23/0.97  --prop_solver_per_cl                    1000
% 3.23/0.97  --min_unsat_core                        false
% 3.23/0.97  --soft_assumptions                      false
% 3.23/0.97  --soft_lemma_size                       3
% 3.23/0.97  --prop_impl_unit_size                   0
% 3.23/0.97  --prop_impl_unit                        []
% 3.23/0.97  --share_sel_clauses                     true
% 3.23/0.97  --reset_solvers                         false
% 3.23/0.97  --bc_imp_inh                            [conj_cone]
% 3.23/0.97  --conj_cone_tolerance                   3.
% 3.23/0.97  --extra_neg_conj                        none
% 3.23/0.97  --large_theory_mode                     true
% 3.23/0.97  --prolific_symb_bound                   200
% 3.23/0.97  --lt_threshold                          2000
% 3.23/0.97  --clause_weak_htbl                      true
% 3.23/0.97  --gc_record_bc_elim                     false
% 3.23/0.97  
% 3.23/0.97  ------ Preprocessing Options
% 3.23/0.97  
% 3.23/0.97  --preprocessing_flag                    true
% 3.23/0.97  --time_out_prep_mult                    0.1
% 3.23/0.97  --splitting_mode                        input
% 3.23/0.97  --splitting_grd                         true
% 3.23/0.97  --splitting_cvd                         false
% 3.23/0.97  --splitting_cvd_svl                     false
% 3.23/0.97  --splitting_nvd                         32
% 3.23/0.97  --sub_typing                            true
% 3.23/0.97  --prep_gs_sim                           true
% 3.23/0.97  --prep_unflatten                        true
% 3.23/0.97  --prep_res_sim                          true
% 3.23/0.97  --prep_upred                            true
% 3.23/0.97  --prep_sem_filter                       exhaustive
% 3.23/0.97  --prep_sem_filter_out                   false
% 3.23/0.97  --pred_elim                             true
% 3.23/0.97  --res_sim_input                         true
% 3.23/0.97  --eq_ax_congr_red                       true
% 3.23/0.97  --pure_diseq_elim                       true
% 3.23/0.97  --brand_transform                       false
% 3.23/0.97  --non_eq_to_eq                          false
% 3.23/0.97  --prep_def_merge                        true
% 3.23/0.97  --prep_def_merge_prop_impl              false
% 3.23/0.97  --prep_def_merge_mbd                    true
% 3.23/0.97  --prep_def_merge_tr_red                 false
% 3.23/0.97  --prep_def_merge_tr_cl                  false
% 3.23/0.97  --smt_preprocessing                     true
% 3.23/0.97  --smt_ac_axioms                         fast
% 3.23/0.97  --preprocessed_out                      false
% 3.23/0.97  --preprocessed_stats                    false
% 3.23/0.97  
% 3.23/0.97  ------ Abstraction refinement Options
% 3.23/0.97  
% 3.23/0.97  --abstr_ref                             []
% 3.23/0.97  --abstr_ref_prep                        false
% 3.23/0.97  --abstr_ref_until_sat                   false
% 3.23/0.97  --abstr_ref_sig_restrict                funpre
% 3.23/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.23/0.97  --abstr_ref_under                       []
% 3.23/0.97  
% 3.23/0.97  ------ SAT Options
% 3.23/0.97  
% 3.23/0.97  --sat_mode                              false
% 3.23/0.97  --sat_fm_restart_options                ""
% 3.23/0.97  --sat_gr_def                            false
% 3.23/0.97  --sat_epr_types                         true
% 3.23/0.97  --sat_non_cyclic_types                  false
% 3.23/0.97  --sat_finite_models                     false
% 3.23/0.97  --sat_fm_lemmas                         false
% 3.23/0.97  --sat_fm_prep                           false
% 3.23/0.97  --sat_fm_uc_incr                        true
% 3.23/0.97  --sat_out_model                         small
% 3.23/0.97  --sat_out_clauses                       false
% 3.23/0.97  
% 3.23/0.97  ------ QBF Options
% 3.23/0.97  
% 3.23/0.97  --qbf_mode                              false
% 3.23/0.97  --qbf_elim_univ                         false
% 3.23/0.97  --qbf_dom_inst                          none
% 3.23/0.97  --qbf_dom_pre_inst                      false
% 3.23/0.97  --qbf_sk_in                             false
% 3.23/0.97  --qbf_pred_elim                         true
% 3.23/0.97  --qbf_split                             512
% 3.23/0.97  
% 3.23/0.97  ------ BMC1 Options
% 3.23/0.97  
% 3.23/0.97  --bmc1_incremental                      false
% 3.23/0.97  --bmc1_axioms                           reachable_all
% 3.23/0.97  --bmc1_min_bound                        0
% 3.23/0.97  --bmc1_max_bound                        -1
% 3.23/0.97  --bmc1_max_bound_default                -1
% 3.23/0.97  --bmc1_symbol_reachability              true
% 3.23/0.97  --bmc1_property_lemmas                  false
% 3.23/0.97  --bmc1_k_induction                      false
% 3.23/0.97  --bmc1_non_equiv_states                 false
% 3.23/0.97  --bmc1_deadlock                         false
% 3.23/0.97  --bmc1_ucm                              false
% 3.23/0.97  --bmc1_add_unsat_core                   none
% 3.23/0.97  --bmc1_unsat_core_children              false
% 3.23/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.23/0.97  --bmc1_out_stat                         full
% 3.23/0.97  --bmc1_ground_init                      false
% 3.23/0.97  --bmc1_pre_inst_next_state              false
% 3.23/0.97  --bmc1_pre_inst_state                   false
% 3.23/0.97  --bmc1_pre_inst_reach_state             false
% 3.23/0.97  --bmc1_out_unsat_core                   false
% 3.23/0.97  --bmc1_aig_witness_out                  false
% 3.23/0.97  --bmc1_verbose                          false
% 3.23/0.97  --bmc1_dump_clauses_tptp                false
% 3.23/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.23/0.97  --bmc1_dump_file                        -
% 3.23/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.23/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.23/0.97  --bmc1_ucm_extend_mode                  1
% 3.23/0.97  --bmc1_ucm_init_mode                    2
% 3.23/0.97  --bmc1_ucm_cone_mode                    none
% 3.23/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.23/0.97  --bmc1_ucm_relax_model                  4
% 3.23/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.23/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.23/0.97  --bmc1_ucm_layered_model                none
% 3.23/0.97  --bmc1_ucm_max_lemma_size               10
% 3.23/0.97  
% 3.23/0.97  ------ AIG Options
% 3.23/0.97  
% 3.23/0.97  --aig_mode                              false
% 3.23/0.97  
% 3.23/0.97  ------ Instantiation Options
% 3.23/0.97  
% 3.23/0.97  --instantiation_flag                    true
% 3.23/0.97  --inst_sos_flag                         false
% 3.23/0.97  --inst_sos_phase                        true
% 3.23/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.23/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.23/0.97  --inst_lit_sel_side                     num_symb
% 3.23/0.97  --inst_solver_per_active                1400
% 3.23/0.97  --inst_solver_calls_frac                1.
% 3.23/0.97  --inst_passive_queue_type               priority_queues
% 3.23/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.23/0.97  --inst_passive_queues_freq              [25;2]
% 3.23/0.97  --inst_dismatching                      true
% 3.23/0.97  --inst_eager_unprocessed_to_passive     true
% 3.23/0.97  --inst_prop_sim_given                   true
% 3.23/0.97  --inst_prop_sim_new                     false
% 3.23/0.97  --inst_subs_new                         false
% 3.23/0.97  --inst_eq_res_simp                      false
% 3.23/0.97  --inst_subs_given                       false
% 3.23/0.97  --inst_orphan_elimination               true
% 3.23/0.97  --inst_learning_loop_flag               true
% 3.23/0.97  --inst_learning_start                   3000
% 3.23/0.97  --inst_learning_factor                  2
% 3.23/0.97  --inst_start_prop_sim_after_learn       3
% 3.23/0.97  --inst_sel_renew                        solver
% 3.23/0.97  --inst_lit_activity_flag                true
% 3.23/0.97  --inst_restr_to_given                   false
% 3.23/0.97  --inst_activity_threshold               500
% 3.23/0.97  --inst_out_proof                        true
% 3.23/0.97  
% 3.23/0.97  ------ Resolution Options
% 3.23/0.97  
% 3.23/0.97  --resolution_flag                       true
% 3.23/0.97  --res_lit_sel                           adaptive
% 3.23/0.97  --res_lit_sel_side                      none
% 3.23/0.97  --res_ordering                          kbo
% 3.23/0.97  --res_to_prop_solver                    active
% 3.23/0.97  --res_prop_simpl_new                    false
% 3.23/0.97  --res_prop_simpl_given                  true
% 3.23/0.97  --res_passive_queue_type                priority_queues
% 3.23/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.23/0.97  --res_passive_queues_freq               [15;5]
% 3.23/0.97  --res_forward_subs                      full
% 3.23/0.97  --res_backward_subs                     full
% 3.23/0.97  --res_forward_subs_resolution           true
% 3.23/0.97  --res_backward_subs_resolution          true
% 3.23/0.97  --res_orphan_elimination                true
% 3.23/0.97  --res_time_limit                        2.
% 3.23/0.97  --res_out_proof                         true
% 3.23/0.97  
% 3.23/0.97  ------ Superposition Options
% 3.23/0.97  
% 3.23/0.97  --superposition_flag                    true
% 3.23/0.97  --sup_passive_queue_type                priority_queues
% 3.23/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.23/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.23/0.97  --demod_completeness_check              fast
% 3.23/0.97  --demod_use_ground                      true
% 3.23/0.97  --sup_to_prop_solver                    passive
% 3.23/0.97  --sup_prop_simpl_new                    true
% 3.23/0.97  --sup_prop_simpl_given                  true
% 3.23/0.97  --sup_fun_splitting                     false
% 3.23/0.97  --sup_smt_interval                      50000
% 3.23/0.97  
% 3.23/0.97  ------ Superposition Simplification Setup
% 3.23/0.97  
% 3.23/0.97  --sup_indices_passive                   []
% 3.23/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.23/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/0.97  --sup_full_bw                           [BwDemod]
% 3.23/0.97  --sup_immed_triv                        [TrivRules]
% 3.23/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.23/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/0.97  --sup_immed_bw_main                     []
% 3.23/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.23/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.23/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.23/0.97  
% 3.23/0.97  ------ Combination Options
% 3.23/0.97  
% 3.23/0.97  --comb_res_mult                         3
% 3.23/0.97  --comb_sup_mult                         2
% 3.23/0.97  --comb_inst_mult                        10
% 3.23/0.97  
% 3.23/0.97  ------ Debug Options
% 3.23/0.97  
% 3.23/0.97  --dbg_backtrace                         false
% 3.23/0.97  --dbg_dump_prop_clauses                 false
% 3.23/0.97  --dbg_dump_prop_clauses_file            -
% 3.23/0.97  --dbg_out_stat                          false
% 3.23/0.97  ------ Parsing...
% 3.23/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.23/0.97  
% 3.23/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.23/0.97  
% 3.23/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.23/0.97  
% 3.23/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.23/0.97  ------ Proving...
% 3.23/0.97  ------ Problem Properties 
% 3.23/0.97  
% 3.23/0.97  
% 3.23/0.97  clauses                                 30
% 3.23/0.97  conjectures                             5
% 3.23/0.97  EPR                                     3
% 3.23/0.97  Horn                                    26
% 3.23/0.97  unary                                   7
% 3.23/0.97  binary                                  4
% 3.23/0.97  lits                                    93
% 3.23/0.97  lits eq                                 22
% 3.23/0.97  fd_pure                                 0
% 3.23/0.97  fd_pseudo                               0
% 3.23/0.97  fd_cond                                 5
% 3.23/0.97  fd_pseudo_cond                          2
% 3.23/0.97  AC symbols                              0
% 3.23/0.97  
% 3.23/0.97  ------ Schedule dynamic 5 is on 
% 3.23/0.97  
% 3.23/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.23/0.97  
% 3.23/0.97  
% 3.23/0.97  ------ 
% 3.23/0.97  Current options:
% 3.23/0.97  ------ 
% 3.23/0.97  
% 3.23/0.97  ------ Input Options
% 3.23/0.97  
% 3.23/0.97  --out_options                           all
% 3.23/0.97  --tptp_safe_out                         true
% 3.23/0.97  --problem_path                          ""
% 3.23/0.97  --include_path                          ""
% 3.23/0.97  --clausifier                            res/vclausify_rel
% 3.23/0.97  --clausifier_options                    --mode clausify
% 3.23/0.97  --stdin                                 false
% 3.23/0.97  --stats_out                             all
% 3.23/0.97  
% 3.23/0.97  ------ General Options
% 3.23/0.97  
% 3.23/0.97  --fof                                   false
% 3.23/0.97  --time_out_real                         305.
% 3.23/0.97  --time_out_virtual                      -1.
% 3.23/0.97  --symbol_type_check                     false
% 3.23/0.97  --clausify_out                          false
% 3.23/0.97  --sig_cnt_out                           false
% 3.23/0.97  --trig_cnt_out                          false
% 3.23/0.97  --trig_cnt_out_tolerance                1.
% 3.23/0.97  --trig_cnt_out_sk_spl                   false
% 3.23/0.97  --abstr_cl_out                          false
% 3.23/0.97  
% 3.23/0.97  ------ Global Options
% 3.23/0.97  
% 3.23/0.97  --schedule                              default
% 3.23/0.97  --add_important_lit                     false
% 3.23/0.97  --prop_solver_per_cl                    1000
% 3.23/0.97  --min_unsat_core                        false
% 3.23/0.97  --soft_assumptions                      false
% 3.23/0.97  --soft_lemma_size                       3
% 3.23/0.97  --prop_impl_unit_size                   0
% 3.23/0.97  --prop_impl_unit                        []
% 3.23/0.97  --share_sel_clauses                     true
% 3.23/0.97  --reset_solvers                         false
% 3.23/0.97  --bc_imp_inh                            [conj_cone]
% 3.23/0.97  --conj_cone_tolerance                   3.
% 3.23/0.97  --extra_neg_conj                        none
% 3.23/0.97  --large_theory_mode                     true
% 3.23/0.97  --prolific_symb_bound                   200
% 3.23/0.97  --lt_threshold                          2000
% 3.23/0.97  --clause_weak_htbl                      true
% 3.23/0.97  --gc_record_bc_elim                     false
% 3.23/0.97  
% 3.23/0.97  ------ Preprocessing Options
% 3.23/0.97  
% 3.23/0.97  --preprocessing_flag                    true
% 3.23/0.97  --time_out_prep_mult                    0.1
% 3.23/0.97  --splitting_mode                        input
% 3.23/0.97  --splitting_grd                         true
% 3.23/0.97  --splitting_cvd                         false
% 3.23/0.97  --splitting_cvd_svl                     false
% 3.23/0.97  --splitting_nvd                         32
% 3.23/0.97  --sub_typing                            true
% 3.23/0.97  --prep_gs_sim                           true
% 3.23/0.97  --prep_unflatten                        true
% 3.23/0.97  --prep_res_sim                          true
% 3.23/0.97  --prep_upred                            true
% 3.23/0.97  --prep_sem_filter                       exhaustive
% 3.23/0.97  --prep_sem_filter_out                   false
% 3.23/0.97  --pred_elim                             true
% 3.23/0.97  --res_sim_input                         true
% 3.23/0.97  --eq_ax_congr_red                       true
% 3.23/0.97  --pure_diseq_elim                       true
% 3.23/0.97  --brand_transform                       false
% 3.23/0.97  --non_eq_to_eq                          false
% 3.23/0.97  --prep_def_merge                        true
% 3.23/0.97  --prep_def_merge_prop_impl              false
% 3.23/0.97  --prep_def_merge_mbd                    true
% 3.23/0.97  --prep_def_merge_tr_red                 false
% 3.23/0.97  --prep_def_merge_tr_cl                  false
% 3.23/0.97  --smt_preprocessing                     true
% 3.23/0.97  --smt_ac_axioms                         fast
% 3.23/0.97  --preprocessed_out                      false
% 3.23/0.97  --preprocessed_stats                    false
% 3.23/0.97  
% 3.23/0.97  ------ Abstraction refinement Options
% 3.23/0.97  
% 3.23/0.97  --abstr_ref                             []
% 3.23/0.97  --abstr_ref_prep                        false
% 3.23/0.97  --abstr_ref_until_sat                   false
% 3.23/0.97  --abstr_ref_sig_restrict                funpre
% 3.23/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.23/0.97  --abstr_ref_under                       []
% 3.23/0.97  
% 3.23/0.97  ------ SAT Options
% 3.23/0.97  
% 3.23/0.97  --sat_mode                              false
% 3.23/0.97  --sat_fm_restart_options                ""
% 3.23/0.97  --sat_gr_def                            false
% 3.23/0.97  --sat_epr_types                         true
% 3.23/0.97  --sat_non_cyclic_types                  false
% 3.23/0.97  --sat_finite_models                     false
% 3.23/0.97  --sat_fm_lemmas                         false
% 3.23/0.97  --sat_fm_prep                           false
% 3.23/0.97  --sat_fm_uc_incr                        true
% 3.23/0.97  --sat_out_model                         small
% 3.23/0.97  --sat_out_clauses                       false
% 3.23/0.97  
% 3.23/0.97  ------ QBF Options
% 3.23/0.97  
% 3.23/0.97  --qbf_mode                              false
% 3.23/0.97  --qbf_elim_univ                         false
% 3.23/0.97  --qbf_dom_inst                          none
% 3.23/0.97  --qbf_dom_pre_inst                      false
% 3.23/0.97  --qbf_sk_in                             false
% 3.23/0.97  --qbf_pred_elim                         true
% 3.23/0.97  --qbf_split                             512
% 3.23/0.97  
% 3.23/0.97  ------ BMC1 Options
% 3.23/0.97  
% 3.23/0.97  --bmc1_incremental                      false
% 3.23/0.97  --bmc1_axioms                           reachable_all
% 3.23/0.97  --bmc1_min_bound                        0
% 3.23/0.97  --bmc1_max_bound                        -1
% 3.23/0.97  --bmc1_max_bound_default                -1
% 3.23/0.97  --bmc1_symbol_reachability              true
% 3.23/0.97  --bmc1_property_lemmas                  false
% 3.23/0.97  --bmc1_k_induction                      false
% 3.23/0.97  --bmc1_non_equiv_states                 false
% 3.23/0.97  --bmc1_deadlock                         false
% 3.23/0.97  --bmc1_ucm                              false
% 3.23/0.97  --bmc1_add_unsat_core                   none
% 3.23/0.97  --bmc1_unsat_core_children              false
% 3.23/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.23/0.97  --bmc1_out_stat                         full
% 3.23/0.97  --bmc1_ground_init                      false
% 3.23/0.97  --bmc1_pre_inst_next_state              false
% 3.23/0.97  --bmc1_pre_inst_state                   false
% 3.23/0.97  --bmc1_pre_inst_reach_state             false
% 3.23/0.97  --bmc1_out_unsat_core                   false
% 3.23/0.97  --bmc1_aig_witness_out                  false
% 3.23/0.97  --bmc1_verbose                          false
% 3.23/0.97  --bmc1_dump_clauses_tptp                false
% 3.23/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.23/0.97  --bmc1_dump_file                        -
% 3.23/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.23/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.23/0.97  --bmc1_ucm_extend_mode                  1
% 3.23/0.97  --bmc1_ucm_init_mode                    2
% 3.23/0.97  --bmc1_ucm_cone_mode                    none
% 3.23/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.23/0.97  --bmc1_ucm_relax_model                  4
% 3.23/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.23/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.23/0.97  --bmc1_ucm_layered_model                none
% 3.23/0.97  --bmc1_ucm_max_lemma_size               10
% 3.23/0.97  
% 3.23/0.97  ------ AIG Options
% 3.23/0.97  
% 3.23/0.97  --aig_mode                              false
% 3.23/0.97  
% 3.23/0.97  ------ Instantiation Options
% 3.23/0.97  
% 3.23/0.97  --instantiation_flag                    true
% 3.23/0.97  --inst_sos_flag                         false
% 3.23/0.97  --inst_sos_phase                        true
% 3.23/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.23/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.23/0.97  --inst_lit_sel_side                     none
% 3.23/0.97  --inst_solver_per_active                1400
% 3.23/0.97  --inst_solver_calls_frac                1.
% 3.23/0.97  --inst_passive_queue_type               priority_queues
% 3.23/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.23/0.97  --inst_passive_queues_freq              [25;2]
% 3.23/0.97  --inst_dismatching                      true
% 3.23/0.97  --inst_eager_unprocessed_to_passive     true
% 3.23/0.97  --inst_prop_sim_given                   true
% 3.23/0.97  --inst_prop_sim_new                     false
% 3.23/0.97  --inst_subs_new                         false
% 3.23/0.97  --inst_eq_res_simp                      false
% 3.23/0.97  --inst_subs_given                       false
% 3.23/0.97  --inst_orphan_elimination               true
% 3.23/0.97  --inst_learning_loop_flag               true
% 3.23/0.97  --inst_learning_start                   3000
% 3.23/0.97  --inst_learning_factor                  2
% 3.23/0.97  --inst_start_prop_sim_after_learn       3
% 3.23/0.97  --inst_sel_renew                        solver
% 3.23/0.97  --inst_lit_activity_flag                true
% 3.23/0.97  --inst_restr_to_given                   false
% 3.23/0.97  --inst_activity_threshold               500
% 3.23/0.97  --inst_out_proof                        true
% 3.23/0.97  
% 3.23/0.97  ------ Resolution Options
% 3.23/0.97  
% 3.23/0.97  --resolution_flag                       false
% 3.23/0.97  --res_lit_sel                           adaptive
% 3.23/0.97  --res_lit_sel_side                      none
% 3.23/0.97  --res_ordering                          kbo
% 3.23/0.97  --res_to_prop_solver                    active
% 3.23/0.97  --res_prop_simpl_new                    false
% 3.23/0.97  --res_prop_simpl_given                  true
% 3.23/0.97  --res_passive_queue_type                priority_queues
% 3.23/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.23/0.97  --res_passive_queues_freq               [15;5]
% 3.23/0.97  --res_forward_subs                      full
% 3.23/0.97  --res_backward_subs                     full
% 3.23/0.97  --res_forward_subs_resolution           true
% 3.23/0.97  --res_backward_subs_resolution          true
% 3.23/0.97  --res_orphan_elimination                true
% 3.23/0.97  --res_time_limit                        2.
% 3.23/0.97  --res_out_proof                         true
% 3.23/0.97  
% 3.23/0.97  ------ Superposition Options
% 3.23/0.97  
% 3.23/0.97  --superposition_flag                    true
% 3.23/0.97  --sup_passive_queue_type                priority_queues
% 3.23/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.23/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.23/0.97  --demod_completeness_check              fast
% 3.23/0.97  --demod_use_ground                      true
% 3.23/0.97  --sup_to_prop_solver                    passive
% 3.23/0.97  --sup_prop_simpl_new                    true
% 3.23/0.97  --sup_prop_simpl_given                  true
% 3.23/0.97  --sup_fun_splitting                     false
% 3.23/0.97  --sup_smt_interval                      50000
% 3.23/0.97  
% 3.23/0.97  ------ Superposition Simplification Setup
% 3.23/0.97  
% 3.23/0.97  --sup_indices_passive                   []
% 3.23/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.23/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/0.97  --sup_full_bw                           [BwDemod]
% 3.23/0.97  --sup_immed_triv                        [TrivRules]
% 3.23/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.23/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/0.97  --sup_immed_bw_main                     []
% 3.23/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.23/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.23/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.23/0.97  
% 3.23/0.97  ------ Combination Options
% 3.23/0.97  
% 3.23/0.97  --comb_res_mult                         3
% 3.23/0.97  --comb_sup_mult                         2
% 3.23/0.97  --comb_inst_mult                        10
% 3.23/0.97  
% 3.23/0.97  ------ Debug Options
% 3.23/0.97  
% 3.23/0.97  --dbg_backtrace                         false
% 3.23/0.97  --dbg_dump_prop_clauses                 false
% 3.23/0.97  --dbg_dump_prop_clauses_file            -
% 3.23/0.97  --dbg_out_stat                          false
% 3.23/0.97  
% 3.23/0.97  
% 3.23/0.97  
% 3.23/0.97  
% 3.23/0.97  ------ Proving...
% 3.23/0.97  
% 3.23/0.97  
% 3.23/0.97  % SZS status Theorem for theBenchmark.p
% 3.23/0.97  
% 3.23/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 3.23/0.97  
% 3.23/0.97  fof(f16,conjecture,(
% 3.23/0.97    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 3.23/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.97  
% 3.23/0.97  fof(f17,negated_conjecture,(
% 3.23/0.97    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 3.23/0.97    inference(negated_conjecture,[],[f16])).
% 3.23/0.97  
% 3.23/0.97  fof(f41,plain,(
% 3.23/0.97    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 3.23/0.97    inference(ennf_transformation,[],[f17])).
% 3.23/0.97  
% 3.23/0.97  fof(f42,plain,(
% 3.23/0.97    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 3.23/0.97    inference(flattening,[],[f41])).
% 3.23/0.97  
% 3.23/0.97  fof(f46,plain,(
% 3.23/0.97    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 3.23/0.97    introduced(choice_axiom,[])).
% 3.23/0.97  
% 3.23/0.97  fof(f47,plain,(
% 3.23/0.97    (~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 3.23/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f42,f46])).
% 3.23/0.97  
% 3.23/0.97  fof(f81,plain,(
% 3.23/0.97    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.23/0.97    inference(cnf_transformation,[],[f47])).
% 3.23/0.97  
% 3.23/0.97  fof(f9,axiom,(
% 3.23/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.23/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.97  
% 3.23/0.97  fof(f31,plain,(
% 3.23/0.97    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.23/0.97    inference(ennf_transformation,[],[f9])).
% 3.23/0.97  
% 3.23/0.97  fof(f32,plain,(
% 3.23/0.97    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.23/0.97    inference(flattening,[],[f31])).
% 3.23/0.97  
% 3.23/0.97  fof(f44,plain,(
% 3.23/0.97    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.23/0.97    inference(nnf_transformation,[],[f32])).
% 3.23/0.97  
% 3.23/0.97  fof(f62,plain,(
% 3.23/0.97    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.23/0.97    inference(cnf_transformation,[],[f44])).
% 3.23/0.97  
% 3.23/0.97  fof(f6,axiom,(
% 3.23/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.23/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.97  
% 3.23/0.97  fof(f26,plain,(
% 3.23/0.97    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.23/0.97    inference(ennf_transformation,[],[f6])).
% 3.23/0.97  
% 3.23/0.97  fof(f56,plain,(
% 3.23/0.97    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.23/0.97    inference(cnf_transformation,[],[f26])).
% 3.23/0.97  
% 3.23/0.97  fof(f79,plain,(
% 3.23/0.97    v1_funct_2(sK1,sK0,sK0)),
% 3.23/0.97    inference(cnf_transformation,[],[f47])).
% 3.23/0.97  
% 3.23/0.97  fof(f14,axiom,(
% 3.23/0.97    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 3.23/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.97  
% 3.23/0.97  fof(f39,plain,(
% 3.23/0.97    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.23/0.97    inference(ennf_transformation,[],[f14])).
% 3.23/0.97  
% 3.23/0.97  fof(f40,plain,(
% 3.23/0.97    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.23/0.97    inference(flattening,[],[f39])).
% 3.23/0.97  
% 3.23/0.97  fof(f76,plain,(
% 3.23/0.97    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.23/0.97    inference(cnf_transformation,[],[f40])).
% 3.23/0.97  
% 3.23/0.97  fof(f78,plain,(
% 3.23/0.97    v1_funct_1(sK1)),
% 3.23/0.97    inference(cnf_transformation,[],[f47])).
% 3.23/0.97  
% 3.23/0.97  fof(f80,plain,(
% 3.23/0.97    v3_funct_2(sK1,sK0,sK0)),
% 3.23/0.97    inference(cnf_transformation,[],[f47])).
% 3.23/0.97  
% 3.23/0.97  fof(f11,axiom,(
% 3.23/0.97    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 3.23/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.97  
% 3.23/0.97  fof(f35,plain,(
% 3.23/0.97    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 3.23/0.97    inference(ennf_transformation,[],[f11])).
% 3.23/0.97  
% 3.23/0.97  fof(f36,plain,(
% 3.23/0.97    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 3.23/0.97    inference(flattening,[],[f35])).
% 3.23/0.97  
% 3.23/0.97  fof(f73,plain,(
% 3.23/0.97    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.23/0.97    inference(cnf_transformation,[],[f36])).
% 3.23/0.97  
% 3.23/0.97  fof(f13,axiom,(
% 3.23/0.97    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.23/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.97  
% 3.23/0.97  fof(f37,plain,(
% 3.23/0.97    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.23/0.97    inference(ennf_transformation,[],[f13])).
% 3.23/0.97  
% 3.23/0.97  fof(f38,plain,(
% 3.23/0.97    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.23/0.97    inference(flattening,[],[f37])).
% 3.23/0.97  
% 3.23/0.97  fof(f75,plain,(
% 3.23/0.97    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.23/0.97    inference(cnf_transformation,[],[f38])).
% 3.23/0.97  
% 3.23/0.97  fof(f70,plain,(
% 3.23/0.97    ( ! [X0,X1] : (v1_funct_1(k2_funct_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 3.23/0.97    inference(cnf_transformation,[],[f36])).
% 3.23/0.97  
% 3.23/0.97  fof(f3,axiom,(
% 3.23/0.97    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))))),
% 3.23/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.97  
% 3.23/0.97  fof(f22,plain,(
% 3.23/0.97    ! [X0] : (((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.23/0.97    inference(ennf_transformation,[],[f3])).
% 3.23/0.97  
% 3.23/0.97  fof(f23,plain,(
% 3.23/0.97    ! [X0] : ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.23/0.97    inference(flattening,[],[f22])).
% 3.23/0.97  
% 3.23/0.97  fof(f52,plain,(
% 3.23/0.97    ( ! [X0] : (k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.23/0.97    inference(cnf_transformation,[],[f23])).
% 3.23/0.97  
% 3.23/0.97  fof(f15,axiom,(
% 3.23/0.97    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.23/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.97  
% 3.23/0.97  fof(f77,plain,(
% 3.23/0.97    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.23/0.97    inference(cnf_transformation,[],[f15])).
% 3.23/0.97  
% 3.23/0.97  fof(f86,plain,(
% 3.23/0.97    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.23/0.97    inference(definition_unfolding,[],[f52,f77])).
% 3.23/0.97  
% 3.23/0.97  fof(f4,axiom,(
% 3.23/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.23/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.97  
% 3.23/0.97  fof(f24,plain,(
% 3.23/0.97    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.23/0.97    inference(ennf_transformation,[],[f4])).
% 3.23/0.97  
% 3.23/0.97  fof(f54,plain,(
% 3.23/0.97    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.23/0.97    inference(cnf_transformation,[],[f24])).
% 3.23/0.97  
% 3.23/0.97  fof(f8,axiom,(
% 3.23/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 3.23/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.97  
% 3.23/0.97  fof(f29,plain,(
% 3.23/0.97    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.23/0.97    inference(ennf_transformation,[],[f8])).
% 3.23/0.97  
% 3.23/0.97  fof(f30,plain,(
% 3.23/0.97    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.23/0.97    inference(flattening,[],[f29])).
% 3.23/0.97  
% 3.23/0.97  fof(f60,plain,(
% 3.23/0.97    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.23/0.97    inference(cnf_transformation,[],[f30])).
% 3.23/0.97  
% 3.23/0.97  fof(f53,plain,(
% 3.23/0.97    ( ! [X0] : (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.23/0.97    inference(cnf_transformation,[],[f23])).
% 3.23/0.97  
% 3.23/0.97  fof(f85,plain,(
% 3.23/0.97    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.23/0.97    inference(definition_unfolding,[],[f53,f77])).
% 3.23/0.97  
% 3.23/0.97  fof(f61,plain,(
% 3.23/0.97    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.23/0.97    inference(cnf_transformation,[],[f30])).
% 3.23/0.97  
% 3.23/0.97  fof(f5,axiom,(
% 3.23/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.23/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.97  
% 3.23/0.97  fof(f19,plain,(
% 3.23/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.23/0.97    inference(pure_predicate_removal,[],[f5])).
% 3.23/0.97  
% 3.23/0.97  fof(f25,plain,(
% 3.23/0.97    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.23/0.97    inference(ennf_transformation,[],[f19])).
% 3.23/0.97  
% 3.23/0.97  fof(f55,plain,(
% 3.23/0.97    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.23/0.97    inference(cnf_transformation,[],[f25])).
% 3.23/0.97  
% 3.23/0.97  fof(f10,axiom,(
% 3.23/0.97    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.23/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.97  
% 3.23/0.97  fof(f33,plain,(
% 3.23/0.97    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.23/0.97    inference(ennf_transformation,[],[f10])).
% 3.23/0.97  
% 3.23/0.97  fof(f34,plain,(
% 3.23/0.97    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.23/0.97    inference(flattening,[],[f33])).
% 3.23/0.97  
% 3.23/0.97  fof(f45,plain,(
% 3.23/0.97    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.23/0.97    inference(nnf_transformation,[],[f34])).
% 3.23/0.97  
% 3.23/0.97  fof(f68,plain,(
% 3.23/0.97    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.23/0.97    inference(cnf_transformation,[],[f45])).
% 3.23/0.97  
% 3.23/0.97  fof(f82,plain,(
% 3.23/0.97    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))),
% 3.23/0.97    inference(cnf_transformation,[],[f47])).
% 3.23/0.97  
% 3.23/0.97  fof(f12,axiom,(
% 3.23/0.97    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 3.23/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.97  
% 3.23/0.97  fof(f18,plain,(
% 3.23/0.97    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.23/0.97    inference(pure_predicate_removal,[],[f12])).
% 3.23/0.97  
% 3.23/0.97  fof(f74,plain,(
% 3.23/0.97    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.23/0.97    inference(cnf_transformation,[],[f18])).
% 3.23/0.97  
% 3.23/0.97  fof(f7,axiom,(
% 3.23/0.97    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.23/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.97  
% 3.23/0.97  fof(f27,plain,(
% 3.23/0.97    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.23/0.97    inference(ennf_transformation,[],[f7])).
% 3.23/0.97  
% 3.23/0.97  fof(f28,plain,(
% 3.23/0.97    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.23/0.97    inference(flattening,[],[f27])).
% 3.23/0.97  
% 3.23/0.97  fof(f43,plain,(
% 3.23/0.97    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.23/0.97    inference(nnf_transformation,[],[f28])).
% 3.23/0.97  
% 3.23/0.97  fof(f58,plain,(
% 3.23/0.97    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.23/0.97    inference(cnf_transformation,[],[f43])).
% 3.23/0.97  
% 3.23/0.97  fof(f87,plain,(
% 3.23/0.97    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.23/0.97    inference(equality_resolution,[],[f58])).
% 3.23/0.97  
% 3.23/0.97  fof(f1,axiom,(
% 3.23/0.97    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_relat_1(X0) = k1_xboole_0) => k1_xboole_0 = X0))),
% 3.23/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.97  
% 3.23/0.97  fof(f20,plain,(
% 3.23/0.97    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_relat_1(X0) != k1_xboole_0)) | ~v1_relat_1(X0))),
% 3.23/0.97    inference(ennf_transformation,[],[f1])).
% 3.23/0.97  
% 3.23/0.97  fof(f21,plain,(
% 3.23/0.97    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_relat_1(X0) != k1_xboole_0) | ~v1_relat_1(X0))),
% 3.23/0.97    inference(flattening,[],[f20])).
% 3.23/0.97  
% 3.23/0.97  fof(f49,plain,(
% 3.23/0.97    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.23/0.97    inference(cnf_transformation,[],[f21])).
% 3.23/0.97  
% 3.23/0.97  fof(f2,axiom,(
% 3.23/0.97    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.23/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.97  
% 3.23/0.97  fof(f50,plain,(
% 3.23/0.97    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 3.23/0.97    inference(cnf_transformation,[],[f2])).
% 3.23/0.97  
% 3.23/0.97  fof(f84,plain,(
% 3.23/0.97    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 3.23/0.97    inference(definition_unfolding,[],[f50,f77])).
% 3.23/0.97  
% 3.23/0.97  fof(f48,plain,(
% 3.23/0.97    ( ! [X0] : (k1_xboole_0 = X0 | k1_relat_1(X0) != k1_xboole_0 | ~v1_relat_1(X0)) )),
% 3.23/0.97    inference(cnf_transformation,[],[f21])).
% 3.23/0.97  
% 3.23/0.97  cnf(c_30,negated_conjecture,
% 3.23/0.97      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 3.23/0.97      inference(cnf_transformation,[],[f81]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_1370,plain,
% 3.23/0.97      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.23/0.97      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_19,plain,
% 3.23/0.97      ( ~ v1_funct_2(X0,X1,X2)
% 3.23/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.23/0.97      | k1_relset_1(X1,X2,X0) = X1
% 3.23/0.97      | k1_xboole_0 = X2 ),
% 3.23/0.97      inference(cnf_transformation,[],[f62]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_1379,plain,
% 3.23/0.97      ( k1_relset_1(X0,X1,X2) = X0
% 3.23/0.97      | k1_xboole_0 = X1
% 3.23/0.97      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.23/0.97      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.23/0.97      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_4492,plain,
% 3.23/0.97      ( k1_relset_1(sK0,sK0,sK1) = sK0
% 3.23/0.97      | sK0 = k1_xboole_0
% 3.23/0.97      | v1_funct_2(sK1,sK0,sK0) != iProver_top ),
% 3.23/0.97      inference(superposition,[status(thm)],[c_1370,c_1379]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_8,plain,
% 3.23/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.23/0.97      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.23/0.97      inference(cnf_transformation,[],[f56]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_1388,plain,
% 3.23/0.97      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.23/0.97      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.23/0.97      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_2902,plain,
% 3.23/0.97      ( k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
% 3.23/0.97      inference(superposition,[status(thm)],[c_1370,c_1388]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_4497,plain,
% 3.23/0.97      ( k1_relat_1(sK1) = sK0
% 3.23/0.97      | sK0 = k1_xboole_0
% 3.23/0.97      | v1_funct_2(sK1,sK0,sK0) != iProver_top ),
% 3.23/0.97      inference(demodulation,[status(thm)],[c_4492,c_2902]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_32,negated_conjecture,
% 3.23/0.97      ( v1_funct_2(sK1,sK0,sK0) ),
% 3.23/0.97      inference(cnf_transformation,[],[f79]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_35,plain,
% 3.23/0.97      ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
% 3.23/0.97      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_5810,plain,
% 3.23/0.97      ( sK0 = k1_xboole_0 | k1_relat_1(sK1) = sK0 ),
% 3.23/0.97      inference(global_propositional_subsumption,
% 3.23/0.97                [status(thm)],
% 3.23/0.97                [c_4497,c_35]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_5811,plain,
% 3.23/0.97      ( k1_relat_1(sK1) = sK0 | sK0 = k1_xboole_0 ),
% 3.23/0.97      inference(renaming,[status(thm)],[c_5810]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_28,plain,
% 3.23/0.97      ( ~ v1_funct_2(X0,X1,X1)
% 3.23/0.97      | ~ v3_funct_2(X0,X1,X1)
% 3.23/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.23/0.97      | ~ v1_funct_1(X0)
% 3.23/0.97      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 3.23/0.97      inference(cnf_transformation,[],[f76]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_1372,plain,
% 3.23/0.97      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
% 3.23/0.97      | v1_funct_2(X1,X0,X0) != iProver_top
% 3.23/0.97      | v3_funct_2(X1,X0,X0) != iProver_top
% 3.23/0.97      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 3.23/0.97      | v1_funct_1(X1) != iProver_top ),
% 3.23/0.97      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_2649,plain,
% 3.23/0.97      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
% 3.23/0.97      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.23/0.97      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.23/0.97      | v1_funct_1(sK1) != iProver_top ),
% 3.23/0.97      inference(superposition,[status(thm)],[c_1370,c_1372]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_33,negated_conjecture,
% 3.23/0.97      ( v1_funct_1(sK1) ),
% 3.23/0.97      inference(cnf_transformation,[],[f78]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_31,negated_conjecture,
% 3.23/0.97      ( v3_funct_2(sK1,sK0,sK0) ),
% 3.23/0.97      inference(cnf_transformation,[],[f80]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_1729,plain,
% 3.23/0.97      ( ~ v1_funct_2(sK1,X0,X0)
% 3.23/0.97      | ~ v3_funct_2(sK1,X0,X0)
% 3.23/0.97      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 3.23/0.97      | ~ v1_funct_1(sK1)
% 3.23/0.97      | k2_funct_2(X0,sK1) = k2_funct_1(sK1) ),
% 3.23/0.97      inference(instantiation,[status(thm)],[c_28]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_1919,plain,
% 3.23/0.97      ( ~ v1_funct_2(sK1,sK0,sK0)
% 3.23/0.97      | ~ v3_funct_2(sK1,sK0,sK0)
% 3.23/0.97      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.23/0.97      | ~ v1_funct_1(sK1)
% 3.23/0.97      | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 3.23/0.97      inference(instantiation,[status(thm)],[c_1729]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_3146,plain,
% 3.23/0.97      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 3.23/0.97      inference(global_propositional_subsumption,
% 3.23/0.97                [status(thm)],
% 3.23/0.97                [c_2649,c_33,c_32,c_31,c_30,c_1919]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_22,plain,
% 3.23/0.97      ( ~ v1_funct_2(X0,X1,X1)
% 3.23/0.97      | ~ v3_funct_2(X0,X1,X1)
% 3.23/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.23/0.97      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.23/0.97      | ~ v1_funct_1(X0) ),
% 3.23/0.97      inference(cnf_transformation,[],[f73]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_1378,plain,
% 3.23/0.97      ( v1_funct_2(X0,X1,X1) != iProver_top
% 3.23/0.97      | v3_funct_2(X0,X1,X1) != iProver_top
% 3.23/0.97      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 3.23/0.97      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) = iProver_top
% 3.23/0.97      | v1_funct_1(X0) != iProver_top ),
% 3.23/0.97      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_6156,plain,
% 3.23/0.97      ( v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.23/0.97      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.23/0.97      | m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 3.23/0.97      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.23/0.97      | v1_funct_1(sK1) != iProver_top ),
% 3.23/0.97      inference(superposition,[status(thm)],[c_3146,c_1378]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_34,plain,
% 3.23/0.97      ( v1_funct_1(sK1) = iProver_top ),
% 3.23/0.97      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_36,plain,
% 3.23/0.97      ( v3_funct_2(sK1,sK0,sK0) = iProver_top ),
% 3.23/0.97      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_37,plain,
% 3.23/0.97      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.23/0.97      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_7367,plain,
% 3.23/0.97      ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 3.23/0.97      inference(global_propositional_subsumption,
% 3.23/0.97                [status(thm)],
% 3.23/0.97                [c_6156,c_34,c_35,c_36,c_37]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_27,plain,
% 3.23/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.23/0.97      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.23/0.97      | ~ v1_funct_1(X0)
% 3.23/0.97      | ~ v1_funct_1(X3)
% 3.23/0.97      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.23/0.97      inference(cnf_transformation,[],[f75]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_1373,plain,
% 3.23/0.97      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 3.23/0.97      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.23/0.97      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.23/0.97      | v1_funct_1(X5) != iProver_top
% 3.23/0.97      | v1_funct_1(X4) != iProver_top ),
% 3.23/0.97      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_7383,plain,
% 3.23/0.97      ( k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1))
% 3.23/0.97      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.23/0.97      | v1_funct_1(X2) != iProver_top
% 3.23/0.97      | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
% 3.23/0.97      inference(superposition,[status(thm)],[c_7367,c_1373]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_25,plain,
% 3.23/0.97      ( ~ v1_funct_2(X0,X1,X1)
% 3.23/0.97      | ~ v3_funct_2(X0,X1,X1)
% 3.23/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.23/0.97      | ~ v1_funct_1(X0)
% 3.23/0.97      | v1_funct_1(k2_funct_2(X1,X0)) ),
% 3.23/0.97      inference(cnf_transformation,[],[f70]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_1375,plain,
% 3.23/0.97      ( v1_funct_2(X0,X1,X1) != iProver_top
% 3.23/0.97      | v3_funct_2(X0,X1,X1) != iProver_top
% 3.23/0.97      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 3.23/0.97      | v1_funct_1(X0) != iProver_top
% 3.23/0.97      | v1_funct_1(k2_funct_2(X1,X0)) = iProver_top ),
% 3.23/0.97      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_4454,plain,
% 3.23/0.97      ( v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.23/0.97      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.23/0.97      | v1_funct_1(k2_funct_2(sK0,sK1)) = iProver_top
% 3.23/0.97      | v1_funct_1(sK1) != iProver_top ),
% 3.23/0.97      inference(superposition,[status(thm)],[c_1370,c_1375]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_4468,plain,
% 3.23/0.97      ( v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.23/0.97      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.23/0.97      | v1_funct_1(k2_funct_1(sK1)) = iProver_top
% 3.23/0.97      | v1_funct_1(sK1) != iProver_top ),
% 3.23/0.97      inference(light_normalisation,[status(thm)],[c_4454,c_3146]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_9021,plain,
% 3.23/0.97      ( v1_funct_1(X2) != iProver_top
% 3.23/0.97      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.23/0.97      | k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1)) ),
% 3.23/0.97      inference(global_propositional_subsumption,
% 3.23/0.97                [status(thm)],
% 3.23/0.97                [c_7383,c_34,c_35,c_36,c_4468]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_9022,plain,
% 3.23/0.97      ( k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1))
% 3.23/0.97      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.23/0.97      | v1_funct_1(X2) != iProver_top ),
% 3.23/0.97      inference(renaming,[status(thm)],[c_9021]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_9032,plain,
% 3.23/0.97      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k5_relat_1(sK1,k2_funct_1(sK1))
% 3.23/0.97      | v1_funct_1(sK1) != iProver_top ),
% 3.23/0.97      inference(superposition,[status(thm)],[c_1370,c_9022]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_1367,plain,
% 3.23/0.97      ( v1_funct_1(sK1) = iProver_top ),
% 3.23/0.97      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_5,plain,
% 3.23/0.97      ( ~ v1_funct_1(X0)
% 3.23/0.97      | ~ v2_funct_1(X0)
% 3.23/0.97      | ~ v1_relat_1(X0)
% 3.23/0.97      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
% 3.23/0.97      inference(cnf_transformation,[],[f86]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_1390,plain,
% 3.23/0.97      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
% 3.23/0.97      | v1_funct_1(X0) != iProver_top
% 3.23/0.97      | v2_funct_1(X0) != iProver_top
% 3.23/0.97      | v1_relat_1(X0) != iProver_top ),
% 3.23/0.97      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_3622,plain,
% 3.23/0.97      ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
% 3.23/0.97      | v2_funct_1(sK1) != iProver_top
% 3.23/0.97      | v1_relat_1(sK1) != iProver_top ),
% 3.23/0.97      inference(superposition,[status(thm)],[c_1367,c_1390]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_6,plain,
% 3.23/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.23/0.97      | v1_relat_1(X0) ),
% 3.23/0.97      inference(cnf_transformation,[],[f54]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_1646,plain,
% 3.23/0.97      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.23/0.97      | v1_relat_1(sK1) ),
% 3.23/0.97      inference(instantiation,[status(thm)],[c_6]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_1661,plain,
% 3.23/0.97      ( ~ v1_funct_1(sK1)
% 3.23/0.97      | ~ v2_funct_1(sK1)
% 3.23/0.97      | ~ v1_relat_1(sK1)
% 3.23/0.97      | k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
% 3.23/0.97      inference(instantiation,[status(thm)],[c_5]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_12,plain,
% 3.23/0.97      ( ~ v3_funct_2(X0,X1,X2)
% 3.23/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.23/0.97      | ~ v1_funct_1(X0)
% 3.23/0.97      | v2_funct_1(X0) ),
% 3.23/0.97      inference(cnf_transformation,[],[f60]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_1690,plain,
% 3.23/0.97      ( ~ v3_funct_2(sK1,X0,X1)
% 3.23/0.97      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.23/0.97      | ~ v1_funct_1(sK1)
% 3.23/0.97      | v2_funct_1(sK1) ),
% 3.23/0.97      inference(instantiation,[status(thm)],[c_12]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_1829,plain,
% 3.23/0.97      ( ~ v3_funct_2(sK1,sK0,sK0)
% 3.23/0.97      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.23/0.97      | ~ v1_funct_1(sK1)
% 3.23/0.97      | v2_funct_1(sK1) ),
% 3.23/0.97      inference(instantiation,[status(thm)],[c_1690]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_3801,plain,
% 3.23/0.97      ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
% 3.23/0.97      inference(global_propositional_subsumption,
% 3.23/0.97                [status(thm)],
% 3.23/0.97                [c_3622,c_33,c_31,c_30,c_1646,c_1661,c_1829]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_9045,plain,
% 3.23/0.97      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
% 3.23/0.97      | v1_funct_1(sK1) != iProver_top ),
% 3.23/0.97      inference(light_normalisation,[status(thm)],[c_9032,c_3801]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_9074,plain,
% 3.23/0.97      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
% 3.23/0.97      inference(global_propositional_subsumption,
% 3.23/0.97                [status(thm)],
% 3.23/0.97                [c_9045,c_34]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_3439,plain,
% 3.23/0.97      ( k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1)
% 3.23/0.97      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.23/0.97      | v1_funct_1(X2) != iProver_top
% 3.23/0.97      | v1_funct_1(sK1) != iProver_top ),
% 3.23/0.97      inference(superposition,[status(thm)],[c_1370,c_1373]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_3805,plain,
% 3.23/0.97      ( v1_funct_1(X2) != iProver_top
% 3.23/0.97      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.23/0.97      | k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1) ),
% 3.23/0.97      inference(global_propositional_subsumption,
% 3.23/0.97                [status(thm)],
% 3.23/0.97                [c_3439,c_34]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_3806,plain,
% 3.23/0.97      ( k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1)
% 3.23/0.97      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.23/0.97      | v1_funct_1(X2) != iProver_top ),
% 3.23/0.97      inference(renaming,[status(thm)],[c_3805]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_6161,plain,
% 3.23/0.97      ( k1_partfun1(X0,X0,sK0,sK0,k2_funct_2(X0,X1),sK1) = k5_relat_1(k2_funct_2(X0,X1),sK1)
% 3.23/0.97      | v1_funct_2(X1,X0,X0) != iProver_top
% 3.23/0.97      | v3_funct_2(X1,X0,X0) != iProver_top
% 3.23/0.97      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 3.23/0.97      | v1_funct_1(X1) != iProver_top
% 3.23/0.97      | v1_funct_1(k2_funct_2(X0,X1)) != iProver_top ),
% 3.23/0.97      inference(superposition,[status(thm)],[c_1378,c_3806]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_7643,plain,
% 3.23/0.97      ( k1_partfun1(X0,X0,sK0,sK0,k2_funct_2(X0,X1),sK1) = k5_relat_1(k2_funct_2(X0,X1),sK1)
% 3.23/0.97      | v1_funct_2(X1,X0,X0) != iProver_top
% 3.23/0.97      | v3_funct_2(X1,X0,X0) != iProver_top
% 3.23/0.97      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 3.23/0.97      | v1_funct_1(X1) != iProver_top ),
% 3.23/0.97      inference(forward_subsumption_resolution,
% 3.23/0.97                [status(thm)],
% 3.23/0.97                [c_6161,c_1375]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_7649,plain,
% 3.23/0.97      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1) = k5_relat_1(k2_funct_2(sK0,sK1),sK1)
% 3.23/0.97      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.23/0.97      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.23/0.97      | v1_funct_1(sK1) != iProver_top ),
% 3.23/0.97      inference(superposition,[status(thm)],[c_1370,c_7643]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_4,plain,
% 3.23/0.97      ( ~ v1_funct_1(X0)
% 3.23/0.97      | ~ v2_funct_1(X0)
% 3.23/0.97      | ~ v1_relat_1(X0)
% 3.23/0.97      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
% 3.23/0.97      inference(cnf_transformation,[],[f85]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_1391,plain,
% 3.23/0.97      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
% 3.23/0.97      | v1_funct_1(X0) != iProver_top
% 3.23/0.97      | v2_funct_1(X0) != iProver_top
% 3.23/0.97      | v1_relat_1(X0) != iProver_top ),
% 3.23/0.97      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_4293,plain,
% 3.23/0.97      ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1))
% 3.23/0.97      | v2_funct_1(sK1) != iProver_top
% 3.23/0.97      | v1_relat_1(sK1) != iProver_top ),
% 3.23/0.97      inference(superposition,[status(thm)],[c_1367,c_1391]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_11,plain,
% 3.23/0.97      ( ~ v3_funct_2(X0,X1,X2)
% 3.23/0.97      | v2_funct_2(X0,X2)
% 3.23/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.23/0.97      | ~ v1_funct_1(X0) ),
% 3.23/0.97      inference(cnf_transformation,[],[f61]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_7,plain,
% 3.23/0.97      ( v5_relat_1(X0,X1)
% 3.23/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.23/0.97      inference(cnf_transformation,[],[f55]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_21,plain,
% 3.23/0.97      ( ~ v2_funct_2(X0,X1)
% 3.23/0.97      | ~ v5_relat_1(X0,X1)
% 3.23/0.97      | ~ v1_relat_1(X0)
% 3.23/0.97      | k2_relat_1(X0) = X1 ),
% 3.23/0.97      inference(cnf_transformation,[],[f68]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_363,plain,
% 3.23/0.97      ( ~ v2_funct_2(X0,X1)
% 3.23/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.23/0.97      | ~ v1_relat_1(X0)
% 3.23/0.97      | k2_relat_1(X0) = X1 ),
% 3.23/0.97      inference(resolution,[status(thm)],[c_7,c_21]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_375,plain,
% 3.23/0.97      ( ~ v2_funct_2(X0,X1)
% 3.23/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.23/0.97      | k2_relat_1(X0) = X1 ),
% 3.23/0.97      inference(forward_subsumption_resolution,[status(thm)],[c_363,c_6]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_406,plain,
% 3.23/0.97      ( ~ v3_funct_2(X0,X1,X2)
% 3.23/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.23/0.97      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.23/0.97      | ~ v1_funct_1(X0)
% 3.23/0.97      | X3 != X0
% 3.23/0.97      | X5 != X2
% 3.23/0.97      | k2_relat_1(X3) = X5 ),
% 3.23/0.97      inference(resolution_lifted,[status(thm)],[c_11,c_375]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_407,plain,
% 3.23/0.97      ( ~ v3_funct_2(X0,X1,X2)
% 3.23/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.23/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 3.23/0.97      | ~ v1_funct_1(X0)
% 3.23/0.97      | k2_relat_1(X0) = X2 ),
% 3.23/0.97      inference(unflattening,[status(thm)],[c_406]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_1366,plain,
% 3.23/0.97      ( k2_relat_1(X0) = X1
% 3.23/0.97      | v3_funct_2(X0,X2,X1) != iProver_top
% 3.23/0.97      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 3.23/0.97      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
% 3.23/0.97      | v1_funct_1(X0) != iProver_top ),
% 3.23/0.97      inference(predicate_to_equality,[status(thm)],[c_407]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_1764,plain,
% 3.23/0.97      ( k2_relat_1(sK1) = sK0
% 3.23/0.97      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.23/0.97      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 3.23/0.97      | v1_funct_1(sK1) != iProver_top ),
% 3.23/0.97      inference(superposition,[status(thm)],[c_1370,c_1366]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_1710,plain,
% 3.23/0.97      ( ~ v3_funct_2(sK1,X0,X1)
% 3.23/0.97      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.23/0.97      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.23/0.97      | ~ v1_funct_1(sK1)
% 3.23/0.97      | k2_relat_1(sK1) = X1 ),
% 3.23/0.97      inference(instantiation,[status(thm)],[c_407]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_1915,plain,
% 3.23/0.97      ( ~ v3_funct_2(sK1,sK0,sK0)
% 3.23/0.97      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
% 3.23/0.97      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.23/0.97      | ~ v1_funct_1(sK1)
% 3.23/0.97      | k2_relat_1(sK1) = sK0 ),
% 3.23/0.97      inference(instantiation,[status(thm)],[c_1710]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_2036,plain,
% 3.23/0.97      ( ~ v3_funct_2(sK1,sK0,sK0)
% 3.23/0.97      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.23/0.97      | ~ v1_funct_1(sK1)
% 3.23/0.97      | k2_relat_1(sK1) = sK0 ),
% 3.23/0.97      inference(instantiation,[status(thm)],[c_1915]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_2198,plain,
% 3.23/0.97      ( k2_relat_1(sK1) = sK0 ),
% 3.23/0.97      inference(global_propositional_subsumption,
% 3.23/0.97                [status(thm)],
% 3.23/0.97                [c_1764,c_33,c_31,c_30,c_2036]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_4294,plain,
% 3.23/0.97      ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
% 3.23/0.97      | v2_funct_1(sK1) != iProver_top
% 3.23/0.97      | v1_relat_1(sK1) != iProver_top ),
% 3.23/0.97      inference(light_normalisation,[status(thm)],[c_4293,c_2198]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_1647,plain,
% 3.23/0.97      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.23/0.97      | v1_relat_1(sK1) = iProver_top ),
% 3.23/0.97      inference(predicate_to_equality,[status(thm)],[c_1646]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_1830,plain,
% 3.23/0.97      ( v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.23/0.97      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.23/0.97      | v1_funct_1(sK1) != iProver_top
% 3.23/0.97      | v2_funct_1(sK1) = iProver_top ),
% 3.23/0.97      inference(predicate_to_equality,[status(thm)],[c_1829]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_5445,plain,
% 3.23/0.97      ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(sK0) ),
% 3.23/0.97      inference(global_propositional_subsumption,
% 3.23/0.97                [status(thm)],
% 3.23/0.97                [c_4294,c_34,c_36,c_37,c_1647,c_1830]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_7672,plain,
% 3.23/0.97      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
% 3.23/0.97      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 3.23/0.97      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 3.23/0.97      | v1_funct_1(sK1) != iProver_top ),
% 3.23/0.97      inference(light_normalisation,[status(thm)],[c_7649,c_3146,c_5445]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_7376,plain,
% 3.23/0.97      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k5_relat_1(k2_funct_1(sK1),sK1)
% 3.23/0.97      | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
% 3.23/0.97      inference(superposition,[status(thm)],[c_7367,c_3806]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_7442,plain,
% 3.23/0.97      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
% 3.23/0.97      | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
% 3.23/0.97      inference(light_normalisation,[status(thm)],[c_7376,c_5445]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_7823,plain,
% 3.23/0.97      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0) ),
% 3.23/0.97      inference(global_propositional_subsumption,
% 3.23/0.97                [status(thm)],
% 3.23/0.97                [c_7672,c_34,c_35,c_36,c_4468,c_7442]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_29,negated_conjecture,
% 3.23/0.97      ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
% 3.23/0.97      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
% 3.23/0.97      inference(cnf_transformation,[],[f82]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_1371,plain,
% 3.23/0.97      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) != iProver_top
% 3.23/0.97      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) != iProver_top ),
% 3.23/0.97      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_3149,plain,
% 3.23/0.97      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) != iProver_top
% 3.23/0.97      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
% 3.23/0.97      inference(demodulation,[status(thm)],[c_3146,c_1371]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_7826,plain,
% 3.23/0.97      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top
% 3.23/0.97      | r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
% 3.23/0.97      inference(demodulation,[status(thm)],[c_7823,c_3149]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_26,plain,
% 3.23/0.97      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.23/0.97      inference(cnf_transformation,[],[f74]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_1374,plain,
% 3.23/0.97      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 3.23/0.97      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_9,plain,
% 3.23/0.97      ( r2_relset_1(X0,X1,X2,X2)
% 3.23/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.23/0.97      inference(cnf_transformation,[],[f87]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_1387,plain,
% 3.23/0.97      ( r2_relset_1(X0,X1,X2,X2) = iProver_top
% 3.23/0.97      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.23/0.97      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_2888,plain,
% 3.23/0.97      ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0)) = iProver_top ),
% 3.23/0.97      inference(superposition,[status(thm)],[c_1374,c_1387]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_7831,plain,
% 3.23/0.97      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
% 3.23/0.97      inference(forward_subsumption_resolution,
% 3.23/0.97                [status(thm)],
% 3.23/0.97                [c_7826,c_2888]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_9077,plain,
% 3.23/0.97      ( r2_relset_1(sK0,sK0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
% 3.23/0.97      inference(demodulation,[status(thm)],[c_9074,c_7831]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_9261,plain,
% 3.23/0.97      ( sK0 = k1_xboole_0
% 3.23/0.97      | r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
% 3.23/0.97      inference(superposition,[status(thm)],[c_5811,c_9077]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_9266,plain,
% 3.23/0.97      ( sK0 = k1_xboole_0 ),
% 3.23/0.97      inference(forward_subsumption_resolution,
% 3.23/0.97                [status(thm)],
% 3.23/0.97                [c_9261,c_2888]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_9267,plain,
% 3.23/0.97      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(k1_xboole_0)) != iProver_top ),
% 3.23/0.97      inference(demodulation,[status(thm)],[c_9266,c_9077]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_0,plain,
% 3.23/0.97      ( ~ v1_relat_1(X0)
% 3.23/0.97      | k2_relat_1(X0) != k1_xboole_0
% 3.23/0.97      | k1_xboole_0 = X0 ),
% 3.23/0.97      inference(cnf_transformation,[],[f49]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_1393,plain,
% 3.23/0.97      ( k2_relat_1(X0) != k1_xboole_0
% 3.23/0.97      | k1_xboole_0 = X0
% 3.23/0.97      | v1_relat_1(X0) != iProver_top ),
% 3.23/0.97      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_2201,plain,
% 3.23/0.97      ( sK1 = k1_xboole_0
% 3.23/0.97      | sK0 != k1_xboole_0
% 3.23/0.97      | v1_relat_1(sK1) != iProver_top ),
% 3.23/0.97      inference(superposition,[status(thm)],[c_2198,c_1393]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_2202,plain,
% 3.23/0.97      ( ~ v1_relat_1(sK1) | sK1 = k1_xboole_0 | sK0 != k1_xboole_0 ),
% 3.23/0.97      inference(predicate_to_equality_rev,[status(thm)],[c_2201]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_2204,plain,
% 3.23/0.97      ( sK0 != k1_xboole_0 | sK1 = k1_xboole_0 ),
% 3.23/0.97      inference(global_propositional_subsumption,
% 3.23/0.97                [status(thm)],
% 3.23/0.97                [c_2201,c_30,c_1646,c_2202]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_2205,plain,
% 3.23/0.97      ( sK1 = k1_xboole_0 | sK0 != k1_xboole_0 ),
% 3.23/0.97      inference(renaming,[status(thm)],[c_2204]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_9298,plain,
% 3.23/0.97      ( sK1 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.23/0.97      inference(demodulation,[status(thm)],[c_9266,c_2205]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_9311,plain,
% 3.23/0.97      ( sK1 = k1_xboole_0 ),
% 3.23/0.97      inference(equality_resolution_simp,[status(thm)],[c_9298]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_9454,plain,
% 3.23/0.97      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_relat_1(k1_xboole_0)),k6_partfun1(k1_xboole_0)) != iProver_top ),
% 3.23/0.97      inference(light_normalisation,[status(thm)],[c_9267,c_9311]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_3,plain,
% 3.23/0.97      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 3.23/0.97      inference(cnf_transformation,[],[f84]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_1,plain,
% 3.23/0.97      ( ~ v1_relat_1(X0)
% 3.23/0.97      | k1_relat_1(X0) != k1_xboole_0
% 3.23/0.97      | k1_xboole_0 = X0 ),
% 3.23/0.97      inference(cnf_transformation,[],[f48]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_1392,plain,
% 3.23/0.97      ( k1_relat_1(X0) != k1_xboole_0
% 3.23/0.97      | k1_xboole_0 = X0
% 3.23/0.97      | v1_relat_1(X0) != iProver_top ),
% 3.23/0.97      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_1906,plain,
% 3.23/0.97      ( k6_partfun1(X0) = k1_xboole_0
% 3.23/0.97      | k1_xboole_0 != X0
% 3.23/0.97      | v1_relat_1(k6_partfun1(X0)) != iProver_top ),
% 3.23/0.97      inference(superposition,[status(thm)],[c_3,c_1392]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_45,plain,
% 3.23/0.97      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 3.23/0.97      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_1641,plain,
% 3.23/0.97      ( ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 3.23/0.97      | v1_relat_1(k6_partfun1(X0)) ),
% 3.23/0.97      inference(instantiation,[status(thm)],[c_6]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_1642,plain,
% 3.23/0.97      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 3.23/0.97      | v1_relat_1(k6_partfun1(X0)) = iProver_top ),
% 3.23/0.97      inference(predicate_to_equality,[status(thm)],[c_1641]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_2023,plain,
% 3.23/0.97      ( k1_xboole_0 != X0 | k6_partfun1(X0) = k1_xboole_0 ),
% 3.23/0.97      inference(global_propositional_subsumption,
% 3.23/0.97                [status(thm)],
% 3.23/0.97                [c_1906,c_45,c_1642]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_2024,plain,
% 3.23/0.97      ( k6_partfun1(X0) = k1_xboole_0 | k1_xboole_0 != X0 ),
% 3.23/0.97      inference(renaming,[status(thm)],[c_2023]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_2028,plain,
% 3.23/0.97      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 3.23/0.97      inference(equality_resolution,[status(thm)],[c_2024]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_2317,plain,
% 3.23/0.97      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.23/0.97      inference(superposition,[status(thm)],[c_2028,c_3]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_9456,plain,
% 3.23/0.97      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.23/0.97      inference(light_normalisation,[status(thm)],[c_9454,c_2028,c_2317]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_2316,plain,
% 3.23/0.97      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.23/0.97      inference(superposition,[status(thm)],[c_2028,c_1374]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_94,plain,
% 3.23/0.97      ( r2_relset_1(X0,X1,X2,X2) = iProver_top
% 3.23/0.97      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.23/0.97      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(c_96,plain,
% 3.23/0.97      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top
% 3.23/0.97      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 3.23/0.97      inference(instantiation,[status(thm)],[c_94]) ).
% 3.23/0.97  
% 3.23/0.97  cnf(contradiction,plain,
% 3.23/0.97      ( $false ),
% 3.23/0.97      inference(minisat,[status(thm)],[c_9456,c_2316,c_96]) ).
% 3.23/0.97  
% 3.23/0.97  
% 3.23/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 3.23/0.97  
% 3.23/0.97  ------                               Statistics
% 3.23/0.97  
% 3.23/0.97  ------ General
% 3.23/0.97  
% 3.23/0.97  abstr_ref_over_cycles:                  0
% 3.23/0.97  abstr_ref_under_cycles:                 0
% 3.23/0.97  gc_basic_clause_elim:                   0
% 3.23/0.97  forced_gc_time:                         0
% 3.23/0.97  parsing_time:                           0.01
% 3.23/0.97  unif_index_cands_time:                  0.
% 3.23/0.97  unif_index_add_time:                    0.
% 3.23/0.97  orderings_time:                         0.
% 3.23/0.97  out_proof_time:                         0.015
% 3.23/0.97  total_time:                             0.282
% 3.23/0.97  num_of_symbols:                         53
% 3.23/0.97  num_of_terms:                           9198
% 3.23/0.97  
% 3.23/0.97  ------ Preprocessing
% 3.23/0.97  
% 3.23/0.97  num_of_splits:                          0
% 3.23/0.97  num_of_split_atoms:                     0
% 3.23/0.97  num_of_reused_defs:                     0
% 3.23/0.97  num_eq_ax_congr_red:                    17
% 3.23/0.97  num_of_sem_filtered_clauses:            1
% 3.23/0.97  num_of_subtypes:                        0
% 3.23/0.97  monotx_restored_types:                  0
% 3.23/0.97  sat_num_of_epr_types:                   0
% 3.23/0.97  sat_num_of_non_cyclic_types:            0
% 3.23/0.97  sat_guarded_non_collapsed_types:        0
% 3.23/0.97  num_pure_diseq_elim:                    0
% 3.23/0.97  simp_replaced_by:                       0
% 3.23/0.97  res_preprocessed:                       156
% 3.23/0.97  prep_upred:                             0
% 3.23/0.97  prep_unflattend:                        6
% 3.23/0.97  smt_new_axioms:                         0
% 3.23/0.97  pred_elim_cands:                        7
% 3.23/0.97  pred_elim:                              2
% 3.23/0.97  pred_elim_cl:                           3
% 3.23/0.97  pred_elim_cycles:                       6
% 3.23/0.97  merged_defs:                            0
% 3.23/0.97  merged_defs_ncl:                        0
% 3.23/0.97  bin_hyper_res:                          0
% 3.23/0.97  prep_cycles:                            4
% 3.23/0.97  pred_elim_time:                         0.006
% 3.23/0.97  splitting_time:                         0.
% 3.23/0.97  sem_filter_time:                        0.
% 3.23/0.97  monotx_time:                            0.002
% 3.23/0.97  subtype_inf_time:                       0.
% 3.23/0.97  
% 3.23/0.97  ------ Problem properties
% 3.23/0.97  
% 3.23/0.97  clauses:                                30
% 3.23/0.97  conjectures:                            5
% 3.23/0.97  epr:                                    3
% 3.23/0.97  horn:                                   26
% 3.23/0.97  ground:                                 5
% 3.23/0.97  unary:                                  7
% 3.23/0.97  binary:                                 4
% 3.23/0.97  lits:                                   93
% 3.23/0.97  lits_eq:                                22
% 3.23/0.97  fd_pure:                                0
% 3.23/0.97  fd_pseudo:                              0
% 3.23/0.97  fd_cond:                                5
% 3.23/0.97  fd_pseudo_cond:                         2
% 3.23/0.97  ac_symbols:                             0
% 3.23/0.97  
% 3.23/0.97  ------ Propositional Solver
% 3.23/0.97  
% 3.23/0.97  prop_solver_calls:                      27
% 3.23/0.97  prop_fast_solver_calls:                 1358
% 3.23/0.97  smt_solver_calls:                       0
% 3.23/0.97  smt_fast_solver_calls:                  0
% 3.23/0.97  prop_num_of_clauses:                    3588
% 3.23/0.97  prop_preprocess_simplified:             9796
% 3.23/0.97  prop_fo_subsumed:                       59
% 3.23/0.97  prop_solver_time:                       0.
% 3.23/0.97  smt_solver_time:                        0.
% 3.23/0.97  smt_fast_solver_time:                   0.
% 3.23/0.97  prop_fast_solver_time:                  0.
% 3.23/0.97  prop_unsat_core_time:                   0.
% 3.23/0.97  
% 3.23/0.97  ------ QBF
% 3.23/0.97  
% 3.23/0.97  qbf_q_res:                              0
% 3.23/0.97  qbf_num_tautologies:                    0
% 3.23/0.97  qbf_prep_cycles:                        0
% 3.23/0.97  
% 3.23/0.97  ------ BMC1
% 3.23/0.97  
% 3.23/0.97  bmc1_current_bound:                     -1
% 3.23/0.97  bmc1_last_solved_bound:                 -1
% 3.23/0.97  bmc1_unsat_core_size:                   -1
% 3.23/0.97  bmc1_unsat_core_parents_size:           -1
% 3.23/0.97  bmc1_merge_next_fun:                    0
% 3.23/0.97  bmc1_unsat_core_clauses_time:           0.
% 3.23/0.97  
% 3.23/0.97  ------ Instantiation
% 3.23/0.97  
% 3.23/0.97  inst_num_of_clauses:                    1074
% 3.23/0.97  inst_num_in_passive:                    348
% 3.23/0.97  inst_num_in_active:                     433
% 3.23/0.97  inst_num_in_unprocessed:                293
% 3.23/0.97  inst_num_of_loops:                      470
% 3.23/0.97  inst_num_of_learning_restarts:          0
% 3.23/0.97  inst_num_moves_active_passive:          36
% 3.23/0.97  inst_lit_activity:                      0
% 3.23/0.97  inst_lit_activity_moves:                0
% 3.23/0.97  inst_num_tautologies:                   0
% 3.23/0.97  inst_num_prop_implied:                  0
% 3.23/0.97  inst_num_existing_simplified:           0
% 3.23/0.97  inst_num_eq_res_simplified:             0
% 3.23/0.97  inst_num_child_elim:                    0
% 3.23/0.97  inst_num_of_dismatching_blockings:      139
% 3.23/0.97  inst_num_of_non_proper_insts:           737
% 3.23/0.97  inst_num_of_duplicates:                 0
% 3.23/0.97  inst_inst_num_from_inst_to_res:         0
% 3.23/0.97  inst_dismatching_checking_time:         0.
% 3.23/0.97  
% 3.23/0.97  ------ Resolution
% 3.23/0.97  
% 3.23/0.97  res_num_of_clauses:                     0
% 3.23/0.97  res_num_in_passive:                     0
% 3.23/0.97  res_num_in_active:                      0
% 3.23/0.97  res_num_of_loops:                       160
% 3.23/0.97  res_forward_subset_subsumed:            25
% 3.23/0.97  res_backward_subset_subsumed:           0
% 3.23/0.97  res_forward_subsumed:                   0
% 3.23/0.97  res_backward_subsumed:                  0
% 3.23/0.97  res_forward_subsumption_resolution:     2
% 3.23/0.97  res_backward_subsumption_resolution:    0
% 3.23/0.97  res_clause_to_clause_subsumption:       251
% 3.23/0.97  res_orphan_elimination:                 0
% 3.23/0.97  res_tautology_del:                      25
% 3.23/0.97  res_num_eq_res_simplified:              0
% 3.23/0.97  res_num_sel_changes:                    0
% 3.23/0.97  res_moves_from_active_to_pass:          0
% 3.23/0.97  
% 3.23/0.97  ------ Superposition
% 3.23/0.97  
% 3.23/0.97  sup_time_total:                         0.
% 3.23/0.97  sup_time_generating:                    0.
% 3.23/0.97  sup_time_sim_full:                      0.
% 3.23/0.97  sup_time_sim_immed:                     0.
% 3.23/0.97  
% 3.23/0.97  sup_num_of_clauses:                     98
% 3.23/0.97  sup_num_in_active:                      51
% 3.23/0.97  sup_num_in_passive:                     47
% 3.23/0.97  sup_num_of_loops:                       93
% 3.23/0.97  sup_fw_superposition:                   78
% 3.23/0.97  sup_bw_superposition:                   54
% 3.23/0.97  sup_immediate_simplified:               65
% 3.23/0.97  sup_given_eliminated:                   0
% 3.23/0.97  comparisons_done:                       0
% 3.23/0.97  comparisons_avoided:                    0
% 3.23/0.97  
% 3.23/0.97  ------ Simplifications
% 3.23/0.97  
% 3.23/0.97  
% 3.23/0.97  sim_fw_subset_subsumed:                 8
% 3.23/0.97  sim_bw_subset_subsumed:                 5
% 3.23/0.97  sim_fw_subsumed:                        4
% 3.23/0.97  sim_bw_subsumed:                        0
% 3.23/0.97  sim_fw_subsumption_res:                 3
% 3.23/0.97  sim_bw_subsumption_res:                 0
% 3.23/0.97  sim_tautology_del:                      0
% 3.23/0.97  sim_eq_tautology_del:                   18
% 3.23/0.97  sim_eq_res_simp:                        2
% 3.23/0.97  sim_fw_demodulated:                     6
% 3.23/0.97  sim_bw_demodulated:                     58
% 3.23/0.97  sim_light_normalised:                   53
% 3.23/0.97  sim_joinable_taut:                      0
% 3.23/0.97  sim_joinable_simp:                      0
% 3.23/0.97  sim_ac_normalised:                      0
% 3.23/0.97  sim_smt_subsumption:                    0
% 3.23/0.97  
%------------------------------------------------------------------------------
