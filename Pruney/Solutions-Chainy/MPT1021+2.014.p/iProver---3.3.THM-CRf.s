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
% DateTime   : Thu Dec  3 12:07:20 EST 2020

% Result     : Theorem 8.00s
% Output     : CNFRefutation 8.00s
% Verified   : 
% Statistics : Number of formulae       :  218 (4792 expanded)
%              Number of clauses        :  135 (1544 expanded)
%              Number of leaves         :   20 ( 895 expanded)
%              Depth                    :   31
%              Number of atoms          :  737 (21359 expanded)
%              Number of equality atoms :  333 (2614 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   13 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f25,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) ) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f56,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f57,plain,(
    ? [X0,X1] :
      ( ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0))
        | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f56])).

fof(f65,plain,
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

fof(f66,plain,
    ( ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) )
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK1,sK0,sK0)
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f57,f65])).

fof(f116,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f66])).

fof(f16,axiom,(
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

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f63,plain,(
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
    inference(nnf_transformation,[],[f43])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f114,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f66])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f40])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f44])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f97,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f113,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f66])).

fof(f115,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f66])).

fof(f23,axiom,(
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
    inference(ennf_transformation,[],[f23])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f52])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f49,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f48])).

fof(f104,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_funct_1(X2))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f33,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f81,plain,(
    ! [X0] :
      ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f22,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f106,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f22])).

fof(f121,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f81,f106])).

fof(f18,axiom,(
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

fof(f46,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f46])).

fof(f102,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f99,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k2_funct_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f82,plain,(
    ! [X0] :
      ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f120,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f82,f106])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_1(X1) = k2_funct_2(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f50])).

fof(f105,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f117,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f66])).

fof(f19,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f103,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f38])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f31,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f78,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f8,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f119,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f79,f106])).

fof(f77,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

cnf(c_46,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_2415,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_29,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2429,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_8603,plain,
    ( k1_relset_1(sK0,sK0,sK1) = sK0
    | sK0 = k1_xboole_0
    | v1_funct_2(sK1,sK0,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2415,c_2429])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2438,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_5338,plain,
    ( k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_2415,c_2438])).

cnf(c_8613,plain,
    ( k1_relat_1(sK1) = sK0
    | sK0 = k1_xboole_0
    | v1_funct_2(sK1,sK0,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8603,c_5338])).

cnf(c_48,negated_conjecture,
    ( v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_51,plain,
    ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_8878,plain,
    ( sK0 = k1_xboole_0
    | k1_relat_1(sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8613,c_51])).

cnf(c_8879,plain,
    ( k1_relat_1(sK1) = sK0
    | sK0 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_8878])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2437,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4484,plain,
    ( k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_2415,c_2437])).

cnf(c_21,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_17,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_31,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_584,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_17,c_31])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_596,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | k2_relat_1(X0) = X1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_584,c_16])).

cnf(c_627,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | X3 != X0
    | X5 != X2
    | k2_relat_1(X3) = X5 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_596])).

cnf(c_628,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(unflattening,[status(thm)],[c_627])).

cnf(c_2411,plain,
    ( k2_relat_1(X0) = X1
    | v3_funct_2(X0,X2,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_628])).

cnf(c_3548,plain,
    ( k2_relat_1(sK1) = sK0
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2415,c_2411])).

cnf(c_49,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_47,negated_conjecture,
    ( v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_2924,plain,
    ( ~ v3_funct_2(sK1,X0,X1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(sK1)
    | k2_relat_1(sK1) = X1 ),
    inference(instantiation,[status(thm)],[c_628])).

cnf(c_3110,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | k2_relat_1(sK1) = sK0 ),
    inference(instantiation,[status(thm)],[c_2924])).

cnf(c_3261,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | k2_relat_1(sK1) = sK0 ),
    inference(instantiation,[status(thm)],[c_3110])).

cnf(c_3873,plain,
    ( k2_relat_1(sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3548,c_49,c_47,c_46,c_3261])).

cnf(c_4496,plain,
    ( k2_relset_1(sK0,sK0,sK1) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_4484,c_3873])).

cnf(c_39,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f109])).

cnf(c_2421,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_7938,plain,
    ( v1_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v2_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4496,c_2421])).

cnf(c_50,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_52,plain,
    ( v3_funct_2(sK1,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_53,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_22,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2891,plain,
    ( ~ v3_funct_2(sK1,X0,X1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK1)
    | v2_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_3048,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | v2_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_2891])).

cnf(c_3049,plain,
    ( v3_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v2_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3048])).

cnf(c_2966,plain,
    ( ~ v1_funct_2(sK1,X0,X1)
    | m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | k2_relset_1(X0,X1,sK1) != X1 ),
    inference(instantiation,[status(thm)],[c_39])).

cnf(c_3271,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | k2_relset_1(sK0,sK0,sK1) != sK0 ),
    inference(instantiation,[status(thm)],[c_2966])).

cnf(c_3272,plain,
    ( k2_relset_1(sK0,sK0,sK1) != sK0
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v2_funct_1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3271])).

cnf(c_11631,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7938,c_50,c_51,c_52,c_53,c_3049,c_3272,c_4496])).

cnf(c_37,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_2423,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_17873,plain,
    ( k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11631,c_2423])).

cnf(c_41,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f107])).

cnf(c_2946,plain,
    ( ~ v1_funct_2(sK1,X0,X1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(k2_funct_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | k2_relset_1(X0,X1,sK1) != X1 ),
    inference(instantiation,[status(thm)],[c_41])).

cnf(c_3268,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v1_funct_1(k2_funct_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | k2_relset_1(sK0,sK0,sK1) != sK0 ),
    inference(instantiation,[status(thm)],[c_2946])).

cnf(c_3269,plain,
    ( k2_relset_1(sK0,sK0,sK1) != sK0
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK1)) = iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v2_funct_1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3268])).

cnf(c_34900,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17873,c_50,c_51,c_52,c_53,c_3049,c_3269,c_4496])).

cnf(c_34901,plain,
    ( k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_34900])).

cnf(c_34914,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k5_relat_1(sK1,k2_funct_1(sK1))
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2415,c_34901])).

cnf(c_2412,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_15,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_2440,plain,
    ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_6732,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
    | v2_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2412,c_2440])).

cnf(c_2828,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2843,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_7451,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6732,c_49,c_47,c_46,c_2828,c_2843,c_3048])).

cnf(c_34964,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
    | v1_funct_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_34914,c_7451])).

cnf(c_35061,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_34964,c_50])).

cnf(c_32,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_2428,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_17872,plain,
    ( k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2415,c_2423])).

cnf(c_18014,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17872,c_50])).

cnf(c_18015,plain,
    ( k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_18014])).

cnf(c_18025,plain,
    ( k1_partfun1(X0,X0,sK0,sK0,k2_funct_2(X0,X1),sK1) = k5_relat_1(k2_funct_2(X0,X1),sK1)
    | v1_funct_2(X1,X0,X0) != iProver_top
    | v3_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(k2_funct_2(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2428,c_18015])).

cnf(c_35,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_2(X1,X0)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_2425,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_2(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_22026,plain,
    ( k1_partfun1(X0,X0,sK0,sK0,k2_funct_2(X0,X1),sK1) = k5_relat_1(k2_funct_2(X0,X1),sK1)
    | v1_funct_2(X1,X0,X0) != iProver_top
    | v3_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_18025,c_2425])).

cnf(c_22035,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1) = k5_relat_1(k2_funct_2(sK0,sK1),sK1)
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2415,c_22026])).

cnf(c_14,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_2441,plain,
    ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_6753,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1))
    | v2_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2412,c_2441])).

cnf(c_6764,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
    | v2_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6753,c_3873])).

cnf(c_2829,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2828])).

cnf(c_7455,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6764,c_50,c_52,c_53,c_2829,c_3049])).

cnf(c_38,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_2422,plain,
    ( k2_funct_2(X0,X1) = k2_funct_1(X1)
    | v1_funct_2(X1,X0,X0) != iProver_top
    | v3_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_16173,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2415,c_2422])).

cnf(c_2941,plain,
    ( ~ v1_funct_2(sK1,X0,X0)
    | ~ v3_funct_2(sK1,X0,X0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v1_funct_1(sK1)
    | k2_funct_2(X0,sK1) = k2_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_38])).

cnf(c_3115,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_2941])).

cnf(c_16436,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16173,c_49,c_48,c_47,c_46,c_3115])).

cnf(c_22086,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_22035,c_7455,c_16436])).

cnf(c_18029,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k5_relat_1(k2_funct_1(sK1),sK1)
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11631,c_18015])).

cnf(c_18062,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_18029,c_7455])).

cnf(c_22166,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_22086,c_50,c_51,c_52,c_53,c_3049,c_3269,c_4496,c_18062])).

cnf(c_45,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_2416,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) != iProver_top
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_16444,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) != iProver_top
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_16436,c_2416])).

cnf(c_22169,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top
    | r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_22166,c_16444])).

cnf(c_35064,plain,
    ( r2_relset_1(sK0,sK0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(sK0)) != iProver_top
    | r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_35061,c_22169])).

cnf(c_36,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_2424,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_20,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2436,plain,
    ( r2_relset_1(X0,X1,X2,X2) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_8012,plain,
    ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0)) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2424,c_2436])).

cnf(c_25769,plain,
    ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2424,c_8012])).

cnf(c_35132,plain,
    ( r2_relset_1(sK0,sK0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_35064,c_25769])).

cnf(c_35134,plain,
    ( sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8879,c_35132])).

cnf(c_35139,plain,
    ( sK0 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_35134,c_25769])).

cnf(c_35140,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_35139,c_35132])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2443,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4435,plain,
    ( sK1 = k1_xboole_0
    | sK0 != k1_xboole_0
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3873,c_2443])).

cnf(c_4442,plain,
    ( ~ v1_relat_1(sK1)
    | sK1 = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4435])).

cnf(c_4618,plain,
    ( sK0 != k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4435,c_46,c_2828,c_4442])).

cnf(c_4619,plain,
    ( sK1 = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_4618])).

cnf(c_35330,plain,
    ( sK1 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_35139,c_4619])).

cnf(c_35351,plain,
    ( sK1 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_35330])).

cnf(c_36205,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_relat_1(k1_xboole_0)),k6_partfun1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_35140,c_35351])).

cnf(c_13,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f119])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2442,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3761,plain,
    ( k6_partfun1(X0) = k1_xboole_0
    | k1_xboole_0 != X0
    | v1_relat_1(k6_partfun1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_2442])).

cnf(c_77,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_2823,plain,
    ( ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | v1_relat_1(k6_partfun1(X0)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2824,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_relat_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2823])).

cnf(c_4444,plain,
    ( k1_xboole_0 != X0
    | k6_partfun1(X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3761,c_77,c_2824])).

cnf(c_4445,plain,
    ( k6_partfun1(X0) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(renaming,[status(thm)],[c_4444])).

cnf(c_4449,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_4445])).

cnf(c_4829,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4449,c_13])).

cnf(c_36207,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_36205,c_4449,c_4829])).

cnf(c_7,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2813,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2816,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2813])).

cnf(c_2818,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2816])).

cnf(c_123,plain,
    ( r2_relset_1(X0,X1,X2,X2) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_125,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_123])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_36207,c_2818,c_125])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:15:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  % Running in FOF mode
% 8.00/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.00/1.50  
% 8.00/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 8.00/1.50  
% 8.00/1.50  ------  iProver source info
% 8.00/1.50  
% 8.00/1.50  git: date: 2020-06-30 10:37:57 +0100
% 8.00/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 8.00/1.50  git: non_committed_changes: false
% 8.00/1.50  git: last_make_outside_of_git: false
% 8.00/1.50  
% 8.00/1.50  ------ 
% 8.00/1.50  
% 8.00/1.50  ------ Input Options
% 8.00/1.50  
% 8.00/1.50  --out_options                           all
% 8.00/1.50  --tptp_safe_out                         true
% 8.00/1.50  --problem_path                          ""
% 8.00/1.50  --include_path                          ""
% 8.00/1.50  --clausifier                            res/vclausify_rel
% 8.00/1.50  --clausifier_options                    --mode clausify
% 8.00/1.50  --stdin                                 false
% 8.00/1.50  --stats_out                             all
% 8.00/1.50  
% 8.00/1.50  ------ General Options
% 8.00/1.50  
% 8.00/1.50  --fof                                   false
% 8.00/1.50  --time_out_real                         305.
% 8.00/1.50  --time_out_virtual                      -1.
% 8.00/1.50  --symbol_type_check                     false
% 8.00/1.50  --clausify_out                          false
% 8.00/1.50  --sig_cnt_out                           false
% 8.00/1.50  --trig_cnt_out                          false
% 8.00/1.50  --trig_cnt_out_tolerance                1.
% 8.00/1.50  --trig_cnt_out_sk_spl                   false
% 8.00/1.50  --abstr_cl_out                          false
% 8.00/1.50  
% 8.00/1.50  ------ Global Options
% 8.00/1.50  
% 8.00/1.50  --schedule                              default
% 8.00/1.50  --add_important_lit                     false
% 8.00/1.50  --prop_solver_per_cl                    1000
% 8.00/1.50  --min_unsat_core                        false
% 8.00/1.50  --soft_assumptions                      false
% 8.00/1.50  --soft_lemma_size                       3
% 8.00/1.50  --prop_impl_unit_size                   0
% 8.00/1.50  --prop_impl_unit                        []
% 8.00/1.50  --share_sel_clauses                     true
% 8.00/1.50  --reset_solvers                         false
% 8.00/1.50  --bc_imp_inh                            [conj_cone]
% 8.00/1.50  --conj_cone_tolerance                   3.
% 8.00/1.50  --extra_neg_conj                        none
% 8.00/1.50  --large_theory_mode                     true
% 8.00/1.50  --prolific_symb_bound                   200
% 8.00/1.50  --lt_threshold                          2000
% 8.00/1.50  --clause_weak_htbl                      true
% 8.00/1.50  --gc_record_bc_elim                     false
% 8.00/1.50  
% 8.00/1.50  ------ Preprocessing Options
% 8.00/1.50  
% 8.00/1.50  --preprocessing_flag                    true
% 8.00/1.50  --time_out_prep_mult                    0.1
% 8.00/1.50  --splitting_mode                        input
% 8.00/1.50  --splitting_grd                         true
% 8.00/1.50  --splitting_cvd                         false
% 8.00/1.50  --splitting_cvd_svl                     false
% 8.00/1.50  --splitting_nvd                         32
% 8.00/1.50  --sub_typing                            true
% 8.00/1.50  --prep_gs_sim                           true
% 8.00/1.50  --prep_unflatten                        true
% 8.00/1.50  --prep_res_sim                          true
% 8.00/1.50  --prep_upred                            true
% 8.00/1.50  --prep_sem_filter                       exhaustive
% 8.00/1.50  --prep_sem_filter_out                   false
% 8.00/1.50  --pred_elim                             true
% 8.00/1.50  --res_sim_input                         true
% 8.00/1.50  --eq_ax_congr_red                       true
% 8.00/1.50  --pure_diseq_elim                       true
% 8.00/1.50  --brand_transform                       false
% 8.00/1.50  --non_eq_to_eq                          false
% 8.00/1.50  --prep_def_merge                        true
% 8.00/1.50  --prep_def_merge_prop_impl              false
% 8.00/1.50  --prep_def_merge_mbd                    true
% 8.00/1.50  --prep_def_merge_tr_red                 false
% 8.00/1.50  --prep_def_merge_tr_cl                  false
% 8.00/1.50  --smt_preprocessing                     true
% 8.00/1.50  --smt_ac_axioms                         fast
% 8.00/1.50  --preprocessed_out                      false
% 8.00/1.50  --preprocessed_stats                    false
% 8.00/1.50  
% 8.00/1.50  ------ Abstraction refinement Options
% 8.00/1.50  
% 8.00/1.50  --abstr_ref                             []
% 8.00/1.50  --abstr_ref_prep                        false
% 8.00/1.50  --abstr_ref_until_sat                   false
% 8.00/1.50  --abstr_ref_sig_restrict                funpre
% 8.00/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 8.00/1.50  --abstr_ref_under                       []
% 8.00/1.50  
% 8.00/1.50  ------ SAT Options
% 8.00/1.50  
% 8.00/1.50  --sat_mode                              false
% 8.00/1.50  --sat_fm_restart_options                ""
% 8.00/1.50  --sat_gr_def                            false
% 8.00/1.50  --sat_epr_types                         true
% 8.00/1.50  --sat_non_cyclic_types                  false
% 8.00/1.50  --sat_finite_models                     false
% 8.00/1.50  --sat_fm_lemmas                         false
% 8.00/1.50  --sat_fm_prep                           false
% 8.00/1.50  --sat_fm_uc_incr                        true
% 8.00/1.50  --sat_out_model                         small
% 8.00/1.50  --sat_out_clauses                       false
% 8.00/1.50  
% 8.00/1.50  ------ QBF Options
% 8.00/1.50  
% 8.00/1.50  --qbf_mode                              false
% 8.00/1.50  --qbf_elim_univ                         false
% 8.00/1.50  --qbf_dom_inst                          none
% 8.00/1.50  --qbf_dom_pre_inst                      false
% 8.00/1.50  --qbf_sk_in                             false
% 8.00/1.50  --qbf_pred_elim                         true
% 8.00/1.50  --qbf_split                             512
% 8.00/1.50  
% 8.00/1.50  ------ BMC1 Options
% 8.00/1.50  
% 8.00/1.50  --bmc1_incremental                      false
% 8.00/1.50  --bmc1_axioms                           reachable_all
% 8.00/1.50  --bmc1_min_bound                        0
% 8.00/1.50  --bmc1_max_bound                        -1
% 8.00/1.50  --bmc1_max_bound_default                -1
% 8.00/1.50  --bmc1_symbol_reachability              true
% 8.00/1.50  --bmc1_property_lemmas                  false
% 8.00/1.50  --bmc1_k_induction                      false
% 8.00/1.50  --bmc1_non_equiv_states                 false
% 8.00/1.50  --bmc1_deadlock                         false
% 8.00/1.50  --bmc1_ucm                              false
% 8.00/1.50  --bmc1_add_unsat_core                   none
% 8.00/1.50  --bmc1_unsat_core_children              false
% 8.00/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 8.00/1.50  --bmc1_out_stat                         full
% 8.00/1.50  --bmc1_ground_init                      false
% 8.00/1.50  --bmc1_pre_inst_next_state              false
% 8.00/1.50  --bmc1_pre_inst_state                   false
% 8.00/1.50  --bmc1_pre_inst_reach_state             false
% 8.00/1.50  --bmc1_out_unsat_core                   false
% 8.00/1.50  --bmc1_aig_witness_out                  false
% 8.00/1.50  --bmc1_verbose                          false
% 8.00/1.50  --bmc1_dump_clauses_tptp                false
% 8.00/1.50  --bmc1_dump_unsat_core_tptp             false
% 8.00/1.50  --bmc1_dump_file                        -
% 8.00/1.50  --bmc1_ucm_expand_uc_limit              128
% 8.00/1.50  --bmc1_ucm_n_expand_iterations          6
% 8.00/1.50  --bmc1_ucm_extend_mode                  1
% 8.00/1.50  --bmc1_ucm_init_mode                    2
% 8.00/1.50  --bmc1_ucm_cone_mode                    none
% 8.00/1.50  --bmc1_ucm_reduced_relation_type        0
% 8.00/1.50  --bmc1_ucm_relax_model                  4
% 8.00/1.50  --bmc1_ucm_full_tr_after_sat            true
% 8.00/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 8.00/1.50  --bmc1_ucm_layered_model                none
% 8.00/1.50  --bmc1_ucm_max_lemma_size               10
% 8.00/1.50  
% 8.00/1.50  ------ AIG Options
% 8.00/1.50  
% 8.00/1.50  --aig_mode                              false
% 8.00/1.50  
% 8.00/1.50  ------ Instantiation Options
% 8.00/1.50  
% 8.00/1.50  --instantiation_flag                    true
% 8.00/1.50  --inst_sos_flag                         false
% 8.00/1.50  --inst_sos_phase                        true
% 8.00/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 8.00/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 8.00/1.50  --inst_lit_sel_side                     num_symb
% 8.00/1.50  --inst_solver_per_active                1400
% 8.00/1.50  --inst_solver_calls_frac                1.
% 8.00/1.50  --inst_passive_queue_type               priority_queues
% 8.00/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 8.00/1.50  --inst_passive_queues_freq              [25;2]
% 8.00/1.50  --inst_dismatching                      true
% 8.00/1.50  --inst_eager_unprocessed_to_passive     true
% 8.00/1.50  --inst_prop_sim_given                   true
% 8.00/1.50  --inst_prop_sim_new                     false
% 8.00/1.50  --inst_subs_new                         false
% 8.00/1.50  --inst_eq_res_simp                      false
% 8.00/1.50  --inst_subs_given                       false
% 8.00/1.50  --inst_orphan_elimination               true
% 8.00/1.50  --inst_learning_loop_flag               true
% 8.00/1.50  --inst_learning_start                   3000
% 8.00/1.50  --inst_learning_factor                  2
% 8.00/1.50  --inst_start_prop_sim_after_learn       3
% 8.00/1.50  --inst_sel_renew                        solver
% 8.00/1.50  --inst_lit_activity_flag                true
% 8.00/1.50  --inst_restr_to_given                   false
% 8.00/1.50  --inst_activity_threshold               500
% 8.00/1.50  --inst_out_proof                        true
% 8.00/1.50  
% 8.00/1.50  ------ Resolution Options
% 8.00/1.50  
% 8.00/1.50  --resolution_flag                       true
% 8.00/1.50  --res_lit_sel                           adaptive
% 8.00/1.50  --res_lit_sel_side                      none
% 8.00/1.50  --res_ordering                          kbo
% 8.00/1.50  --res_to_prop_solver                    active
% 8.00/1.50  --res_prop_simpl_new                    false
% 8.00/1.50  --res_prop_simpl_given                  true
% 8.00/1.50  --res_passive_queue_type                priority_queues
% 8.00/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 8.00/1.50  --res_passive_queues_freq               [15;5]
% 8.00/1.50  --res_forward_subs                      full
% 8.00/1.50  --res_backward_subs                     full
% 8.00/1.50  --res_forward_subs_resolution           true
% 8.00/1.50  --res_backward_subs_resolution          true
% 8.00/1.50  --res_orphan_elimination                true
% 8.00/1.50  --res_time_limit                        2.
% 8.00/1.50  --res_out_proof                         true
% 8.00/1.50  
% 8.00/1.50  ------ Superposition Options
% 8.00/1.50  
% 8.00/1.50  --superposition_flag                    true
% 8.00/1.50  --sup_passive_queue_type                priority_queues
% 8.00/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 8.00/1.50  --sup_passive_queues_freq               [8;1;4]
% 8.00/1.50  --demod_completeness_check              fast
% 8.00/1.50  --demod_use_ground                      true
% 8.00/1.50  --sup_to_prop_solver                    passive
% 8.00/1.50  --sup_prop_simpl_new                    true
% 8.00/1.50  --sup_prop_simpl_given                  true
% 8.00/1.50  --sup_fun_splitting                     false
% 8.00/1.50  --sup_smt_interval                      50000
% 8.00/1.50  
% 8.00/1.50  ------ Superposition Simplification Setup
% 8.00/1.50  
% 8.00/1.50  --sup_indices_passive                   []
% 8.00/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.00/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.00/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.00/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 8.00/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.00/1.50  --sup_full_bw                           [BwDemod]
% 8.00/1.50  --sup_immed_triv                        [TrivRules]
% 8.00/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 8.00/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.00/1.50  --sup_immed_bw_main                     []
% 8.00/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 8.00/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 8.00/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.00/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 8.00/1.50  
% 8.00/1.50  ------ Combination Options
% 8.00/1.50  
% 8.00/1.50  --comb_res_mult                         3
% 8.00/1.50  --comb_sup_mult                         2
% 8.00/1.50  --comb_inst_mult                        10
% 8.00/1.50  
% 8.00/1.50  ------ Debug Options
% 8.00/1.50  
% 8.00/1.50  --dbg_backtrace                         false
% 8.00/1.50  --dbg_dump_prop_clauses                 false
% 8.00/1.50  --dbg_dump_prop_clauses_file            -
% 8.00/1.50  --dbg_out_stat                          false
% 8.00/1.50  ------ Parsing...
% 8.00/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 8.00/1.50  
% 8.00/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 8.00/1.50  
% 8.00/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 8.00/1.50  
% 8.00/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.00/1.50  ------ Proving...
% 8.00/1.50  ------ Problem Properties 
% 8.00/1.50  
% 8.00/1.50  
% 8.00/1.50  clauses                                 44
% 8.00/1.50  conjectures                             5
% 8.00/1.50  EPR                                     6
% 8.00/1.50  Horn                                    39
% 8.00/1.50  unary                                   12
% 8.00/1.50  binary                                  6
% 8.00/1.50  lits                                    133
% 8.00/1.50  lits eq                                 31
% 8.00/1.50  fd_pure                                 0
% 8.00/1.50  fd_pseudo                               0
% 8.00/1.50  fd_cond                                 6
% 8.00/1.50  fd_pseudo_cond                          2
% 8.00/1.50  AC symbols                              0
% 8.00/1.50  
% 8.00/1.50  ------ Schedule dynamic 5 is on 
% 8.00/1.50  
% 8.00/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 8.00/1.50  
% 8.00/1.50  
% 8.00/1.50  ------ 
% 8.00/1.50  Current options:
% 8.00/1.50  ------ 
% 8.00/1.50  
% 8.00/1.50  ------ Input Options
% 8.00/1.50  
% 8.00/1.50  --out_options                           all
% 8.00/1.50  --tptp_safe_out                         true
% 8.00/1.50  --problem_path                          ""
% 8.00/1.50  --include_path                          ""
% 8.00/1.50  --clausifier                            res/vclausify_rel
% 8.00/1.50  --clausifier_options                    --mode clausify
% 8.00/1.50  --stdin                                 false
% 8.00/1.50  --stats_out                             all
% 8.00/1.50  
% 8.00/1.50  ------ General Options
% 8.00/1.50  
% 8.00/1.50  --fof                                   false
% 8.00/1.50  --time_out_real                         305.
% 8.00/1.50  --time_out_virtual                      -1.
% 8.00/1.50  --symbol_type_check                     false
% 8.00/1.50  --clausify_out                          false
% 8.00/1.50  --sig_cnt_out                           false
% 8.00/1.50  --trig_cnt_out                          false
% 8.00/1.50  --trig_cnt_out_tolerance                1.
% 8.00/1.50  --trig_cnt_out_sk_spl                   false
% 8.00/1.50  --abstr_cl_out                          false
% 8.00/1.50  
% 8.00/1.50  ------ Global Options
% 8.00/1.50  
% 8.00/1.50  --schedule                              default
% 8.00/1.50  --add_important_lit                     false
% 8.00/1.50  --prop_solver_per_cl                    1000
% 8.00/1.50  --min_unsat_core                        false
% 8.00/1.50  --soft_assumptions                      false
% 8.00/1.50  --soft_lemma_size                       3
% 8.00/1.50  --prop_impl_unit_size                   0
% 8.00/1.50  --prop_impl_unit                        []
% 8.00/1.50  --share_sel_clauses                     true
% 8.00/1.50  --reset_solvers                         false
% 8.00/1.50  --bc_imp_inh                            [conj_cone]
% 8.00/1.50  --conj_cone_tolerance                   3.
% 8.00/1.50  --extra_neg_conj                        none
% 8.00/1.50  --large_theory_mode                     true
% 8.00/1.50  --prolific_symb_bound                   200
% 8.00/1.50  --lt_threshold                          2000
% 8.00/1.50  --clause_weak_htbl                      true
% 8.00/1.50  --gc_record_bc_elim                     false
% 8.00/1.50  
% 8.00/1.50  ------ Preprocessing Options
% 8.00/1.50  
% 8.00/1.50  --preprocessing_flag                    true
% 8.00/1.50  --time_out_prep_mult                    0.1
% 8.00/1.50  --splitting_mode                        input
% 8.00/1.50  --splitting_grd                         true
% 8.00/1.50  --splitting_cvd                         false
% 8.00/1.50  --splitting_cvd_svl                     false
% 8.00/1.50  --splitting_nvd                         32
% 8.00/1.50  --sub_typing                            true
% 8.00/1.50  --prep_gs_sim                           true
% 8.00/1.50  --prep_unflatten                        true
% 8.00/1.50  --prep_res_sim                          true
% 8.00/1.50  --prep_upred                            true
% 8.00/1.50  --prep_sem_filter                       exhaustive
% 8.00/1.50  --prep_sem_filter_out                   false
% 8.00/1.50  --pred_elim                             true
% 8.00/1.50  --res_sim_input                         true
% 8.00/1.50  --eq_ax_congr_red                       true
% 8.00/1.50  --pure_diseq_elim                       true
% 8.00/1.50  --brand_transform                       false
% 8.00/1.50  --non_eq_to_eq                          false
% 8.00/1.50  --prep_def_merge                        true
% 8.00/1.50  --prep_def_merge_prop_impl              false
% 8.00/1.50  --prep_def_merge_mbd                    true
% 8.00/1.50  --prep_def_merge_tr_red                 false
% 8.00/1.50  --prep_def_merge_tr_cl                  false
% 8.00/1.50  --smt_preprocessing                     true
% 8.00/1.50  --smt_ac_axioms                         fast
% 8.00/1.50  --preprocessed_out                      false
% 8.00/1.50  --preprocessed_stats                    false
% 8.00/1.50  
% 8.00/1.50  ------ Abstraction refinement Options
% 8.00/1.50  
% 8.00/1.50  --abstr_ref                             []
% 8.00/1.50  --abstr_ref_prep                        false
% 8.00/1.50  --abstr_ref_until_sat                   false
% 8.00/1.50  --abstr_ref_sig_restrict                funpre
% 8.00/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 8.00/1.50  --abstr_ref_under                       []
% 8.00/1.50  
% 8.00/1.50  ------ SAT Options
% 8.00/1.50  
% 8.00/1.50  --sat_mode                              false
% 8.00/1.50  --sat_fm_restart_options                ""
% 8.00/1.50  --sat_gr_def                            false
% 8.00/1.50  --sat_epr_types                         true
% 8.00/1.50  --sat_non_cyclic_types                  false
% 8.00/1.50  --sat_finite_models                     false
% 8.00/1.50  --sat_fm_lemmas                         false
% 8.00/1.50  --sat_fm_prep                           false
% 8.00/1.50  --sat_fm_uc_incr                        true
% 8.00/1.50  --sat_out_model                         small
% 8.00/1.50  --sat_out_clauses                       false
% 8.00/1.50  
% 8.00/1.50  ------ QBF Options
% 8.00/1.50  
% 8.00/1.50  --qbf_mode                              false
% 8.00/1.50  --qbf_elim_univ                         false
% 8.00/1.50  --qbf_dom_inst                          none
% 8.00/1.50  --qbf_dom_pre_inst                      false
% 8.00/1.50  --qbf_sk_in                             false
% 8.00/1.50  --qbf_pred_elim                         true
% 8.00/1.50  --qbf_split                             512
% 8.00/1.50  
% 8.00/1.50  ------ BMC1 Options
% 8.00/1.50  
% 8.00/1.50  --bmc1_incremental                      false
% 8.00/1.50  --bmc1_axioms                           reachable_all
% 8.00/1.50  --bmc1_min_bound                        0
% 8.00/1.50  --bmc1_max_bound                        -1
% 8.00/1.50  --bmc1_max_bound_default                -1
% 8.00/1.50  --bmc1_symbol_reachability              true
% 8.00/1.50  --bmc1_property_lemmas                  false
% 8.00/1.50  --bmc1_k_induction                      false
% 8.00/1.50  --bmc1_non_equiv_states                 false
% 8.00/1.50  --bmc1_deadlock                         false
% 8.00/1.50  --bmc1_ucm                              false
% 8.00/1.50  --bmc1_add_unsat_core                   none
% 8.00/1.50  --bmc1_unsat_core_children              false
% 8.00/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 8.00/1.50  --bmc1_out_stat                         full
% 8.00/1.50  --bmc1_ground_init                      false
% 8.00/1.50  --bmc1_pre_inst_next_state              false
% 8.00/1.50  --bmc1_pre_inst_state                   false
% 8.00/1.50  --bmc1_pre_inst_reach_state             false
% 8.00/1.50  --bmc1_out_unsat_core                   false
% 8.00/1.50  --bmc1_aig_witness_out                  false
% 8.00/1.50  --bmc1_verbose                          false
% 8.00/1.50  --bmc1_dump_clauses_tptp                false
% 8.00/1.50  --bmc1_dump_unsat_core_tptp             false
% 8.00/1.50  --bmc1_dump_file                        -
% 8.00/1.50  --bmc1_ucm_expand_uc_limit              128
% 8.00/1.50  --bmc1_ucm_n_expand_iterations          6
% 8.00/1.50  --bmc1_ucm_extend_mode                  1
% 8.00/1.50  --bmc1_ucm_init_mode                    2
% 8.00/1.50  --bmc1_ucm_cone_mode                    none
% 8.00/1.50  --bmc1_ucm_reduced_relation_type        0
% 8.00/1.50  --bmc1_ucm_relax_model                  4
% 8.00/1.50  --bmc1_ucm_full_tr_after_sat            true
% 8.00/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 8.00/1.50  --bmc1_ucm_layered_model                none
% 8.00/1.50  --bmc1_ucm_max_lemma_size               10
% 8.00/1.50  
% 8.00/1.50  ------ AIG Options
% 8.00/1.50  
% 8.00/1.50  --aig_mode                              false
% 8.00/1.50  
% 8.00/1.50  ------ Instantiation Options
% 8.00/1.50  
% 8.00/1.50  --instantiation_flag                    true
% 8.00/1.50  --inst_sos_flag                         false
% 8.00/1.50  --inst_sos_phase                        true
% 8.00/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 8.00/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 8.00/1.50  --inst_lit_sel_side                     none
% 8.00/1.50  --inst_solver_per_active                1400
% 8.00/1.50  --inst_solver_calls_frac                1.
% 8.00/1.50  --inst_passive_queue_type               priority_queues
% 8.00/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 8.00/1.50  --inst_passive_queues_freq              [25;2]
% 8.00/1.50  --inst_dismatching                      true
% 8.00/1.50  --inst_eager_unprocessed_to_passive     true
% 8.00/1.50  --inst_prop_sim_given                   true
% 8.00/1.50  --inst_prop_sim_new                     false
% 8.00/1.50  --inst_subs_new                         false
% 8.00/1.50  --inst_eq_res_simp                      false
% 8.00/1.50  --inst_subs_given                       false
% 8.00/1.50  --inst_orphan_elimination               true
% 8.00/1.50  --inst_learning_loop_flag               true
% 8.00/1.50  --inst_learning_start                   3000
% 8.00/1.50  --inst_learning_factor                  2
% 8.00/1.50  --inst_start_prop_sim_after_learn       3
% 8.00/1.50  --inst_sel_renew                        solver
% 8.00/1.50  --inst_lit_activity_flag                true
% 8.00/1.50  --inst_restr_to_given                   false
% 8.00/1.50  --inst_activity_threshold               500
% 8.00/1.50  --inst_out_proof                        true
% 8.00/1.50  
% 8.00/1.50  ------ Resolution Options
% 8.00/1.50  
% 8.00/1.50  --resolution_flag                       false
% 8.00/1.50  --res_lit_sel                           adaptive
% 8.00/1.50  --res_lit_sel_side                      none
% 8.00/1.50  --res_ordering                          kbo
% 8.00/1.50  --res_to_prop_solver                    active
% 8.00/1.50  --res_prop_simpl_new                    false
% 8.00/1.50  --res_prop_simpl_given                  true
% 8.00/1.50  --res_passive_queue_type                priority_queues
% 8.00/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 8.00/1.50  --res_passive_queues_freq               [15;5]
% 8.00/1.50  --res_forward_subs                      full
% 8.00/1.50  --res_backward_subs                     full
% 8.00/1.50  --res_forward_subs_resolution           true
% 8.00/1.50  --res_backward_subs_resolution          true
% 8.00/1.50  --res_orphan_elimination                true
% 8.00/1.50  --res_time_limit                        2.
% 8.00/1.50  --res_out_proof                         true
% 8.00/1.50  
% 8.00/1.50  ------ Superposition Options
% 8.00/1.50  
% 8.00/1.50  --superposition_flag                    true
% 8.00/1.50  --sup_passive_queue_type                priority_queues
% 8.00/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 8.00/1.50  --sup_passive_queues_freq               [8;1;4]
% 8.00/1.50  --demod_completeness_check              fast
% 8.00/1.50  --demod_use_ground                      true
% 8.00/1.50  --sup_to_prop_solver                    passive
% 8.00/1.50  --sup_prop_simpl_new                    true
% 8.00/1.50  --sup_prop_simpl_given                  true
% 8.00/1.50  --sup_fun_splitting                     false
% 8.00/1.50  --sup_smt_interval                      50000
% 8.00/1.50  
% 8.00/1.50  ------ Superposition Simplification Setup
% 8.00/1.50  
% 8.00/1.50  --sup_indices_passive                   []
% 8.00/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.00/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.00/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.00/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 8.00/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.00/1.50  --sup_full_bw                           [BwDemod]
% 8.00/1.50  --sup_immed_triv                        [TrivRules]
% 8.00/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 8.00/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.00/1.50  --sup_immed_bw_main                     []
% 8.00/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 8.00/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 8.00/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.00/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 8.00/1.50  
% 8.00/1.50  ------ Combination Options
% 8.00/1.50  
% 8.00/1.50  --comb_res_mult                         3
% 8.00/1.50  --comb_sup_mult                         2
% 8.00/1.50  --comb_inst_mult                        10
% 8.00/1.50  
% 8.00/1.50  ------ Debug Options
% 8.00/1.50  
% 8.00/1.50  --dbg_backtrace                         false
% 8.00/1.50  --dbg_dump_prop_clauses                 false
% 8.00/1.50  --dbg_dump_prop_clauses_file            -
% 8.00/1.50  --dbg_out_stat                          false
% 8.00/1.50  
% 8.00/1.50  
% 8.00/1.50  
% 8.00/1.50  
% 8.00/1.50  ------ Proving...
% 8.00/1.50  
% 8.00/1.50  
% 8.00/1.50  % SZS status Theorem for theBenchmark.p
% 8.00/1.50  
% 8.00/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 8.00/1.50  
% 8.00/1.50  fof(f25,conjecture,(
% 8.00/1.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 8.00/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.00/1.50  
% 8.00/1.50  fof(f26,negated_conjecture,(
% 8.00/1.50    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 8.00/1.50    inference(negated_conjecture,[],[f25])).
% 8.00/1.50  
% 8.00/1.50  fof(f56,plain,(
% 8.00/1.50    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 8.00/1.50    inference(ennf_transformation,[],[f26])).
% 8.00/1.50  
% 8.00/1.50  fof(f57,plain,(
% 8.00/1.50    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 8.00/1.50    inference(flattening,[],[f56])).
% 8.00/1.50  
% 8.00/1.50  fof(f65,plain,(
% 8.00/1.50    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 8.00/1.50    introduced(choice_axiom,[])).
% 8.00/1.50  
% 8.00/1.50  fof(f66,plain,(
% 8.00/1.50    (~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 8.00/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f57,f65])).
% 8.00/1.50  
% 8.00/1.50  fof(f116,plain,(
% 8.00/1.50    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 8.00/1.50    inference(cnf_transformation,[],[f66])).
% 8.00/1.50  
% 8.00/1.50  fof(f16,axiom,(
% 8.00/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 8.00/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.00/1.50  
% 8.00/1.50  fof(f42,plain,(
% 8.00/1.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.00/1.50    inference(ennf_transformation,[],[f16])).
% 8.00/1.50  
% 8.00/1.50  fof(f43,plain,(
% 8.00/1.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.00/1.50    inference(flattening,[],[f42])).
% 8.00/1.50  
% 8.00/1.50  fof(f63,plain,(
% 8.00/1.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.00/1.50    inference(nnf_transformation,[],[f43])).
% 8.00/1.50  
% 8.00/1.50  fof(f91,plain,(
% 8.00/1.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 8.00/1.50    inference(cnf_transformation,[],[f63])).
% 8.00/1.50  
% 8.00/1.50  fof(f12,axiom,(
% 8.00/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 8.00/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.00/1.50  
% 8.00/1.50  fof(f36,plain,(
% 8.00/1.50    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.00/1.50    inference(ennf_transformation,[],[f12])).
% 8.00/1.50  
% 8.00/1.50  fof(f85,plain,(
% 8.00/1.50    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 8.00/1.50    inference(cnf_transformation,[],[f36])).
% 8.00/1.50  
% 8.00/1.50  fof(f114,plain,(
% 8.00/1.50    v1_funct_2(sK1,sK0,sK0)),
% 8.00/1.50    inference(cnf_transformation,[],[f66])).
% 8.00/1.50  
% 8.00/1.50  fof(f13,axiom,(
% 8.00/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 8.00/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.00/1.50  
% 8.00/1.50  fof(f37,plain,(
% 8.00/1.50    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.00/1.50    inference(ennf_transformation,[],[f13])).
% 8.00/1.50  
% 8.00/1.50  fof(f86,plain,(
% 8.00/1.50    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 8.00/1.50    inference(cnf_transformation,[],[f37])).
% 8.00/1.50  
% 8.00/1.50  fof(f15,axiom,(
% 8.00/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 8.00/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.00/1.50  
% 8.00/1.50  fof(f40,plain,(
% 8.00/1.50    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.00/1.50    inference(ennf_transformation,[],[f15])).
% 8.00/1.50  
% 8.00/1.50  fof(f41,plain,(
% 8.00/1.50    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.00/1.50    inference(flattening,[],[f40])).
% 8.00/1.50  
% 8.00/1.50  fof(f90,plain,(
% 8.00/1.50    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 8.00/1.50    inference(cnf_transformation,[],[f41])).
% 8.00/1.50  
% 8.00/1.50  fof(f11,axiom,(
% 8.00/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 8.00/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.00/1.50  
% 8.00/1.50  fof(f28,plain,(
% 8.00/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 8.00/1.50    inference(pure_predicate_removal,[],[f11])).
% 8.00/1.50  
% 8.00/1.50  fof(f35,plain,(
% 8.00/1.50    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.00/1.50    inference(ennf_transformation,[],[f28])).
% 8.00/1.50  
% 8.00/1.50  fof(f84,plain,(
% 8.00/1.50    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 8.00/1.50    inference(cnf_transformation,[],[f35])).
% 8.00/1.50  
% 8.00/1.50  fof(f17,axiom,(
% 8.00/1.50    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 8.00/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.00/1.50  
% 8.00/1.50  fof(f44,plain,(
% 8.00/1.50    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 8.00/1.50    inference(ennf_transformation,[],[f17])).
% 8.00/1.50  
% 8.00/1.50  fof(f45,plain,(
% 8.00/1.50    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 8.00/1.50    inference(flattening,[],[f44])).
% 8.00/1.50  
% 8.00/1.50  fof(f64,plain,(
% 8.00/1.50    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 8.00/1.50    inference(nnf_transformation,[],[f45])).
% 8.00/1.50  
% 8.00/1.50  fof(f97,plain,(
% 8.00/1.50    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 8.00/1.50    inference(cnf_transformation,[],[f64])).
% 8.00/1.50  
% 8.00/1.50  fof(f10,axiom,(
% 8.00/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 8.00/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.00/1.50  
% 8.00/1.50  fof(f34,plain,(
% 8.00/1.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.00/1.50    inference(ennf_transformation,[],[f10])).
% 8.00/1.50  
% 8.00/1.50  fof(f83,plain,(
% 8.00/1.50    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 8.00/1.50    inference(cnf_transformation,[],[f34])).
% 8.00/1.50  
% 8.00/1.50  fof(f113,plain,(
% 8.00/1.50    v1_funct_1(sK1)),
% 8.00/1.50    inference(cnf_transformation,[],[f66])).
% 8.00/1.50  
% 8.00/1.50  fof(f115,plain,(
% 8.00/1.50    v3_funct_2(sK1,sK0,sK0)),
% 8.00/1.50    inference(cnf_transformation,[],[f66])).
% 8.00/1.50  
% 8.00/1.50  fof(f23,axiom,(
% 8.00/1.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 8.00/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.00/1.50  
% 8.00/1.50  fof(f52,plain,(
% 8.00/1.50    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 8.00/1.50    inference(ennf_transformation,[],[f23])).
% 8.00/1.50  
% 8.00/1.50  fof(f53,plain,(
% 8.00/1.50    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 8.00/1.50    inference(flattening,[],[f52])).
% 8.00/1.50  
% 8.00/1.50  fof(f109,plain,(
% 8.00/1.50    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 8.00/1.50    inference(cnf_transformation,[],[f53])).
% 8.00/1.50  
% 8.00/1.50  fof(f89,plain,(
% 8.00/1.50    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 8.00/1.50    inference(cnf_transformation,[],[f41])).
% 8.00/1.50  
% 8.00/1.50  fof(f20,axiom,(
% 8.00/1.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 8.00/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.00/1.50  
% 8.00/1.50  fof(f48,plain,(
% 8.00/1.50    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 8.00/1.50    inference(ennf_transformation,[],[f20])).
% 8.00/1.50  
% 8.00/1.50  fof(f49,plain,(
% 8.00/1.50    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 8.00/1.50    inference(flattening,[],[f48])).
% 8.00/1.50  
% 8.00/1.50  fof(f104,plain,(
% 8.00/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 8.00/1.50    inference(cnf_transformation,[],[f49])).
% 8.00/1.50  
% 8.00/1.50  fof(f107,plain,(
% 8.00/1.50    ( ! [X2,X0,X1] : (v1_funct_1(k2_funct_1(X2)) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 8.00/1.50    inference(cnf_transformation,[],[f53])).
% 8.00/1.50  
% 8.00/1.50  fof(f9,axiom,(
% 8.00/1.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))))),
% 8.00/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.00/1.50  
% 8.00/1.50  fof(f32,plain,(
% 8.00/1.50    ! [X0] : (((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 8.00/1.50    inference(ennf_transformation,[],[f9])).
% 8.00/1.50  
% 8.00/1.50  fof(f33,plain,(
% 8.00/1.50    ! [X0] : ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 8.00/1.50    inference(flattening,[],[f32])).
% 8.00/1.50  
% 8.00/1.50  fof(f81,plain,(
% 8.00/1.50    ( ! [X0] : (k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 8.00/1.50    inference(cnf_transformation,[],[f33])).
% 8.00/1.50  
% 8.00/1.50  fof(f22,axiom,(
% 8.00/1.50    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 8.00/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.00/1.50  
% 8.00/1.50  fof(f106,plain,(
% 8.00/1.50    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 8.00/1.50    inference(cnf_transformation,[],[f22])).
% 8.00/1.50  
% 8.00/1.50  fof(f121,plain,(
% 8.00/1.50    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 8.00/1.50    inference(definition_unfolding,[],[f81,f106])).
% 8.00/1.50  
% 8.00/1.50  fof(f18,axiom,(
% 8.00/1.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 8.00/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.00/1.50  
% 8.00/1.50  fof(f46,plain,(
% 8.00/1.50    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 8.00/1.50    inference(ennf_transformation,[],[f18])).
% 8.00/1.50  
% 8.00/1.50  fof(f47,plain,(
% 8.00/1.50    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 8.00/1.50    inference(flattening,[],[f46])).
% 8.00/1.50  
% 8.00/1.50  fof(f102,plain,(
% 8.00/1.50    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 8.00/1.50    inference(cnf_transformation,[],[f47])).
% 8.00/1.50  
% 8.00/1.50  fof(f99,plain,(
% 8.00/1.50    ( ! [X0,X1] : (v1_funct_1(k2_funct_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 8.00/1.50    inference(cnf_transformation,[],[f47])).
% 8.00/1.50  
% 8.00/1.50  fof(f82,plain,(
% 8.00/1.50    ( ! [X0] : (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 8.00/1.50    inference(cnf_transformation,[],[f33])).
% 8.00/1.50  
% 8.00/1.50  fof(f120,plain,(
% 8.00/1.50    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 8.00/1.50    inference(definition_unfolding,[],[f82,f106])).
% 8.00/1.50  
% 8.00/1.50  fof(f21,axiom,(
% 8.00/1.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 8.00/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.00/1.50  
% 8.00/1.50  fof(f50,plain,(
% 8.00/1.50    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 8.00/1.50    inference(ennf_transformation,[],[f21])).
% 8.00/1.50  
% 8.00/1.50  fof(f51,plain,(
% 8.00/1.50    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 8.00/1.50    inference(flattening,[],[f50])).
% 8.00/1.50  
% 8.00/1.50  fof(f105,plain,(
% 8.00/1.50    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 8.00/1.50    inference(cnf_transformation,[],[f51])).
% 8.00/1.50  
% 8.00/1.50  fof(f117,plain,(
% 8.00/1.50    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))),
% 8.00/1.50    inference(cnf_transformation,[],[f66])).
% 8.00/1.50  
% 8.00/1.50  fof(f19,axiom,(
% 8.00/1.50    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 8.00/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.00/1.50  
% 8.00/1.50  fof(f27,plain,(
% 8.00/1.50    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 8.00/1.50    inference(pure_predicate_removal,[],[f19])).
% 8.00/1.50  
% 8.00/1.50  fof(f103,plain,(
% 8.00/1.50    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 8.00/1.50    inference(cnf_transformation,[],[f27])).
% 8.00/1.50  
% 8.00/1.50  fof(f14,axiom,(
% 8.00/1.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 8.00/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.00/1.50  
% 8.00/1.50  fof(f38,plain,(
% 8.00/1.50    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 8.00/1.50    inference(ennf_transformation,[],[f14])).
% 8.00/1.50  
% 8.00/1.50  fof(f39,plain,(
% 8.00/1.50    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 8.00/1.50    inference(flattening,[],[f38])).
% 8.00/1.50  
% 8.00/1.50  fof(f87,plain,(
% 8.00/1.50    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 8.00/1.50    inference(cnf_transformation,[],[f39])).
% 8.00/1.50  
% 8.00/1.50  fof(f7,axiom,(
% 8.00/1.50    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 8.00/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.00/1.50  
% 8.00/1.50  fof(f30,plain,(
% 8.00/1.50    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 8.00/1.50    inference(ennf_transformation,[],[f7])).
% 8.00/1.50  
% 8.00/1.50  fof(f31,plain,(
% 8.00/1.50    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 8.00/1.50    inference(flattening,[],[f30])).
% 8.00/1.50  
% 8.00/1.50  fof(f78,plain,(
% 8.00/1.50    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 8.00/1.50    inference(cnf_transformation,[],[f31])).
% 8.00/1.50  
% 8.00/1.50  fof(f8,axiom,(
% 8.00/1.50    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 8.00/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.00/1.50  
% 8.00/1.50  fof(f79,plain,(
% 8.00/1.50    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 8.00/1.50    inference(cnf_transformation,[],[f8])).
% 8.00/1.50  
% 8.00/1.50  fof(f119,plain,(
% 8.00/1.50    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 8.00/1.50    inference(definition_unfolding,[],[f79,f106])).
% 8.00/1.50  
% 8.00/1.50  fof(f77,plain,(
% 8.00/1.50    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 8.00/1.50    inference(cnf_transformation,[],[f31])).
% 8.00/1.50  
% 8.00/1.50  fof(f4,axiom,(
% 8.00/1.50    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 8.00/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.00/1.50  
% 8.00/1.50  fof(f74,plain,(
% 8.00/1.50    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 8.00/1.50    inference(cnf_transformation,[],[f4])).
% 8.00/1.50  
% 8.00/1.50  cnf(c_46,negated_conjecture,
% 8.00/1.50      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 8.00/1.50      inference(cnf_transformation,[],[f116]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_2415,plain,
% 8.00/1.50      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 8.00/1.50      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_29,plain,
% 8.00/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 8.00/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.00/1.50      | k1_relset_1(X1,X2,X0) = X1
% 8.00/1.50      | k1_xboole_0 = X2 ),
% 8.00/1.50      inference(cnf_transformation,[],[f91]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_2429,plain,
% 8.00/1.50      ( k1_relset_1(X0,X1,X2) = X0
% 8.00/1.50      | k1_xboole_0 = X1
% 8.00/1.50      | v1_funct_2(X2,X0,X1) != iProver_top
% 8.00/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 8.00/1.50      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_8603,plain,
% 8.00/1.50      ( k1_relset_1(sK0,sK0,sK1) = sK0
% 8.00/1.50      | sK0 = k1_xboole_0
% 8.00/1.50      | v1_funct_2(sK1,sK0,sK0) != iProver_top ),
% 8.00/1.50      inference(superposition,[status(thm)],[c_2415,c_2429]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_18,plain,
% 8.00/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.00/1.50      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 8.00/1.50      inference(cnf_transformation,[],[f85]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_2438,plain,
% 8.00/1.50      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 8.00/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 8.00/1.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_5338,plain,
% 8.00/1.50      ( k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
% 8.00/1.50      inference(superposition,[status(thm)],[c_2415,c_2438]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_8613,plain,
% 8.00/1.50      ( k1_relat_1(sK1) = sK0
% 8.00/1.50      | sK0 = k1_xboole_0
% 8.00/1.50      | v1_funct_2(sK1,sK0,sK0) != iProver_top ),
% 8.00/1.50      inference(demodulation,[status(thm)],[c_8603,c_5338]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_48,negated_conjecture,
% 8.00/1.50      ( v1_funct_2(sK1,sK0,sK0) ),
% 8.00/1.50      inference(cnf_transformation,[],[f114]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_51,plain,
% 8.00/1.50      ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
% 8.00/1.50      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_8878,plain,
% 8.00/1.50      ( sK0 = k1_xboole_0 | k1_relat_1(sK1) = sK0 ),
% 8.00/1.50      inference(global_propositional_subsumption,
% 8.00/1.50                [status(thm)],
% 8.00/1.50                [c_8613,c_51]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_8879,plain,
% 8.00/1.50      ( k1_relat_1(sK1) = sK0 | sK0 = k1_xboole_0 ),
% 8.00/1.50      inference(renaming,[status(thm)],[c_8878]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_19,plain,
% 8.00/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.00/1.50      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 8.00/1.50      inference(cnf_transformation,[],[f86]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_2437,plain,
% 8.00/1.50      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 8.00/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 8.00/1.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_4484,plain,
% 8.00/1.50      ( k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
% 8.00/1.50      inference(superposition,[status(thm)],[c_2415,c_2437]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_21,plain,
% 8.00/1.50      ( ~ v3_funct_2(X0,X1,X2)
% 8.00/1.50      | v2_funct_2(X0,X2)
% 8.00/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.00/1.50      | ~ v1_funct_1(X0) ),
% 8.00/1.50      inference(cnf_transformation,[],[f90]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_17,plain,
% 8.00/1.50      ( v5_relat_1(X0,X1)
% 8.00/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 8.00/1.50      inference(cnf_transformation,[],[f84]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_31,plain,
% 8.00/1.50      ( ~ v2_funct_2(X0,X1)
% 8.00/1.50      | ~ v5_relat_1(X0,X1)
% 8.00/1.50      | ~ v1_relat_1(X0)
% 8.00/1.50      | k2_relat_1(X0) = X1 ),
% 8.00/1.50      inference(cnf_transformation,[],[f97]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_584,plain,
% 8.00/1.50      ( ~ v2_funct_2(X0,X1)
% 8.00/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 8.00/1.50      | ~ v1_relat_1(X0)
% 8.00/1.50      | k2_relat_1(X0) = X1 ),
% 8.00/1.50      inference(resolution,[status(thm)],[c_17,c_31]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_16,plain,
% 8.00/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.00/1.50      | v1_relat_1(X0) ),
% 8.00/1.50      inference(cnf_transformation,[],[f83]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_596,plain,
% 8.00/1.50      ( ~ v2_funct_2(X0,X1)
% 8.00/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 8.00/1.50      | k2_relat_1(X0) = X1 ),
% 8.00/1.50      inference(forward_subsumption_resolution,
% 8.00/1.50                [status(thm)],
% 8.00/1.50                [c_584,c_16]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_627,plain,
% 8.00/1.50      ( ~ v3_funct_2(X0,X1,X2)
% 8.00/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.00/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 8.00/1.50      | ~ v1_funct_1(X0)
% 8.00/1.50      | X3 != X0
% 8.00/1.50      | X5 != X2
% 8.00/1.50      | k2_relat_1(X3) = X5 ),
% 8.00/1.50      inference(resolution_lifted,[status(thm)],[c_21,c_596]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_628,plain,
% 8.00/1.50      ( ~ v3_funct_2(X0,X1,X2)
% 8.00/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.00/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 8.00/1.50      | ~ v1_funct_1(X0)
% 8.00/1.50      | k2_relat_1(X0) = X2 ),
% 8.00/1.50      inference(unflattening,[status(thm)],[c_627]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_2411,plain,
% 8.00/1.50      ( k2_relat_1(X0) = X1
% 8.00/1.50      | v3_funct_2(X0,X2,X1) != iProver_top
% 8.00/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 8.00/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
% 8.00/1.50      | v1_funct_1(X0) != iProver_top ),
% 8.00/1.50      inference(predicate_to_equality,[status(thm)],[c_628]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_3548,plain,
% 8.00/1.50      ( k2_relat_1(sK1) = sK0
% 8.00/1.50      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 8.00/1.50      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 8.00/1.50      | v1_funct_1(sK1) != iProver_top ),
% 8.00/1.50      inference(superposition,[status(thm)],[c_2415,c_2411]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_49,negated_conjecture,
% 8.00/1.50      ( v1_funct_1(sK1) ),
% 8.00/1.50      inference(cnf_transformation,[],[f113]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_47,negated_conjecture,
% 8.00/1.50      ( v3_funct_2(sK1,sK0,sK0) ),
% 8.00/1.50      inference(cnf_transformation,[],[f115]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_2924,plain,
% 8.00/1.50      ( ~ v3_funct_2(sK1,X0,X1)
% 8.00/1.50      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 8.00/1.50      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 8.00/1.50      | ~ v1_funct_1(sK1)
% 8.00/1.50      | k2_relat_1(sK1) = X1 ),
% 8.00/1.50      inference(instantiation,[status(thm)],[c_628]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_3110,plain,
% 8.00/1.50      ( ~ v3_funct_2(sK1,sK0,sK0)
% 8.00/1.50      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
% 8.00/1.50      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 8.00/1.50      | ~ v1_funct_1(sK1)
% 8.00/1.50      | k2_relat_1(sK1) = sK0 ),
% 8.00/1.50      inference(instantiation,[status(thm)],[c_2924]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_3261,plain,
% 8.00/1.50      ( ~ v3_funct_2(sK1,sK0,sK0)
% 8.00/1.50      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 8.00/1.50      | ~ v1_funct_1(sK1)
% 8.00/1.50      | k2_relat_1(sK1) = sK0 ),
% 8.00/1.50      inference(instantiation,[status(thm)],[c_3110]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_3873,plain,
% 8.00/1.50      ( k2_relat_1(sK1) = sK0 ),
% 8.00/1.50      inference(global_propositional_subsumption,
% 8.00/1.50                [status(thm)],
% 8.00/1.50                [c_3548,c_49,c_47,c_46,c_3261]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_4496,plain,
% 8.00/1.50      ( k2_relset_1(sK0,sK0,sK1) = sK0 ),
% 8.00/1.50      inference(light_normalisation,[status(thm)],[c_4484,c_3873]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_39,plain,
% 8.00/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 8.00/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.00/1.50      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 8.00/1.50      | ~ v1_funct_1(X0)
% 8.00/1.50      | ~ v2_funct_1(X0)
% 8.00/1.50      | k2_relset_1(X1,X2,X0) != X2 ),
% 8.00/1.50      inference(cnf_transformation,[],[f109]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_2421,plain,
% 8.00/1.50      ( k2_relset_1(X0,X1,X2) != X1
% 8.00/1.50      | v1_funct_2(X2,X0,X1) != iProver_top
% 8.00/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 8.00/1.50      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
% 8.00/1.50      | v1_funct_1(X2) != iProver_top
% 8.00/1.50      | v2_funct_1(X2) != iProver_top ),
% 8.00/1.50      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_7938,plain,
% 8.00/1.50      ( v1_funct_2(sK1,sK0,sK0) != iProver_top
% 8.00/1.50      | m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 8.00/1.50      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 8.00/1.50      | v1_funct_1(sK1) != iProver_top
% 8.00/1.50      | v2_funct_1(sK1) != iProver_top ),
% 8.00/1.50      inference(superposition,[status(thm)],[c_4496,c_2421]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_50,plain,
% 8.00/1.50      ( v1_funct_1(sK1) = iProver_top ),
% 8.00/1.50      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_52,plain,
% 8.00/1.50      ( v3_funct_2(sK1,sK0,sK0) = iProver_top ),
% 8.00/1.50      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_53,plain,
% 8.00/1.50      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 8.00/1.50      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_22,plain,
% 8.00/1.50      ( ~ v3_funct_2(X0,X1,X2)
% 8.00/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.00/1.50      | ~ v1_funct_1(X0)
% 8.00/1.50      | v2_funct_1(X0) ),
% 8.00/1.50      inference(cnf_transformation,[],[f89]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_2891,plain,
% 8.00/1.50      ( ~ v3_funct_2(sK1,X0,X1)
% 8.00/1.50      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 8.00/1.50      | ~ v1_funct_1(sK1)
% 8.00/1.50      | v2_funct_1(sK1) ),
% 8.00/1.50      inference(instantiation,[status(thm)],[c_22]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_3048,plain,
% 8.00/1.50      ( ~ v3_funct_2(sK1,sK0,sK0)
% 8.00/1.50      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 8.00/1.50      | ~ v1_funct_1(sK1)
% 8.00/1.50      | v2_funct_1(sK1) ),
% 8.00/1.50      inference(instantiation,[status(thm)],[c_2891]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_3049,plain,
% 8.00/1.50      ( v3_funct_2(sK1,sK0,sK0) != iProver_top
% 8.00/1.50      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 8.00/1.50      | v1_funct_1(sK1) != iProver_top
% 8.00/1.50      | v2_funct_1(sK1) = iProver_top ),
% 8.00/1.50      inference(predicate_to_equality,[status(thm)],[c_3048]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_2966,plain,
% 8.00/1.50      ( ~ v1_funct_2(sK1,X0,X1)
% 8.00/1.50      | m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 8.00/1.50      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 8.00/1.50      | ~ v1_funct_1(sK1)
% 8.00/1.50      | ~ v2_funct_1(sK1)
% 8.00/1.50      | k2_relset_1(X0,X1,sK1) != X1 ),
% 8.00/1.50      inference(instantiation,[status(thm)],[c_39]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_3271,plain,
% 8.00/1.50      ( ~ v1_funct_2(sK1,sK0,sK0)
% 8.00/1.50      | m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 8.00/1.50      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 8.00/1.50      | ~ v1_funct_1(sK1)
% 8.00/1.50      | ~ v2_funct_1(sK1)
% 8.00/1.50      | k2_relset_1(sK0,sK0,sK1) != sK0 ),
% 8.00/1.50      inference(instantiation,[status(thm)],[c_2966]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_3272,plain,
% 8.00/1.50      ( k2_relset_1(sK0,sK0,sK1) != sK0
% 8.00/1.50      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 8.00/1.50      | m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 8.00/1.50      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 8.00/1.50      | v1_funct_1(sK1) != iProver_top
% 8.00/1.50      | v2_funct_1(sK1) != iProver_top ),
% 8.00/1.50      inference(predicate_to_equality,[status(thm)],[c_3271]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_11631,plain,
% 8.00/1.50      ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 8.00/1.50      inference(global_propositional_subsumption,
% 8.00/1.50                [status(thm)],
% 8.00/1.50                [c_7938,c_50,c_51,c_52,c_53,c_3049,c_3272,c_4496]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_37,plain,
% 8.00/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.00/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 8.00/1.50      | ~ v1_funct_1(X0)
% 8.00/1.50      | ~ v1_funct_1(X3)
% 8.00/1.50      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 8.00/1.50      inference(cnf_transformation,[],[f104]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_2423,plain,
% 8.00/1.50      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 8.00/1.50      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 8.00/1.50      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 8.00/1.50      | v1_funct_1(X5) != iProver_top
% 8.00/1.50      | v1_funct_1(X4) != iProver_top ),
% 8.00/1.50      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_17873,plain,
% 8.00/1.50      ( k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1))
% 8.00/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 8.00/1.50      | v1_funct_1(X2) != iProver_top
% 8.00/1.50      | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
% 8.00/1.50      inference(superposition,[status(thm)],[c_11631,c_2423]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_41,plain,
% 8.00/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 8.00/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 8.00/1.50      | ~ v1_funct_1(X0)
% 8.00/1.50      | v1_funct_1(k2_funct_1(X0))
% 8.00/1.50      | ~ v2_funct_1(X0)
% 8.00/1.50      | k2_relset_1(X1,X2,X0) != X2 ),
% 8.00/1.50      inference(cnf_transformation,[],[f107]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_2946,plain,
% 8.00/1.50      ( ~ v1_funct_2(sK1,X0,X1)
% 8.00/1.50      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 8.00/1.50      | v1_funct_1(k2_funct_1(sK1))
% 8.00/1.50      | ~ v1_funct_1(sK1)
% 8.00/1.50      | ~ v2_funct_1(sK1)
% 8.00/1.50      | k2_relset_1(X0,X1,sK1) != X1 ),
% 8.00/1.50      inference(instantiation,[status(thm)],[c_41]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_3268,plain,
% 8.00/1.50      ( ~ v1_funct_2(sK1,sK0,sK0)
% 8.00/1.50      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 8.00/1.50      | v1_funct_1(k2_funct_1(sK1))
% 8.00/1.50      | ~ v1_funct_1(sK1)
% 8.00/1.50      | ~ v2_funct_1(sK1)
% 8.00/1.50      | k2_relset_1(sK0,sK0,sK1) != sK0 ),
% 8.00/1.50      inference(instantiation,[status(thm)],[c_2946]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_3269,plain,
% 8.00/1.50      ( k2_relset_1(sK0,sK0,sK1) != sK0
% 8.00/1.50      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 8.00/1.50      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 8.00/1.50      | v1_funct_1(k2_funct_1(sK1)) = iProver_top
% 8.00/1.50      | v1_funct_1(sK1) != iProver_top
% 8.00/1.50      | v2_funct_1(sK1) != iProver_top ),
% 8.00/1.50      inference(predicate_to_equality,[status(thm)],[c_3268]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_34900,plain,
% 8.00/1.50      ( v1_funct_1(X2) != iProver_top
% 8.00/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 8.00/1.50      | k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1)) ),
% 8.00/1.50      inference(global_propositional_subsumption,
% 8.00/1.50                [status(thm)],
% 8.00/1.50                [c_17873,c_50,c_51,c_52,c_53,c_3049,c_3269,c_4496]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_34901,plain,
% 8.00/1.50      ( k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1))
% 8.00/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 8.00/1.50      | v1_funct_1(X2) != iProver_top ),
% 8.00/1.50      inference(renaming,[status(thm)],[c_34900]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_34914,plain,
% 8.00/1.50      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k5_relat_1(sK1,k2_funct_1(sK1))
% 8.00/1.50      | v1_funct_1(sK1) != iProver_top ),
% 8.00/1.50      inference(superposition,[status(thm)],[c_2415,c_34901]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_2412,plain,
% 8.00/1.50      ( v1_funct_1(sK1) = iProver_top ),
% 8.00/1.50      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_15,plain,
% 8.00/1.50      ( ~ v1_funct_1(X0)
% 8.00/1.50      | ~ v2_funct_1(X0)
% 8.00/1.50      | ~ v1_relat_1(X0)
% 8.00/1.50      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
% 8.00/1.50      inference(cnf_transformation,[],[f121]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_2440,plain,
% 8.00/1.50      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
% 8.00/1.50      | v1_funct_1(X0) != iProver_top
% 8.00/1.50      | v2_funct_1(X0) != iProver_top
% 8.00/1.50      | v1_relat_1(X0) != iProver_top ),
% 8.00/1.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_6732,plain,
% 8.00/1.50      ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
% 8.00/1.50      | v2_funct_1(sK1) != iProver_top
% 8.00/1.50      | v1_relat_1(sK1) != iProver_top ),
% 8.00/1.50      inference(superposition,[status(thm)],[c_2412,c_2440]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_2828,plain,
% 8.00/1.50      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 8.00/1.50      | v1_relat_1(sK1) ),
% 8.00/1.50      inference(instantiation,[status(thm)],[c_16]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_2843,plain,
% 8.00/1.50      ( ~ v1_funct_1(sK1)
% 8.00/1.50      | ~ v2_funct_1(sK1)
% 8.00/1.50      | ~ v1_relat_1(sK1)
% 8.00/1.50      | k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
% 8.00/1.50      inference(instantiation,[status(thm)],[c_15]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_7451,plain,
% 8.00/1.50      ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
% 8.00/1.50      inference(global_propositional_subsumption,
% 8.00/1.50                [status(thm)],
% 8.00/1.50                [c_6732,c_49,c_47,c_46,c_2828,c_2843,c_3048]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_34964,plain,
% 8.00/1.50      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
% 8.00/1.50      | v1_funct_1(sK1) != iProver_top ),
% 8.00/1.50      inference(light_normalisation,[status(thm)],[c_34914,c_7451]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_35061,plain,
% 8.00/1.50      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
% 8.00/1.50      inference(global_propositional_subsumption,
% 8.00/1.50                [status(thm)],
% 8.00/1.50                [c_34964,c_50]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_32,plain,
% 8.00/1.50      ( ~ v1_funct_2(X0,X1,X1)
% 8.00/1.50      | ~ v3_funct_2(X0,X1,X1)
% 8.00/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 8.00/1.50      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 8.00/1.50      | ~ v1_funct_1(X0) ),
% 8.00/1.50      inference(cnf_transformation,[],[f102]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_2428,plain,
% 8.00/1.50      ( v1_funct_2(X0,X1,X1) != iProver_top
% 8.00/1.50      | v3_funct_2(X0,X1,X1) != iProver_top
% 8.00/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 8.00/1.50      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) = iProver_top
% 8.00/1.50      | v1_funct_1(X0) != iProver_top ),
% 8.00/1.50      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_17872,plain,
% 8.00/1.50      ( k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1)
% 8.00/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 8.00/1.50      | v1_funct_1(X2) != iProver_top
% 8.00/1.50      | v1_funct_1(sK1) != iProver_top ),
% 8.00/1.50      inference(superposition,[status(thm)],[c_2415,c_2423]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_18014,plain,
% 8.00/1.50      ( v1_funct_1(X2) != iProver_top
% 8.00/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 8.00/1.50      | k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1) ),
% 8.00/1.50      inference(global_propositional_subsumption,
% 8.00/1.50                [status(thm)],
% 8.00/1.50                [c_17872,c_50]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_18015,plain,
% 8.00/1.50      ( k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1)
% 8.00/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 8.00/1.50      | v1_funct_1(X2) != iProver_top ),
% 8.00/1.50      inference(renaming,[status(thm)],[c_18014]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_18025,plain,
% 8.00/1.50      ( k1_partfun1(X0,X0,sK0,sK0,k2_funct_2(X0,X1),sK1) = k5_relat_1(k2_funct_2(X0,X1),sK1)
% 8.00/1.50      | v1_funct_2(X1,X0,X0) != iProver_top
% 8.00/1.50      | v3_funct_2(X1,X0,X0) != iProver_top
% 8.00/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 8.00/1.50      | v1_funct_1(X1) != iProver_top
% 8.00/1.50      | v1_funct_1(k2_funct_2(X0,X1)) != iProver_top ),
% 8.00/1.50      inference(superposition,[status(thm)],[c_2428,c_18015]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_35,plain,
% 8.00/1.50      ( ~ v1_funct_2(X0,X1,X1)
% 8.00/1.50      | ~ v3_funct_2(X0,X1,X1)
% 8.00/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 8.00/1.50      | ~ v1_funct_1(X0)
% 8.00/1.50      | v1_funct_1(k2_funct_2(X1,X0)) ),
% 8.00/1.50      inference(cnf_transformation,[],[f99]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_2425,plain,
% 8.00/1.50      ( v1_funct_2(X0,X1,X1) != iProver_top
% 8.00/1.50      | v3_funct_2(X0,X1,X1) != iProver_top
% 8.00/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 8.00/1.50      | v1_funct_1(X0) != iProver_top
% 8.00/1.50      | v1_funct_1(k2_funct_2(X1,X0)) = iProver_top ),
% 8.00/1.50      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_22026,plain,
% 8.00/1.50      ( k1_partfun1(X0,X0,sK0,sK0,k2_funct_2(X0,X1),sK1) = k5_relat_1(k2_funct_2(X0,X1),sK1)
% 8.00/1.50      | v1_funct_2(X1,X0,X0) != iProver_top
% 8.00/1.50      | v3_funct_2(X1,X0,X0) != iProver_top
% 8.00/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 8.00/1.50      | v1_funct_1(X1) != iProver_top ),
% 8.00/1.50      inference(forward_subsumption_resolution,
% 8.00/1.50                [status(thm)],
% 8.00/1.50                [c_18025,c_2425]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_22035,plain,
% 8.00/1.50      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1) = k5_relat_1(k2_funct_2(sK0,sK1),sK1)
% 8.00/1.50      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 8.00/1.50      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 8.00/1.50      | v1_funct_1(sK1) != iProver_top ),
% 8.00/1.50      inference(superposition,[status(thm)],[c_2415,c_22026]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_14,plain,
% 8.00/1.50      ( ~ v1_funct_1(X0)
% 8.00/1.50      | ~ v2_funct_1(X0)
% 8.00/1.50      | ~ v1_relat_1(X0)
% 8.00/1.50      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
% 8.00/1.50      inference(cnf_transformation,[],[f120]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_2441,plain,
% 8.00/1.50      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
% 8.00/1.50      | v1_funct_1(X0) != iProver_top
% 8.00/1.50      | v2_funct_1(X0) != iProver_top
% 8.00/1.50      | v1_relat_1(X0) != iProver_top ),
% 8.00/1.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_6753,plain,
% 8.00/1.50      ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1))
% 8.00/1.50      | v2_funct_1(sK1) != iProver_top
% 8.00/1.50      | v1_relat_1(sK1) != iProver_top ),
% 8.00/1.50      inference(superposition,[status(thm)],[c_2412,c_2441]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_6764,plain,
% 8.00/1.50      ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
% 8.00/1.50      | v2_funct_1(sK1) != iProver_top
% 8.00/1.50      | v1_relat_1(sK1) != iProver_top ),
% 8.00/1.50      inference(light_normalisation,[status(thm)],[c_6753,c_3873]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_2829,plain,
% 8.00/1.50      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 8.00/1.50      | v1_relat_1(sK1) = iProver_top ),
% 8.00/1.50      inference(predicate_to_equality,[status(thm)],[c_2828]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_7455,plain,
% 8.00/1.50      ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(sK0) ),
% 8.00/1.50      inference(global_propositional_subsumption,
% 8.00/1.50                [status(thm)],
% 8.00/1.50                [c_6764,c_50,c_52,c_53,c_2829,c_3049]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_38,plain,
% 8.00/1.50      ( ~ v1_funct_2(X0,X1,X1)
% 8.00/1.50      | ~ v3_funct_2(X0,X1,X1)
% 8.00/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 8.00/1.50      | ~ v1_funct_1(X0)
% 8.00/1.50      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 8.00/1.50      inference(cnf_transformation,[],[f105]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_2422,plain,
% 8.00/1.50      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
% 8.00/1.50      | v1_funct_2(X1,X0,X0) != iProver_top
% 8.00/1.50      | v3_funct_2(X1,X0,X0) != iProver_top
% 8.00/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 8.00/1.50      | v1_funct_1(X1) != iProver_top ),
% 8.00/1.50      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_16173,plain,
% 8.00/1.50      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
% 8.00/1.50      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 8.00/1.50      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 8.00/1.50      | v1_funct_1(sK1) != iProver_top ),
% 8.00/1.50      inference(superposition,[status(thm)],[c_2415,c_2422]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_2941,plain,
% 8.00/1.50      ( ~ v1_funct_2(sK1,X0,X0)
% 8.00/1.50      | ~ v3_funct_2(sK1,X0,X0)
% 8.00/1.50      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 8.00/1.50      | ~ v1_funct_1(sK1)
% 8.00/1.50      | k2_funct_2(X0,sK1) = k2_funct_1(sK1) ),
% 8.00/1.50      inference(instantiation,[status(thm)],[c_38]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_3115,plain,
% 8.00/1.50      ( ~ v1_funct_2(sK1,sK0,sK0)
% 8.00/1.50      | ~ v3_funct_2(sK1,sK0,sK0)
% 8.00/1.50      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 8.00/1.50      | ~ v1_funct_1(sK1)
% 8.00/1.50      | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 8.00/1.50      inference(instantiation,[status(thm)],[c_2941]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_16436,plain,
% 8.00/1.50      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 8.00/1.50      inference(global_propositional_subsumption,
% 8.00/1.50                [status(thm)],
% 8.00/1.50                [c_16173,c_49,c_48,c_47,c_46,c_3115]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_22086,plain,
% 8.00/1.50      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
% 8.00/1.50      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 8.00/1.50      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 8.00/1.50      | v1_funct_1(sK1) != iProver_top ),
% 8.00/1.50      inference(light_normalisation,
% 8.00/1.50                [status(thm)],
% 8.00/1.50                [c_22035,c_7455,c_16436]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_18029,plain,
% 8.00/1.50      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k5_relat_1(k2_funct_1(sK1),sK1)
% 8.00/1.50      | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
% 8.00/1.50      inference(superposition,[status(thm)],[c_11631,c_18015]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_18062,plain,
% 8.00/1.50      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
% 8.00/1.50      | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
% 8.00/1.50      inference(light_normalisation,[status(thm)],[c_18029,c_7455]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_22166,plain,
% 8.00/1.50      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0) ),
% 8.00/1.50      inference(global_propositional_subsumption,
% 8.00/1.50                [status(thm)],
% 8.00/1.50                [c_22086,c_50,c_51,c_52,c_53,c_3049,c_3269,c_4496,
% 8.00/1.50                 c_18062]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_45,negated_conjecture,
% 8.00/1.50      ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
% 8.00/1.50      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
% 8.00/1.50      inference(cnf_transformation,[],[f117]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_2416,plain,
% 8.00/1.50      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) != iProver_top
% 8.00/1.50      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) != iProver_top ),
% 8.00/1.50      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_16444,plain,
% 8.00/1.50      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) != iProver_top
% 8.00/1.50      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
% 8.00/1.50      inference(demodulation,[status(thm)],[c_16436,c_2416]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_22169,plain,
% 8.00/1.50      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top
% 8.00/1.50      | r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
% 8.00/1.50      inference(demodulation,[status(thm)],[c_22166,c_16444]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_35064,plain,
% 8.00/1.50      ( r2_relset_1(sK0,sK0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(sK0)) != iProver_top
% 8.00/1.50      | r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
% 8.00/1.50      inference(demodulation,[status(thm)],[c_35061,c_22169]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_36,plain,
% 8.00/1.50      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 8.00/1.50      inference(cnf_transformation,[],[f103]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_2424,plain,
% 8.00/1.50      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 8.00/1.50      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_20,plain,
% 8.00/1.50      ( r2_relset_1(X0,X1,X2,X2)
% 8.00/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 8.00/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 8.00/1.50      inference(cnf_transformation,[],[f87]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_2436,plain,
% 8.00/1.50      ( r2_relset_1(X0,X1,X2,X2) = iProver_top
% 8.00/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 8.00/1.50      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 8.00/1.50      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_8012,plain,
% 8.00/1.50      ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0)) = iProver_top
% 8.00/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
% 8.00/1.50      inference(superposition,[status(thm)],[c_2424,c_2436]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_25769,plain,
% 8.00/1.50      ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0)) = iProver_top ),
% 8.00/1.50      inference(superposition,[status(thm)],[c_2424,c_8012]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_35132,plain,
% 8.00/1.50      ( r2_relset_1(sK0,sK0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
% 8.00/1.50      inference(forward_subsumption_resolution,
% 8.00/1.50                [status(thm)],
% 8.00/1.50                [c_35064,c_25769]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_35134,plain,
% 8.00/1.50      ( sK0 = k1_xboole_0
% 8.00/1.50      | r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
% 8.00/1.50      inference(superposition,[status(thm)],[c_8879,c_35132]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_35139,plain,
% 8.00/1.50      ( sK0 = k1_xboole_0 ),
% 8.00/1.50      inference(forward_subsumption_resolution,
% 8.00/1.50                [status(thm)],
% 8.00/1.50                [c_35134,c_25769]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_35140,plain,
% 8.00/1.50      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(k1_xboole_0)) != iProver_top ),
% 8.00/1.50      inference(demodulation,[status(thm)],[c_35139,c_35132]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_10,plain,
% 8.00/1.50      ( ~ v1_relat_1(X0)
% 8.00/1.50      | k2_relat_1(X0) != k1_xboole_0
% 8.00/1.50      | k1_xboole_0 = X0 ),
% 8.00/1.50      inference(cnf_transformation,[],[f78]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_2443,plain,
% 8.00/1.50      ( k2_relat_1(X0) != k1_xboole_0
% 8.00/1.50      | k1_xboole_0 = X0
% 8.00/1.50      | v1_relat_1(X0) != iProver_top ),
% 8.00/1.50      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_4435,plain,
% 8.00/1.50      ( sK1 = k1_xboole_0
% 8.00/1.50      | sK0 != k1_xboole_0
% 8.00/1.50      | v1_relat_1(sK1) != iProver_top ),
% 8.00/1.50      inference(superposition,[status(thm)],[c_3873,c_2443]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_4442,plain,
% 8.00/1.50      ( ~ v1_relat_1(sK1) | sK1 = k1_xboole_0 | sK0 != k1_xboole_0 ),
% 8.00/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_4435]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_4618,plain,
% 8.00/1.50      ( sK0 != k1_xboole_0 | sK1 = k1_xboole_0 ),
% 8.00/1.50      inference(global_propositional_subsumption,
% 8.00/1.50                [status(thm)],
% 8.00/1.50                [c_4435,c_46,c_2828,c_4442]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_4619,plain,
% 8.00/1.50      ( sK1 = k1_xboole_0 | sK0 != k1_xboole_0 ),
% 8.00/1.50      inference(renaming,[status(thm)],[c_4618]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_35330,plain,
% 8.00/1.50      ( sK1 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 8.00/1.50      inference(demodulation,[status(thm)],[c_35139,c_4619]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_35351,plain,
% 8.00/1.50      ( sK1 = k1_xboole_0 ),
% 8.00/1.50      inference(equality_resolution_simp,[status(thm)],[c_35330]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_36205,plain,
% 8.00/1.50      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_relat_1(k1_xboole_0)),k6_partfun1(k1_xboole_0)) != iProver_top ),
% 8.00/1.50      inference(light_normalisation,[status(thm)],[c_35140,c_35351]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_13,plain,
% 8.00/1.50      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 8.00/1.50      inference(cnf_transformation,[],[f119]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_11,plain,
% 8.00/1.50      ( ~ v1_relat_1(X0)
% 8.00/1.50      | k1_relat_1(X0) != k1_xboole_0
% 8.00/1.50      | k1_xboole_0 = X0 ),
% 8.00/1.50      inference(cnf_transformation,[],[f77]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_2442,plain,
% 8.00/1.50      ( k1_relat_1(X0) != k1_xboole_0
% 8.00/1.50      | k1_xboole_0 = X0
% 8.00/1.50      | v1_relat_1(X0) != iProver_top ),
% 8.00/1.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_3761,plain,
% 8.00/1.50      ( k6_partfun1(X0) = k1_xboole_0
% 8.00/1.50      | k1_xboole_0 != X0
% 8.00/1.50      | v1_relat_1(k6_partfun1(X0)) != iProver_top ),
% 8.00/1.50      inference(superposition,[status(thm)],[c_13,c_2442]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_77,plain,
% 8.00/1.50      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 8.00/1.50      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_2823,plain,
% 8.00/1.50      ( ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 8.00/1.50      | v1_relat_1(k6_partfun1(X0)) ),
% 8.00/1.50      inference(instantiation,[status(thm)],[c_16]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_2824,plain,
% 8.00/1.50      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 8.00/1.50      | v1_relat_1(k6_partfun1(X0)) = iProver_top ),
% 8.00/1.50      inference(predicate_to_equality,[status(thm)],[c_2823]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_4444,plain,
% 8.00/1.50      ( k1_xboole_0 != X0 | k6_partfun1(X0) = k1_xboole_0 ),
% 8.00/1.50      inference(global_propositional_subsumption,
% 8.00/1.50                [status(thm)],
% 8.00/1.50                [c_3761,c_77,c_2824]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_4445,plain,
% 8.00/1.50      ( k6_partfun1(X0) = k1_xboole_0 | k1_xboole_0 != X0 ),
% 8.00/1.50      inference(renaming,[status(thm)],[c_4444]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_4449,plain,
% 8.00/1.50      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 8.00/1.50      inference(equality_resolution,[status(thm)],[c_4445]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_4829,plain,
% 8.00/1.50      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 8.00/1.50      inference(superposition,[status(thm)],[c_4449,c_13]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_36207,plain,
% 8.00/1.50      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 8.00/1.50      inference(light_normalisation,
% 8.00/1.50                [status(thm)],
% 8.00/1.50                [c_36205,c_4449,c_4829]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_7,plain,
% 8.00/1.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 8.00/1.50      inference(cnf_transformation,[],[f74]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_2813,plain,
% 8.00/1.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 8.00/1.50      inference(instantiation,[status(thm)],[c_7]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_2816,plain,
% 8.00/1.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
% 8.00/1.50      inference(predicate_to_equality,[status(thm)],[c_2813]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_2818,plain,
% 8.00/1.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 8.00/1.50      inference(instantiation,[status(thm)],[c_2816]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_123,plain,
% 8.00/1.50      ( r2_relset_1(X0,X1,X2,X2) = iProver_top
% 8.00/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 8.00/1.50      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 8.00/1.50      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(c_125,plain,
% 8.00/1.50      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top
% 8.00/1.50      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 8.00/1.50      inference(instantiation,[status(thm)],[c_123]) ).
% 8.00/1.50  
% 8.00/1.50  cnf(contradiction,plain,
% 8.00/1.50      ( $false ),
% 8.00/1.50      inference(minisat,[status(thm)],[c_36207,c_2818,c_125]) ).
% 8.00/1.50  
% 8.00/1.50  
% 8.00/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 8.00/1.50  
% 8.00/1.50  ------                               Statistics
% 8.00/1.50  
% 8.00/1.50  ------ General
% 8.00/1.50  
% 8.00/1.50  abstr_ref_over_cycles:                  0
% 8.00/1.50  abstr_ref_under_cycles:                 0
% 8.00/1.50  gc_basic_clause_elim:                   0
% 8.00/1.50  forced_gc_time:                         0
% 8.00/1.50  parsing_time:                           0.013
% 8.00/1.50  unif_index_cands_time:                  0.
% 8.00/1.50  unif_index_add_time:                    0.
% 8.00/1.50  orderings_time:                         0.
% 8.00/1.50  out_proof_time:                         0.02
% 8.00/1.50  total_time:                             0.864
% 8.00/1.50  num_of_symbols:                         55
% 8.00/1.50  num_of_terms:                           22422
% 8.00/1.50  
% 8.00/1.50  ------ Preprocessing
% 8.00/1.50  
% 8.00/1.50  num_of_splits:                          0
% 8.00/1.50  num_of_split_atoms:                     0
% 8.00/1.50  num_of_reused_defs:                     0
% 8.00/1.50  num_eq_ax_congr_red:                    29
% 8.00/1.50  num_of_sem_filtered_clauses:            1
% 8.00/1.50  num_of_subtypes:                        0
% 8.00/1.50  monotx_restored_types:                  0
% 8.00/1.50  sat_num_of_epr_types:                   0
% 8.00/1.50  sat_num_of_non_cyclic_types:            0
% 8.00/1.50  sat_guarded_non_collapsed_types:        0
% 8.00/1.50  num_pure_diseq_elim:                    0
% 8.00/1.50  simp_replaced_by:                       0
% 8.00/1.50  res_preprocessed:                       214
% 8.00/1.50  prep_upred:                             0
% 8.00/1.50  prep_unflattend:                        6
% 8.00/1.50  smt_new_axioms:                         0
% 8.00/1.50  pred_elim_cands:                        8
% 8.00/1.50  pred_elim:                              2
% 8.00/1.50  pred_elim_cl:                           3
% 8.00/1.50  pred_elim_cycles:                       6
% 8.00/1.50  merged_defs:                            8
% 8.00/1.50  merged_defs_ncl:                        0
% 8.00/1.50  bin_hyper_res:                          8
% 8.00/1.50  prep_cycles:                            4
% 8.00/1.50  pred_elim_time:                         0.013
% 8.00/1.50  splitting_time:                         0.
% 8.00/1.50  sem_filter_time:                        0.
% 8.00/1.50  monotx_time:                            0.001
% 8.00/1.50  subtype_inf_time:                       0.
% 8.00/1.50  
% 8.00/1.50  ------ Problem properties
% 8.00/1.50  
% 8.00/1.50  clauses:                                44
% 8.00/1.50  conjectures:                            5
% 8.00/1.50  epr:                                    6
% 8.00/1.50  horn:                                   39
% 8.00/1.50  ground:                                 5
% 8.00/1.50  unary:                                  12
% 8.00/1.50  binary:                                 6
% 8.00/1.50  lits:                                   133
% 8.00/1.50  lits_eq:                                31
% 8.00/1.50  fd_pure:                                0
% 8.00/1.50  fd_pseudo:                              0
% 8.00/1.50  fd_cond:                                6
% 8.00/1.50  fd_pseudo_cond:                         2
% 8.00/1.50  ac_symbols:                             0
% 8.00/1.50  
% 8.00/1.50  ------ Propositional Solver
% 8.00/1.50  
% 8.00/1.50  prop_solver_calls:                      30
% 8.00/1.50  prop_fast_solver_calls:                 3157
% 8.00/1.50  smt_solver_calls:                       0
% 8.00/1.50  smt_fast_solver_calls:                  0
% 8.00/1.50  prop_num_of_clauses:                    11187
% 8.00/1.50  prop_preprocess_simplified:             23411
% 8.00/1.50  prop_fo_subsumed:                       193
% 8.00/1.50  prop_solver_time:                       0.
% 8.00/1.50  smt_solver_time:                        0.
% 8.00/1.50  smt_fast_solver_time:                   0.
% 8.00/1.50  prop_fast_solver_time:                  0.
% 8.00/1.50  prop_unsat_core_time:                   0.001
% 8.00/1.50  
% 8.00/1.50  ------ QBF
% 8.00/1.50  
% 8.00/1.50  qbf_q_res:                              0
% 8.00/1.50  qbf_num_tautologies:                    0
% 8.00/1.50  qbf_prep_cycles:                        0
% 8.00/1.50  
% 8.00/1.50  ------ BMC1
% 8.00/1.50  
% 8.00/1.50  bmc1_current_bound:                     -1
% 8.00/1.50  bmc1_last_solved_bound:                 -1
% 8.00/1.50  bmc1_unsat_core_size:                   -1
% 8.00/1.50  bmc1_unsat_core_parents_size:           -1
% 8.00/1.50  bmc1_merge_next_fun:                    0
% 8.00/1.50  bmc1_unsat_core_clauses_time:           0.
% 8.00/1.50  
% 8.00/1.50  ------ Instantiation
% 8.00/1.50  
% 8.00/1.50  inst_num_of_clauses:                    3136
% 8.00/1.50  inst_num_in_passive:                    428
% 8.00/1.50  inst_num_in_active:                     1590
% 8.00/1.50  inst_num_in_unprocessed:                1120
% 8.00/1.50  inst_num_of_loops:                      1980
% 8.00/1.50  inst_num_of_learning_restarts:          0
% 8.00/1.50  inst_num_moves_active_passive:          388
% 8.00/1.50  inst_lit_activity:                      0
% 8.00/1.50  inst_lit_activity_moves:                1
% 8.00/1.50  inst_num_tautologies:                   0
% 8.00/1.50  inst_num_prop_implied:                  0
% 8.00/1.50  inst_num_existing_simplified:           0
% 8.00/1.50  inst_num_eq_res_simplified:             0
% 8.00/1.50  inst_num_child_elim:                    0
% 8.00/1.50  inst_num_of_dismatching_blockings:      1516
% 8.00/1.50  inst_num_of_non_proper_insts:           3605
% 8.00/1.50  inst_num_of_duplicates:                 0
% 8.00/1.50  inst_inst_num_from_inst_to_res:         0
% 8.00/1.50  inst_dismatching_checking_time:         0.
% 8.00/1.50  
% 8.00/1.50  ------ Resolution
% 8.00/1.50  
% 8.00/1.50  res_num_of_clauses:                     0
% 8.00/1.50  res_num_in_passive:                     0
% 8.00/1.50  res_num_in_active:                      0
% 8.00/1.50  res_num_of_loops:                       218
% 8.00/1.50  res_forward_subset_subsumed:            141
% 8.00/1.50  res_backward_subset_subsumed:           10
% 8.00/1.50  res_forward_subsumed:                   0
% 8.00/1.50  res_backward_subsumed:                  0
% 8.00/1.50  res_forward_subsumption_resolution:     2
% 8.00/1.50  res_backward_subsumption_resolution:    0
% 8.00/1.50  res_clause_to_clause_subsumption:       4450
% 8.00/1.50  res_orphan_elimination:                 0
% 8.00/1.50  res_tautology_del:                      96
% 8.00/1.50  res_num_eq_res_simplified:              0
% 8.00/1.50  res_num_sel_changes:                    0
% 8.00/1.50  res_moves_from_active_to_pass:          0
% 8.00/1.50  
% 8.00/1.50  ------ Superposition
% 8.00/1.50  
% 8.00/1.50  sup_time_total:                         0.
% 8.00/1.50  sup_time_generating:                    0.
% 8.00/1.50  sup_time_sim_full:                      0.
% 8.00/1.50  sup_time_sim_immed:                     0.
% 8.00/1.50  
% 8.00/1.50  sup_num_of_clauses:                     535
% 8.00/1.50  sup_num_in_active:                      159
% 8.00/1.50  sup_num_in_passive:                     376
% 8.00/1.50  sup_num_of_loops:                       395
% 8.00/1.50  sup_fw_superposition:                   795
% 8.00/1.50  sup_bw_superposition:                   281
% 8.00/1.50  sup_immediate_simplified:               574
% 8.00/1.50  sup_given_eliminated:                   5
% 8.00/1.50  comparisons_done:                       0
% 8.00/1.50  comparisons_avoided:                    52
% 8.00/1.50  
% 8.00/1.50  ------ Simplifications
% 8.00/1.50  
% 8.00/1.50  
% 8.00/1.50  sim_fw_subset_subsumed:                 57
% 8.00/1.50  sim_bw_subset_subsumed:                 36
% 8.00/1.50  sim_fw_subsumed:                        139
% 8.00/1.50  sim_bw_subsumed:                        46
% 8.00/1.50  sim_fw_subsumption_res:                 12
% 8.00/1.50  sim_bw_subsumption_res:                 0
% 8.00/1.50  sim_tautology_del:                      8
% 8.00/1.50  sim_eq_tautology_del:                   97
% 8.00/1.50  sim_eq_res_simp:                        6
% 8.00/1.50  sim_fw_demodulated:                     76
% 8.00/1.50  sim_bw_demodulated:                     238
% 8.00/1.50  sim_light_normalised:                   362
% 8.00/1.50  sim_joinable_taut:                      0
% 8.00/1.50  sim_joinable_simp:                      0
% 8.00/1.50  sim_ac_normalised:                      0
% 8.00/1.50  sim_smt_subsumption:                    0
% 8.00/1.50  
%------------------------------------------------------------------------------
