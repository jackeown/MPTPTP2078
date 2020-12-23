%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:19 EST 2020

% Result     : Theorem 7.58s
% Output     : CNFRefutation 7.58s
% Verified   : 
% Statistics : Number of formulae       :  253 (6004 expanded)
%              Number of clauses        :  158 (1827 expanded)
%              Number of leaves         :   24 (1166 expanded)
%              Depth                    :   30
%              Number of atoms          :  820 (28393 expanded)
%              Number of equality atoms :  380 (3219 expanded)
%              Maximal formula depth    :   12 (   4 average)
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

fof(f67,plain,
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

fof(f68,plain,
    ( ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) )
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK1,sK0,sK0)
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f57,f67])).

fof(f116,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f68])).

fof(f17,axiom,(
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

fof(f44,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f65,plain,(
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
    inference(nnf_transformation,[],[f45])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f114,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f68])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v5_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v5_relat_1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v5_relat_1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f77,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f60])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f61])).

fof(f122,plain,(
    ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f74])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f51,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f50])).

fof(f107,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f113,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f68])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f20,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f20])).

fof(f106,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_1(X1) = k2_funct_2(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f52])).

fof(f108,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X1) = k2_funct_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f115,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f68])).

fof(f19,axiom,(
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

fof(f48,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_2(k2_funct_2(X0,X1),X0,X0)
        & v1_funct_1(k2_funct_2(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f48])).

fof(f105,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f102,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k2_funct_2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f35,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f84,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f23,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f109,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f23])).

fof(f119,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f84,f109])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f42])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f85,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f118,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f85,f109])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_2(X2,X1)
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f46])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f100,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f117,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f68])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f40])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f64,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f83,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f58])).

fof(f71,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_44,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_2545,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_30,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_2556,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_10804,plain,
    ( k1_relset_1(sK0,sK0,sK1) = sK0
    | sK0 = k1_xboole_0
    | v1_funct_2(sK1,sK0,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2545,c_2556])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2564,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4314,plain,
    ( k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_2545,c_2564])).

cnf(c_10815,plain,
    ( k1_relat_1(sK1) = sK0
    | sK0 = k1_xboole_0
    | v1_funct_2(sK1,sK0,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10804,c_4314])).

cnf(c_46,negated_conjecture,
    ( v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_49,plain,
    ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_11260,plain,
    ( sK0 = k1_xboole_0
    | k1_relat_1(sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10815,c_49])).

cnf(c_11261,plain,
    ( k1_relat_1(sK1) = sK0
    | sK0 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_11260])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2565,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_5124,plain,
    ( m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(sK0)) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4314,c_2565])).

cnf(c_51,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_5532,plain,
    ( m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5124,c_51])).

cnf(c_9,plain,
    ( ~ v5_relat_1(X0,X1)
    | v5_relat_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2575,plain,
    ( v5_relat_1(X0,X1) != iProver_top
    | v5_relat_1(X2,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_9556,plain,
    ( v5_relat_1(k1_relat_1(sK1),X0) = iProver_top
    | v5_relat_1(sK0,X0) != iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5532,c_2575])).

cnf(c_11,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2573,plain,
    ( v5_relat_1(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2577,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f122])).

cnf(c_38,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_2550,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_17294,plain,
    ( k1_partfun1(X0,X1,X2,k1_xboole_0,X3,X4) = k5_relat_1(X3,X4)
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_2550])).

cnf(c_17581,plain,
    ( k1_partfun1(sK0,sK0,X0,k1_xboole_0,sK1,X1) = k5_relat_1(sK1,X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2545,c_17294])).

cnf(c_47,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_48,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_17732,plain,
    ( v1_funct_1(X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | k1_partfun1(sK0,sK0,X0,k1_xboole_0,sK1,X1) = k5_relat_1(sK1,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17581,c_48])).

cnf(c_17733,plain,
    ( k1_partfun1(sK0,sK0,X0,k1_xboole_0,sK1,X1) = k5_relat_1(sK1,X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_17732])).

cnf(c_17742,plain,
    ( k1_partfun1(sK0,sK0,X0,k1_xboole_0,sK1,X1) = k5_relat_1(sK1,X1)
    | r1_tarski(X1,k1_xboole_0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2577,c_17733])).

cnf(c_18349,plain,
    ( k1_partfun1(sK0,sK0,X0,k1_xboole_0,sK1,k2_relat_1(X1)) = k5_relat_1(sK1,k2_relat_1(X1))
    | v5_relat_1(X1,k1_xboole_0) != iProver_top
    | v1_funct_1(k2_relat_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2573,c_17742])).

cnf(c_24483,plain,
    ( k1_partfun1(sK0,sK0,X0,k1_xboole_0,sK1,k2_relat_1(k1_relat_1(sK1))) = k5_relat_1(sK1,k2_relat_1(k1_relat_1(sK1)))
    | v5_relat_1(sK0,k1_xboole_0) != iProver_top
    | v1_funct_1(k2_relat_1(k1_relat_1(sK1))) != iProver_top
    | v1_relat_1(k1_relat_1(sK1)) != iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9556,c_18349])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2924,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2926,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2924])).

cnf(c_6,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2925,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2928,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2925])).

cnf(c_37,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_3844,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_37])).

cnf(c_5349,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) ),
    inference(instantiation,[status(thm)],[c_2925])).

cnf(c_9648,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_5349])).

cnf(c_39,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_2549,plain,
    ( k2_funct_2(X0,X1) = k2_funct_1(X1)
    | v1_funct_2(X1,X0,X0) != iProver_top
    | v3_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_13961,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2545,c_2549])).

cnf(c_45,negated_conjecture,
    ( v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_3064,plain,
    ( ~ v1_funct_2(sK1,X0,X0)
    | ~ v3_funct_2(sK1,X0,X0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ v1_funct_1(sK1)
    | k2_funct_2(X0,sK1) = k2_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_39])).

cnf(c_3265,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_3064])).

cnf(c_14050,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13961,c_47,c_46,c_45,c_44,c_3265])).

cnf(c_33,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_2555,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_14083,plain,
    ( v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_14050,c_2555])).

cnf(c_50,plain,
    ( v3_funct_2(sK1,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_15051,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14083,c_48,c_49,c_50,c_51])).

cnf(c_17293,plain,
    ( k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_15051,c_2550])).

cnf(c_36,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ v3_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_2(X1,X0)) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_2552,plain,
    ( v1_funct_2(X0,X1,X1) != iProver_top
    | v3_funct_2(X0,X1,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_2(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_6135,plain,
    ( v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(k2_funct_2(sK0,sK1)) = iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2545,c_2552])).

cnf(c_3046,plain,
    ( ~ v1_funct_2(sK1,X0,X0)
    | ~ v3_funct_2(sK1,X0,X0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | v1_funct_1(k2_funct_2(X0,sK1))
    | ~ v1_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_36])).

cnf(c_3262,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v1_funct_1(k2_funct_2(sK0,sK1))
    | ~ v1_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_3046])).

cnf(c_3263,plain,
    ( v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(k2_funct_2(sK0,sK1)) = iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3262])).

cnf(c_6554,plain,
    ( v1_funct_1(k2_funct_2(sK0,sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6135,c_48,c_49,c_50,c_51,c_3263])).

cnf(c_14057,plain,
    ( v1_funct_1(k2_funct_1(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_14050,c_6554])).

cnf(c_25900,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17293,c_14057])).

cnf(c_25901,plain,
    ( k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_25900])).

cnf(c_25915,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k5_relat_1(sK1,k2_funct_1(sK1))
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2545,c_25901])).

cnf(c_2542,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_16,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_2568,plain,
    ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_8369,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
    | v2_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2542,c_2568])).

cnf(c_2940,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2972,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_23,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_3013,plain,
    ( ~ v3_funct_2(sK1,X0,X1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK1)
    | v2_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_3195,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | v2_funct_1(sK1) ),
    inference(instantiation,[status(thm)],[c_3013])).

cnf(c_8587,plain,
    ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8369,c_47,c_45,c_44,c_2940,c_2972,c_3195])).

cnf(c_25948,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
    | v1_funct_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_25915,c_8587])).

cnf(c_26097,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_25948,c_48])).

cnf(c_17290,plain,
    ( k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2545,c_2550])).

cnf(c_17855,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17290,c_48])).

cnf(c_17856,plain,
    ( k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_17855])).

cnf(c_17867,plain,
    ( k1_partfun1(X0,X0,sK0,sK0,k2_funct_2(X0,X1),sK1) = k5_relat_1(k2_funct_2(X0,X1),sK1)
    | v1_funct_2(X1,X0,X0) != iProver_top
    | v3_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(k2_funct_2(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2555,c_17856])).

cnf(c_19535,plain,
    ( k1_partfun1(X0,X0,sK0,sK0,k2_funct_2(X0,X1),sK1) = k5_relat_1(k2_funct_2(X0,X1),sK1)
    | v1_funct_2(X1,X0,X0) != iProver_top
    | v3_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_17867,c_2552])).

cnf(c_19544,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1) = k5_relat_1(k2_funct_2(sK0,sK1),sK1)
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2545,c_19535])).

cnf(c_15,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_2569,plain,
    ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_9526,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1))
    | v2_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2542,c_2569])).

cnf(c_22,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | v2_funct_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_32,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_578,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ v5_relat_1(X3,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X3)
    | X3 != X0
    | X4 != X2
    | k2_relat_1(X3) = X4 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_32])).

cnf(c_579,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ v5_relat_1(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(unflattening,[status(thm)],[c_578])).

cnf(c_583,plain,
    ( ~ v1_funct_1(X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v5_relat_1(X0,X2)
    | ~ v3_funct_2(X0,X1,X2)
    | k2_relat_1(X0) = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_579,c_17])).

cnf(c_584,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ v5_relat_1(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(renaming,[status(thm)],[c_583])).

cnf(c_18,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_599,plain,
    ( ~ v3_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) = X2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_584,c_18])).

cnf(c_2541,plain,
    ( k2_relat_1(X0) = X1
    | v3_funct_2(X0,X2,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_599])).

cnf(c_3487,plain,
    ( k2_relat_1(sK1) = sK0
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2545,c_2541])).

cnf(c_3028,plain,
    ( ~ v3_funct_2(sK1,X0,X1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK1)
    | k2_relat_1(sK1) = X1 ),
    inference(instantiation,[status(thm)],[c_599])).

cnf(c_3198,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | k2_relat_1(sK1) = sK0 ),
    inference(instantiation,[status(thm)],[c_3028])).

cnf(c_3805,plain,
    ( k2_relat_1(sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3487,c_47,c_45,c_44,c_3198])).

cnf(c_9537,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
    | v2_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9526,c_3805])).

cnf(c_2941,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2940])).

cnf(c_3196,plain,
    ( v3_funct_2(sK1,sK0,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v2_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3195])).

cnf(c_9878,plain,
    ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9537,c_48,c_50,c_51,c_2941,c_3196])).

cnf(c_19570,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v3_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_19544,c_9878,c_14050])).

cnf(c_17873,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k5_relat_1(k2_funct_1(sK1),sK1)
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_15051,c_17856])).

cnf(c_17890,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_17873,c_9878])).

cnf(c_20098,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19570,c_14057,c_17890])).

cnf(c_43,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_2546,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) != iProver_top
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_14058,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) != iProver_top
    | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_14050,c_2546])).

cnf(c_20101,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top
    | r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_20098,c_14058])).

cnf(c_26100,plain,
    ( r2_relset_1(sK0,sK0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(sK0)) != iProver_top
    | r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_26097,c_20101])).

cnf(c_26489,plain,
    ( sK0 = k1_xboole_0
    | r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11261,c_26100])).

cnf(c_26490,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
    | sK0 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_26489])).

cnf(c_21,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_3036,plain,
    ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
    | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_33191,plain,
    ( r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_3036])).

cnf(c_33195,plain,
    ( r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_33191])).

cnf(c_1619,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_34458,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(sK0)
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_1619])).

cnf(c_34459,plain,
    ( sK0 != X0
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34458])).

cnf(c_34461,plain,
    ( sK0 != k1_xboole_0
    | v1_relat_1(sK0) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_34459])).

cnf(c_35995,plain,
    ( v1_relat_1(k1_relat_1(sK1)) != iProver_top
    | v1_funct_1(k2_relat_1(k1_relat_1(sK1))) != iProver_top
    | v5_relat_1(sK0,k1_xboole_0) != iProver_top
    | k1_partfun1(sK0,sK0,X0,k1_xboole_0,sK1,k2_relat_1(k1_relat_1(sK1))) = k5_relat_1(sK1,k2_relat_1(k1_relat_1(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_24483,c_2926,c_2928,c_3844,c_9648,c_26490,c_33195,c_34461])).

cnf(c_35996,plain,
    ( k1_partfun1(sK0,sK0,X0,k1_xboole_0,sK1,k2_relat_1(k1_relat_1(sK1))) = k5_relat_1(sK1,k2_relat_1(k1_relat_1(sK1)))
    | v5_relat_1(sK0,k1_xboole_0) != iProver_top
    | v1_funct_1(k2_relat_1(k1_relat_1(sK1))) != iProver_top
    | v1_relat_1(k1_relat_1(sK1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_35995])).

cnf(c_36005,plain,
    ( k1_partfun1(sK0,sK0,X0,k1_xboole_0,sK1,k2_relat_1(k1_relat_1(sK1))) = k5_relat_1(sK1,k2_relat_1(k1_relat_1(sK1)))
    | sK0 = k1_xboole_0
    | v5_relat_1(sK0,k1_xboole_0) != iProver_top
    | v1_funct_1(k2_relat_1(sK0)) != iProver_top
    | v1_relat_1(k1_relat_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11261,c_35996])).

cnf(c_36226,plain,
    ( sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_36005,c_3844,c_9648,c_26490,c_33195])).

cnf(c_36285,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(k1_xboole_0)) != iProver_top
    | r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),k6_partfun1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_36226,c_26100])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) = k1_xboole_0
    | k2_relat_1(X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2571,plain,
    ( k1_relat_1(X0) = k1_xboole_0
    | k2_relat_1(X0) != k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4306,plain,
    ( k1_relat_1(sK1) = k1_xboole_0
    | sK0 != k1_xboole_0
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3805,c_2571])).

cnf(c_4307,plain,
    ( ~ v1_relat_1(sK1)
    | k1_relat_1(sK1) = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4306])).

cnf(c_4510,plain,
    ( sK0 != k1_xboole_0
    | k1_relat_1(sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4306,c_44,c_2940,c_4307])).

cnf(c_4511,plain,
    ( k1_relat_1(sK1) = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_4510])).

cnf(c_36386,plain,
    ( k1_relat_1(sK1) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_36226,c_4511])).

cnf(c_36410,plain,
    ( k1_relat_1(sK1) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_36386])).

cnf(c_36767,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),k6_partfun1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_36285,c_36410])).

cnf(c_2551,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_3190,plain,
    ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_2551])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2576,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3280,plain,
    ( r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3190,c_2576])).

cnf(c_2578,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3277,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2578,c_2576])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2580,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_5093,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3277,c_2580])).

cnf(c_7698,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3280,c_5093])).

cnf(c_36769,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_36767,c_7698])).

cnf(c_2930,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2928])).

cnf(c_112,plain,
    ( r2_relset_1(X0,X1,X2,X2) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_114,plain,
    ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_112])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_36769,c_2930,c_114])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 19:25:12 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 7.58/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.58/1.50  
% 7.58/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.58/1.50  
% 7.58/1.50  ------  iProver source info
% 7.58/1.50  
% 7.58/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.58/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.58/1.50  git: non_committed_changes: false
% 7.58/1.50  git: last_make_outside_of_git: false
% 7.58/1.50  
% 7.58/1.50  ------ 
% 7.58/1.50  
% 7.58/1.50  ------ Input Options
% 7.58/1.50  
% 7.58/1.50  --out_options                           all
% 7.58/1.50  --tptp_safe_out                         true
% 7.58/1.50  --problem_path                          ""
% 7.58/1.50  --include_path                          ""
% 7.58/1.50  --clausifier                            res/vclausify_rel
% 7.58/1.50  --clausifier_options                    --mode clausify
% 7.58/1.50  --stdin                                 false
% 7.58/1.50  --stats_out                             all
% 7.58/1.50  
% 7.58/1.50  ------ General Options
% 7.58/1.50  
% 7.58/1.50  --fof                                   false
% 7.58/1.50  --time_out_real                         305.
% 7.58/1.50  --time_out_virtual                      -1.
% 7.58/1.50  --symbol_type_check                     false
% 7.58/1.50  --clausify_out                          false
% 7.58/1.50  --sig_cnt_out                           false
% 7.58/1.50  --trig_cnt_out                          false
% 7.58/1.50  --trig_cnt_out_tolerance                1.
% 7.58/1.50  --trig_cnt_out_sk_spl                   false
% 7.58/1.50  --abstr_cl_out                          false
% 7.58/1.50  
% 7.58/1.50  ------ Global Options
% 7.58/1.50  
% 7.58/1.50  --schedule                              default
% 7.58/1.50  --add_important_lit                     false
% 7.58/1.50  --prop_solver_per_cl                    1000
% 7.58/1.50  --min_unsat_core                        false
% 7.58/1.50  --soft_assumptions                      false
% 7.58/1.50  --soft_lemma_size                       3
% 7.58/1.50  --prop_impl_unit_size                   0
% 7.58/1.50  --prop_impl_unit                        []
% 7.58/1.50  --share_sel_clauses                     true
% 7.58/1.50  --reset_solvers                         false
% 7.58/1.50  --bc_imp_inh                            [conj_cone]
% 7.58/1.50  --conj_cone_tolerance                   3.
% 7.58/1.50  --extra_neg_conj                        none
% 7.58/1.50  --large_theory_mode                     true
% 7.58/1.50  --prolific_symb_bound                   200
% 7.58/1.50  --lt_threshold                          2000
% 7.58/1.50  --clause_weak_htbl                      true
% 7.58/1.50  --gc_record_bc_elim                     false
% 7.58/1.50  
% 7.58/1.50  ------ Preprocessing Options
% 7.58/1.50  
% 7.58/1.50  --preprocessing_flag                    true
% 7.58/1.50  --time_out_prep_mult                    0.1
% 7.58/1.50  --splitting_mode                        input
% 7.58/1.50  --splitting_grd                         true
% 7.58/1.50  --splitting_cvd                         false
% 7.58/1.50  --splitting_cvd_svl                     false
% 7.58/1.50  --splitting_nvd                         32
% 7.58/1.50  --sub_typing                            true
% 7.58/1.50  --prep_gs_sim                           true
% 7.58/1.50  --prep_unflatten                        true
% 7.58/1.50  --prep_res_sim                          true
% 7.58/1.50  --prep_upred                            true
% 7.58/1.50  --prep_sem_filter                       exhaustive
% 7.58/1.50  --prep_sem_filter_out                   false
% 7.58/1.50  --pred_elim                             true
% 7.58/1.50  --res_sim_input                         true
% 7.58/1.50  --eq_ax_congr_red                       true
% 7.58/1.50  --pure_diseq_elim                       true
% 7.58/1.50  --brand_transform                       false
% 7.58/1.50  --non_eq_to_eq                          false
% 7.58/1.50  --prep_def_merge                        true
% 7.58/1.50  --prep_def_merge_prop_impl              false
% 7.58/1.50  --prep_def_merge_mbd                    true
% 7.58/1.50  --prep_def_merge_tr_red                 false
% 7.58/1.50  --prep_def_merge_tr_cl                  false
% 7.58/1.50  --smt_preprocessing                     true
% 7.58/1.50  --smt_ac_axioms                         fast
% 7.58/1.50  --preprocessed_out                      false
% 7.58/1.50  --preprocessed_stats                    false
% 7.58/1.50  
% 7.58/1.50  ------ Abstraction refinement Options
% 7.58/1.50  
% 7.58/1.50  --abstr_ref                             []
% 7.58/1.50  --abstr_ref_prep                        false
% 7.58/1.50  --abstr_ref_until_sat                   false
% 7.58/1.50  --abstr_ref_sig_restrict                funpre
% 7.58/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.58/1.50  --abstr_ref_under                       []
% 7.58/1.50  
% 7.58/1.50  ------ SAT Options
% 7.58/1.50  
% 7.58/1.50  --sat_mode                              false
% 7.58/1.50  --sat_fm_restart_options                ""
% 7.58/1.50  --sat_gr_def                            false
% 7.58/1.50  --sat_epr_types                         true
% 7.58/1.50  --sat_non_cyclic_types                  false
% 7.58/1.50  --sat_finite_models                     false
% 7.58/1.50  --sat_fm_lemmas                         false
% 7.58/1.50  --sat_fm_prep                           false
% 7.58/1.50  --sat_fm_uc_incr                        true
% 7.58/1.50  --sat_out_model                         small
% 7.58/1.50  --sat_out_clauses                       false
% 7.58/1.50  
% 7.58/1.50  ------ QBF Options
% 7.58/1.50  
% 7.58/1.50  --qbf_mode                              false
% 7.58/1.50  --qbf_elim_univ                         false
% 7.58/1.50  --qbf_dom_inst                          none
% 7.58/1.50  --qbf_dom_pre_inst                      false
% 7.58/1.50  --qbf_sk_in                             false
% 7.58/1.50  --qbf_pred_elim                         true
% 7.58/1.50  --qbf_split                             512
% 7.58/1.50  
% 7.58/1.50  ------ BMC1 Options
% 7.58/1.50  
% 7.58/1.50  --bmc1_incremental                      false
% 7.58/1.50  --bmc1_axioms                           reachable_all
% 7.58/1.50  --bmc1_min_bound                        0
% 7.58/1.50  --bmc1_max_bound                        -1
% 7.58/1.50  --bmc1_max_bound_default                -1
% 7.58/1.50  --bmc1_symbol_reachability              true
% 7.58/1.50  --bmc1_property_lemmas                  false
% 7.58/1.50  --bmc1_k_induction                      false
% 7.58/1.50  --bmc1_non_equiv_states                 false
% 7.58/1.50  --bmc1_deadlock                         false
% 7.58/1.50  --bmc1_ucm                              false
% 7.58/1.50  --bmc1_add_unsat_core                   none
% 7.58/1.50  --bmc1_unsat_core_children              false
% 7.58/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.58/1.50  --bmc1_out_stat                         full
% 7.58/1.50  --bmc1_ground_init                      false
% 7.58/1.50  --bmc1_pre_inst_next_state              false
% 7.58/1.50  --bmc1_pre_inst_state                   false
% 7.58/1.50  --bmc1_pre_inst_reach_state             false
% 7.58/1.50  --bmc1_out_unsat_core                   false
% 7.58/1.50  --bmc1_aig_witness_out                  false
% 7.58/1.50  --bmc1_verbose                          false
% 7.58/1.50  --bmc1_dump_clauses_tptp                false
% 7.58/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.58/1.50  --bmc1_dump_file                        -
% 7.58/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.58/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.58/1.50  --bmc1_ucm_extend_mode                  1
% 7.58/1.50  --bmc1_ucm_init_mode                    2
% 7.58/1.50  --bmc1_ucm_cone_mode                    none
% 7.58/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.58/1.50  --bmc1_ucm_relax_model                  4
% 7.58/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.58/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.58/1.50  --bmc1_ucm_layered_model                none
% 7.58/1.50  --bmc1_ucm_max_lemma_size               10
% 7.58/1.50  
% 7.58/1.50  ------ AIG Options
% 7.58/1.50  
% 7.58/1.50  --aig_mode                              false
% 7.58/1.50  
% 7.58/1.50  ------ Instantiation Options
% 7.58/1.50  
% 7.58/1.50  --instantiation_flag                    true
% 7.58/1.50  --inst_sos_flag                         false
% 7.58/1.50  --inst_sos_phase                        true
% 7.58/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.58/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.58/1.50  --inst_lit_sel_side                     num_symb
% 7.58/1.50  --inst_solver_per_active                1400
% 7.58/1.50  --inst_solver_calls_frac                1.
% 7.58/1.50  --inst_passive_queue_type               priority_queues
% 7.58/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.58/1.50  --inst_passive_queues_freq              [25;2]
% 7.58/1.50  --inst_dismatching                      true
% 7.58/1.50  --inst_eager_unprocessed_to_passive     true
% 7.58/1.50  --inst_prop_sim_given                   true
% 7.58/1.50  --inst_prop_sim_new                     false
% 7.58/1.50  --inst_subs_new                         false
% 7.58/1.50  --inst_eq_res_simp                      false
% 7.58/1.50  --inst_subs_given                       false
% 7.58/1.50  --inst_orphan_elimination               true
% 7.58/1.50  --inst_learning_loop_flag               true
% 7.58/1.50  --inst_learning_start                   3000
% 7.58/1.50  --inst_learning_factor                  2
% 7.58/1.50  --inst_start_prop_sim_after_learn       3
% 7.58/1.50  --inst_sel_renew                        solver
% 7.58/1.50  --inst_lit_activity_flag                true
% 7.58/1.50  --inst_restr_to_given                   false
% 7.58/1.50  --inst_activity_threshold               500
% 7.58/1.50  --inst_out_proof                        true
% 7.58/1.50  
% 7.58/1.50  ------ Resolution Options
% 7.58/1.50  
% 7.58/1.50  --resolution_flag                       true
% 7.58/1.50  --res_lit_sel                           adaptive
% 7.58/1.50  --res_lit_sel_side                      none
% 7.58/1.50  --res_ordering                          kbo
% 7.58/1.50  --res_to_prop_solver                    active
% 7.58/1.50  --res_prop_simpl_new                    false
% 7.58/1.50  --res_prop_simpl_given                  true
% 7.58/1.50  --res_passive_queue_type                priority_queues
% 7.58/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.58/1.50  --res_passive_queues_freq               [15;5]
% 7.58/1.50  --res_forward_subs                      full
% 7.58/1.50  --res_backward_subs                     full
% 7.58/1.50  --res_forward_subs_resolution           true
% 7.58/1.50  --res_backward_subs_resolution          true
% 7.58/1.50  --res_orphan_elimination                true
% 7.58/1.50  --res_time_limit                        2.
% 7.58/1.50  --res_out_proof                         true
% 7.58/1.50  
% 7.58/1.50  ------ Superposition Options
% 7.58/1.50  
% 7.58/1.50  --superposition_flag                    true
% 7.58/1.50  --sup_passive_queue_type                priority_queues
% 7.58/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.58/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.58/1.50  --demod_completeness_check              fast
% 7.58/1.50  --demod_use_ground                      true
% 7.58/1.50  --sup_to_prop_solver                    passive
% 7.58/1.50  --sup_prop_simpl_new                    true
% 7.58/1.50  --sup_prop_simpl_given                  true
% 7.58/1.50  --sup_fun_splitting                     false
% 7.58/1.50  --sup_smt_interval                      50000
% 7.58/1.50  
% 7.58/1.50  ------ Superposition Simplification Setup
% 7.58/1.50  
% 7.58/1.50  --sup_indices_passive                   []
% 7.58/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.58/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.58/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.58/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.58/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.58/1.50  --sup_full_bw                           [BwDemod]
% 7.58/1.50  --sup_immed_triv                        [TrivRules]
% 7.58/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.58/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.58/1.50  --sup_immed_bw_main                     []
% 7.58/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.58/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.58/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.58/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.58/1.50  
% 7.58/1.50  ------ Combination Options
% 7.58/1.50  
% 7.58/1.50  --comb_res_mult                         3
% 7.58/1.50  --comb_sup_mult                         2
% 7.58/1.50  --comb_inst_mult                        10
% 7.58/1.50  
% 7.58/1.50  ------ Debug Options
% 7.58/1.50  
% 7.58/1.50  --dbg_backtrace                         false
% 7.58/1.50  --dbg_dump_prop_clauses                 false
% 7.58/1.50  --dbg_dump_prop_clauses_file            -
% 7.58/1.50  --dbg_out_stat                          false
% 7.58/1.50  ------ Parsing...
% 7.58/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.58/1.50  
% 7.58/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.58/1.50  
% 7.58/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.58/1.50  
% 7.58/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.58/1.50  ------ Proving...
% 7.58/1.50  ------ Problem Properties 
% 7.58/1.50  
% 7.58/1.50  
% 7.58/1.50  clauses                                 43
% 7.58/1.50  conjectures                             5
% 7.58/1.50  EPR                                     5
% 7.58/1.50  Horn                                    38
% 7.58/1.50  unary                                   10
% 7.58/1.50  binary                                  7
% 7.58/1.50  lits                                    122
% 7.58/1.50  lits eq                                 25
% 7.58/1.50  fd_pure                                 0
% 7.58/1.50  fd_pseudo                               0
% 7.58/1.50  fd_cond                                 4
% 7.58/1.50  fd_pseudo_cond                          2
% 7.58/1.50  AC symbols                              0
% 7.58/1.50  
% 7.58/1.50  ------ Schedule dynamic 5 is on 
% 7.58/1.50  
% 7.58/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.58/1.50  
% 7.58/1.50  
% 7.58/1.50  ------ 
% 7.58/1.50  Current options:
% 7.58/1.50  ------ 
% 7.58/1.50  
% 7.58/1.50  ------ Input Options
% 7.58/1.50  
% 7.58/1.50  --out_options                           all
% 7.58/1.50  --tptp_safe_out                         true
% 7.58/1.50  --problem_path                          ""
% 7.58/1.50  --include_path                          ""
% 7.58/1.50  --clausifier                            res/vclausify_rel
% 7.58/1.50  --clausifier_options                    --mode clausify
% 7.58/1.50  --stdin                                 false
% 7.58/1.50  --stats_out                             all
% 7.58/1.50  
% 7.58/1.50  ------ General Options
% 7.58/1.50  
% 7.58/1.50  --fof                                   false
% 7.58/1.50  --time_out_real                         305.
% 7.58/1.50  --time_out_virtual                      -1.
% 7.58/1.50  --symbol_type_check                     false
% 7.58/1.50  --clausify_out                          false
% 7.58/1.50  --sig_cnt_out                           false
% 7.58/1.50  --trig_cnt_out                          false
% 7.58/1.50  --trig_cnt_out_tolerance                1.
% 7.58/1.50  --trig_cnt_out_sk_spl                   false
% 7.58/1.50  --abstr_cl_out                          false
% 7.58/1.50  
% 7.58/1.50  ------ Global Options
% 7.58/1.50  
% 7.58/1.50  --schedule                              default
% 7.58/1.50  --add_important_lit                     false
% 7.58/1.50  --prop_solver_per_cl                    1000
% 7.58/1.50  --min_unsat_core                        false
% 7.58/1.50  --soft_assumptions                      false
% 7.58/1.50  --soft_lemma_size                       3
% 7.58/1.50  --prop_impl_unit_size                   0
% 7.58/1.50  --prop_impl_unit                        []
% 7.58/1.50  --share_sel_clauses                     true
% 7.58/1.50  --reset_solvers                         false
% 7.58/1.50  --bc_imp_inh                            [conj_cone]
% 7.58/1.50  --conj_cone_tolerance                   3.
% 7.58/1.50  --extra_neg_conj                        none
% 7.58/1.50  --large_theory_mode                     true
% 7.58/1.50  --prolific_symb_bound                   200
% 7.58/1.50  --lt_threshold                          2000
% 7.58/1.50  --clause_weak_htbl                      true
% 7.58/1.50  --gc_record_bc_elim                     false
% 7.58/1.50  
% 7.58/1.50  ------ Preprocessing Options
% 7.58/1.50  
% 7.58/1.50  --preprocessing_flag                    true
% 7.58/1.50  --time_out_prep_mult                    0.1
% 7.58/1.50  --splitting_mode                        input
% 7.58/1.50  --splitting_grd                         true
% 7.58/1.50  --splitting_cvd                         false
% 7.58/1.50  --splitting_cvd_svl                     false
% 7.58/1.50  --splitting_nvd                         32
% 7.58/1.50  --sub_typing                            true
% 7.58/1.50  --prep_gs_sim                           true
% 7.58/1.50  --prep_unflatten                        true
% 7.58/1.50  --prep_res_sim                          true
% 7.58/1.50  --prep_upred                            true
% 7.58/1.50  --prep_sem_filter                       exhaustive
% 7.58/1.50  --prep_sem_filter_out                   false
% 7.58/1.50  --pred_elim                             true
% 7.58/1.50  --res_sim_input                         true
% 7.58/1.50  --eq_ax_congr_red                       true
% 7.58/1.50  --pure_diseq_elim                       true
% 7.58/1.50  --brand_transform                       false
% 7.58/1.50  --non_eq_to_eq                          false
% 7.58/1.50  --prep_def_merge                        true
% 7.58/1.50  --prep_def_merge_prop_impl              false
% 7.58/1.50  --prep_def_merge_mbd                    true
% 7.58/1.50  --prep_def_merge_tr_red                 false
% 7.58/1.50  --prep_def_merge_tr_cl                  false
% 7.58/1.50  --smt_preprocessing                     true
% 7.58/1.50  --smt_ac_axioms                         fast
% 7.58/1.50  --preprocessed_out                      false
% 7.58/1.50  --preprocessed_stats                    false
% 7.58/1.50  
% 7.58/1.50  ------ Abstraction refinement Options
% 7.58/1.50  
% 7.58/1.50  --abstr_ref                             []
% 7.58/1.50  --abstr_ref_prep                        false
% 7.58/1.50  --abstr_ref_until_sat                   false
% 7.58/1.50  --abstr_ref_sig_restrict                funpre
% 7.58/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.58/1.50  --abstr_ref_under                       []
% 7.58/1.50  
% 7.58/1.50  ------ SAT Options
% 7.58/1.50  
% 7.58/1.50  --sat_mode                              false
% 7.58/1.50  --sat_fm_restart_options                ""
% 7.58/1.50  --sat_gr_def                            false
% 7.58/1.50  --sat_epr_types                         true
% 7.58/1.50  --sat_non_cyclic_types                  false
% 7.58/1.50  --sat_finite_models                     false
% 7.58/1.50  --sat_fm_lemmas                         false
% 7.58/1.50  --sat_fm_prep                           false
% 7.58/1.50  --sat_fm_uc_incr                        true
% 7.58/1.50  --sat_out_model                         small
% 7.58/1.50  --sat_out_clauses                       false
% 7.58/1.50  
% 7.58/1.50  ------ QBF Options
% 7.58/1.50  
% 7.58/1.50  --qbf_mode                              false
% 7.58/1.50  --qbf_elim_univ                         false
% 7.58/1.50  --qbf_dom_inst                          none
% 7.58/1.50  --qbf_dom_pre_inst                      false
% 7.58/1.50  --qbf_sk_in                             false
% 7.58/1.50  --qbf_pred_elim                         true
% 7.58/1.50  --qbf_split                             512
% 7.58/1.50  
% 7.58/1.50  ------ BMC1 Options
% 7.58/1.50  
% 7.58/1.50  --bmc1_incremental                      false
% 7.58/1.50  --bmc1_axioms                           reachable_all
% 7.58/1.50  --bmc1_min_bound                        0
% 7.58/1.50  --bmc1_max_bound                        -1
% 7.58/1.50  --bmc1_max_bound_default                -1
% 7.58/1.50  --bmc1_symbol_reachability              true
% 7.58/1.50  --bmc1_property_lemmas                  false
% 7.58/1.50  --bmc1_k_induction                      false
% 7.58/1.50  --bmc1_non_equiv_states                 false
% 7.58/1.50  --bmc1_deadlock                         false
% 7.58/1.50  --bmc1_ucm                              false
% 7.58/1.50  --bmc1_add_unsat_core                   none
% 7.58/1.50  --bmc1_unsat_core_children              false
% 7.58/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.58/1.50  --bmc1_out_stat                         full
% 7.58/1.50  --bmc1_ground_init                      false
% 7.58/1.50  --bmc1_pre_inst_next_state              false
% 7.58/1.50  --bmc1_pre_inst_state                   false
% 7.58/1.50  --bmc1_pre_inst_reach_state             false
% 7.58/1.50  --bmc1_out_unsat_core                   false
% 7.58/1.50  --bmc1_aig_witness_out                  false
% 7.58/1.50  --bmc1_verbose                          false
% 7.58/1.50  --bmc1_dump_clauses_tptp                false
% 7.58/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.58/1.50  --bmc1_dump_file                        -
% 7.58/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.58/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.58/1.50  --bmc1_ucm_extend_mode                  1
% 7.58/1.50  --bmc1_ucm_init_mode                    2
% 7.58/1.50  --bmc1_ucm_cone_mode                    none
% 7.58/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.58/1.50  --bmc1_ucm_relax_model                  4
% 7.58/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.58/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.58/1.50  --bmc1_ucm_layered_model                none
% 7.58/1.50  --bmc1_ucm_max_lemma_size               10
% 7.58/1.50  
% 7.58/1.50  ------ AIG Options
% 7.58/1.50  
% 7.58/1.50  --aig_mode                              false
% 7.58/1.50  
% 7.58/1.50  ------ Instantiation Options
% 7.58/1.50  
% 7.58/1.50  --instantiation_flag                    true
% 7.58/1.50  --inst_sos_flag                         false
% 7.58/1.50  --inst_sos_phase                        true
% 7.58/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.58/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.58/1.50  --inst_lit_sel_side                     none
% 7.58/1.50  --inst_solver_per_active                1400
% 7.58/1.50  --inst_solver_calls_frac                1.
% 7.58/1.50  --inst_passive_queue_type               priority_queues
% 7.58/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.58/1.50  --inst_passive_queues_freq              [25;2]
% 7.58/1.50  --inst_dismatching                      true
% 7.58/1.50  --inst_eager_unprocessed_to_passive     true
% 7.58/1.50  --inst_prop_sim_given                   true
% 7.58/1.50  --inst_prop_sim_new                     false
% 7.58/1.50  --inst_subs_new                         false
% 7.58/1.50  --inst_eq_res_simp                      false
% 7.58/1.50  --inst_subs_given                       false
% 7.58/1.50  --inst_orphan_elimination               true
% 7.58/1.50  --inst_learning_loop_flag               true
% 7.58/1.50  --inst_learning_start                   3000
% 7.58/1.50  --inst_learning_factor                  2
% 7.58/1.50  --inst_start_prop_sim_after_learn       3
% 7.58/1.50  --inst_sel_renew                        solver
% 7.58/1.50  --inst_lit_activity_flag                true
% 7.58/1.50  --inst_restr_to_given                   false
% 7.58/1.50  --inst_activity_threshold               500
% 7.58/1.50  --inst_out_proof                        true
% 7.58/1.50  
% 7.58/1.50  ------ Resolution Options
% 7.58/1.50  
% 7.58/1.50  --resolution_flag                       false
% 7.58/1.50  --res_lit_sel                           adaptive
% 7.58/1.50  --res_lit_sel_side                      none
% 7.58/1.50  --res_ordering                          kbo
% 7.58/1.50  --res_to_prop_solver                    active
% 7.58/1.50  --res_prop_simpl_new                    false
% 7.58/1.50  --res_prop_simpl_given                  true
% 7.58/1.50  --res_passive_queue_type                priority_queues
% 7.58/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.58/1.50  --res_passive_queues_freq               [15;5]
% 7.58/1.50  --res_forward_subs                      full
% 7.58/1.50  --res_backward_subs                     full
% 7.58/1.50  --res_forward_subs_resolution           true
% 7.58/1.50  --res_backward_subs_resolution          true
% 7.58/1.50  --res_orphan_elimination                true
% 7.58/1.50  --res_time_limit                        2.
% 7.58/1.50  --res_out_proof                         true
% 7.58/1.50  
% 7.58/1.50  ------ Superposition Options
% 7.58/1.50  
% 7.58/1.50  --superposition_flag                    true
% 7.58/1.50  --sup_passive_queue_type                priority_queues
% 7.58/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.58/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.58/1.50  --demod_completeness_check              fast
% 7.58/1.50  --demod_use_ground                      true
% 7.58/1.50  --sup_to_prop_solver                    passive
% 7.58/1.50  --sup_prop_simpl_new                    true
% 7.58/1.50  --sup_prop_simpl_given                  true
% 7.58/1.50  --sup_fun_splitting                     false
% 7.58/1.50  --sup_smt_interval                      50000
% 7.58/1.50  
% 7.58/1.50  ------ Superposition Simplification Setup
% 7.58/1.50  
% 7.58/1.50  --sup_indices_passive                   []
% 7.58/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.58/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.58/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.58/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.58/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.58/1.50  --sup_full_bw                           [BwDemod]
% 7.58/1.50  --sup_immed_triv                        [TrivRules]
% 7.58/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.58/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.58/1.50  --sup_immed_bw_main                     []
% 7.58/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.58/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.58/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.58/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.58/1.50  
% 7.58/1.50  ------ Combination Options
% 7.58/1.50  
% 7.58/1.50  --comb_res_mult                         3
% 7.58/1.50  --comb_sup_mult                         2
% 7.58/1.50  --comb_inst_mult                        10
% 7.58/1.50  
% 7.58/1.50  ------ Debug Options
% 7.58/1.50  
% 7.58/1.50  --dbg_backtrace                         false
% 7.58/1.50  --dbg_dump_prop_clauses                 false
% 7.58/1.50  --dbg_dump_prop_clauses_file            -
% 7.58/1.50  --dbg_out_stat                          false
% 7.58/1.50  
% 7.58/1.50  
% 7.58/1.50  
% 7.58/1.50  
% 7.58/1.50  ------ Proving...
% 7.58/1.50  
% 7.58/1.50  
% 7.58/1.50  % SZS status Theorem for theBenchmark.p
% 7.58/1.50  
% 7.58/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.58/1.50  
% 7.58/1.50  fof(f25,conjecture,(
% 7.58/1.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 7.58/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f26,negated_conjecture,(
% 7.58/1.50    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))))),
% 7.58/1.50    inference(negated_conjecture,[],[f25])).
% 7.58/1.50  
% 7.58/1.50  fof(f56,plain,(
% 7.58/1.50    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 7.58/1.50    inference(ennf_transformation,[],[f26])).
% 7.58/1.50  
% 7.58/1.50  fof(f57,plain,(
% 7.58/1.50    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 7.58/1.50    inference(flattening,[],[f56])).
% 7.58/1.50  
% 7.58/1.50  fof(f67,plain,(
% 7.58/1.50    ? [X0,X1] : ((~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,k2_funct_2(X0,X1),X1),k6_partfun1(X0)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,k2_funct_2(X0,X1)),k6_partfun1(X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 7.58/1.50    introduced(choice_axiom,[])).
% 7.58/1.50  
% 7.58/1.50  fof(f68,plain,(
% 7.58/1.50    (~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 7.58/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f57,f67])).
% 7.58/1.50  
% 7.58/1.50  fof(f116,plain,(
% 7.58/1.50    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 7.58/1.50    inference(cnf_transformation,[],[f68])).
% 7.58/1.50  
% 7.58/1.50  fof(f17,axiom,(
% 7.58/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 7.58/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f44,plain,(
% 7.58/1.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.58/1.50    inference(ennf_transformation,[],[f17])).
% 7.58/1.50  
% 7.58/1.50  fof(f45,plain,(
% 7.58/1.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.58/1.50    inference(flattening,[],[f44])).
% 7.58/1.50  
% 7.58/1.50  fof(f65,plain,(
% 7.58/1.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.58/1.50    inference(nnf_transformation,[],[f45])).
% 7.58/1.50  
% 7.58/1.50  fof(f94,plain,(
% 7.58/1.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.58/1.50    inference(cnf_transformation,[],[f65])).
% 7.58/1.50  
% 7.58/1.50  fof(f14,axiom,(
% 7.58/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 7.58/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f39,plain,(
% 7.58/1.50    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.58/1.50    inference(ennf_transformation,[],[f14])).
% 7.58/1.50  
% 7.58/1.50  fof(f89,plain,(
% 7.58/1.50    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.58/1.50    inference(cnf_transformation,[],[f39])).
% 7.58/1.50  
% 7.58/1.50  fof(f114,plain,(
% 7.58/1.50    v1_funct_2(sK1,sK0,sK0)),
% 7.58/1.50    inference(cnf_transformation,[],[f68])).
% 7.58/1.50  
% 7.58/1.50  fof(f13,axiom,(
% 7.58/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 7.58/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f38,plain,(
% 7.58/1.50    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.58/1.50    inference(ennf_transformation,[],[f13])).
% 7.58/1.50  
% 7.58/1.50  fof(f88,plain,(
% 7.58/1.50    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.58/1.50    inference(cnf_transformation,[],[f38])).
% 7.58/1.50  
% 7.58/1.50  fof(f6,axiom,(
% 7.58/1.50    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X1)) => v5_relat_1(X2,X0)))),
% 7.58/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f30,plain,(
% 7.58/1.50    ! [X0,X1] : (! [X2] : (v5_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X1))) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 7.58/1.50    inference(ennf_transformation,[],[f6])).
% 7.58/1.50  
% 7.58/1.50  fof(f31,plain,(
% 7.58/1.50    ! [X0,X1] : (! [X2] : (v5_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X1))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.58/1.50    inference(flattening,[],[f30])).
% 7.58/1.50  
% 7.58/1.50  fof(f78,plain,(
% 7.58/1.50    ( ! [X2,X0,X1] : (v5_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.58/1.50    inference(cnf_transformation,[],[f31])).
% 7.58/1.50  
% 7.58/1.50  fof(f7,axiom,(
% 7.58/1.50    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 7.58/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f32,plain,(
% 7.58/1.50    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.58/1.50    inference(ennf_transformation,[],[f7])).
% 7.58/1.50  
% 7.58/1.50  fof(f63,plain,(
% 7.58/1.50    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.58/1.50    inference(nnf_transformation,[],[f32])).
% 7.58/1.50  
% 7.58/1.50  fof(f79,plain,(
% 7.58/1.50    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.58/1.50    inference(cnf_transformation,[],[f63])).
% 7.58/1.50  
% 7.58/1.50  fof(f4,axiom,(
% 7.58/1.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.58/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f62,plain,(
% 7.58/1.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.58/1.50    inference(nnf_transformation,[],[f4])).
% 7.58/1.50  
% 7.58/1.50  fof(f77,plain,(
% 7.58/1.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.58/1.50    inference(cnf_transformation,[],[f62])).
% 7.58/1.50  
% 7.58/1.50  fof(f2,axiom,(
% 7.58/1.50    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.58/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f60,plain,(
% 7.58/1.50    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 7.58/1.50    inference(nnf_transformation,[],[f2])).
% 7.58/1.50  
% 7.58/1.50  fof(f61,plain,(
% 7.58/1.50    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 7.58/1.50    inference(flattening,[],[f60])).
% 7.58/1.50  
% 7.58/1.50  fof(f74,plain,(
% 7.58/1.50    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 7.58/1.50    inference(cnf_transformation,[],[f61])).
% 7.58/1.50  
% 7.58/1.50  fof(f122,plain,(
% 7.58/1.50    ( ! [X0] : (k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0) )),
% 7.58/1.50    inference(equality_resolution,[],[f74])).
% 7.58/1.50  
% 7.58/1.50  fof(f21,axiom,(
% 7.58/1.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 7.58/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f50,plain,(
% 7.58/1.50    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 7.58/1.50    inference(ennf_transformation,[],[f21])).
% 7.58/1.50  
% 7.58/1.50  fof(f51,plain,(
% 7.58/1.50    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 7.58/1.50    inference(flattening,[],[f50])).
% 7.58/1.50  
% 7.58/1.50  fof(f107,plain,(
% 7.58/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 7.58/1.50    inference(cnf_transformation,[],[f51])).
% 7.58/1.50  
% 7.58/1.50  fof(f113,plain,(
% 7.58/1.50    v1_funct_1(sK1)),
% 7.58/1.50    inference(cnf_transformation,[],[f68])).
% 7.58/1.50  
% 7.58/1.50  fof(f11,axiom,(
% 7.58/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.58/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f36,plain,(
% 7.58/1.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.58/1.50    inference(ennf_transformation,[],[f11])).
% 7.58/1.50  
% 7.58/1.50  fof(f86,plain,(
% 7.58/1.50    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.58/1.50    inference(cnf_transformation,[],[f36])).
% 7.58/1.50  
% 7.58/1.50  fof(f3,axiom,(
% 7.58/1.50    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 7.58/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f75,plain,(
% 7.58/1.50    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 7.58/1.50    inference(cnf_transformation,[],[f3])).
% 7.58/1.50  
% 7.58/1.50  fof(f20,axiom,(
% 7.58/1.50    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 7.58/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f27,plain,(
% 7.58/1.50    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 7.58/1.50    inference(pure_predicate_removal,[],[f20])).
% 7.58/1.50  
% 7.58/1.50  fof(f106,plain,(
% 7.58/1.50    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 7.58/1.50    inference(cnf_transformation,[],[f27])).
% 7.58/1.50  
% 7.58/1.50  fof(f22,axiom,(
% 7.58/1.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_1(X1) = k2_funct_2(X0,X1))),
% 7.58/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f52,plain,(
% 7.58/1.50    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 7.58/1.50    inference(ennf_transformation,[],[f22])).
% 7.58/1.50  
% 7.58/1.50  fof(f53,plain,(
% 7.58/1.50    ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 7.58/1.50    inference(flattening,[],[f52])).
% 7.58/1.50  
% 7.58/1.50  fof(f108,plain,(
% 7.58/1.50    ( ! [X0,X1] : (k2_funct_1(X1) = k2_funct_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 7.58/1.50    inference(cnf_transformation,[],[f53])).
% 7.58/1.50  
% 7.58/1.50  fof(f115,plain,(
% 7.58/1.50    v3_funct_2(sK1,sK0,sK0)),
% 7.58/1.50    inference(cnf_transformation,[],[f68])).
% 7.58/1.50  
% 7.58/1.50  fof(f19,axiom,(
% 7.58/1.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))))),
% 7.58/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f48,plain,(
% 7.58/1.50    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 7.58/1.50    inference(ennf_transformation,[],[f19])).
% 7.58/1.50  
% 7.58/1.50  fof(f49,plain,(
% 7.58/1.50    ! [X0,X1] : ((m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_2(k2_funct_2(X0,X1),X0,X0) & v1_funct_1(k2_funct_2(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 7.58/1.50    inference(flattening,[],[f48])).
% 7.58/1.50  
% 7.58/1.50  fof(f105,plain,(
% 7.58/1.50    ( ! [X0,X1] : (m1_subset_1(k2_funct_2(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 7.58/1.50    inference(cnf_transformation,[],[f49])).
% 7.58/1.50  
% 7.58/1.50  fof(f102,plain,(
% 7.58/1.50    ( ! [X0,X1] : (v1_funct_1(k2_funct_2(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 7.58/1.50    inference(cnf_transformation,[],[f49])).
% 7.58/1.50  
% 7.58/1.50  fof(f10,axiom,(
% 7.58/1.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 7.58/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f34,plain,(
% 7.58/1.50    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.58/1.50    inference(ennf_transformation,[],[f10])).
% 7.58/1.50  
% 7.58/1.50  fof(f35,plain,(
% 7.58/1.50    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.58/1.50    inference(flattening,[],[f34])).
% 7.58/1.50  
% 7.58/1.50  fof(f84,plain,(
% 7.58/1.50    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.58/1.50    inference(cnf_transformation,[],[f35])).
% 7.58/1.50  
% 7.58/1.50  fof(f23,axiom,(
% 7.58/1.50    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 7.58/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f109,plain,(
% 7.58/1.50    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 7.58/1.50    inference(cnf_transformation,[],[f23])).
% 7.58/1.50  
% 7.58/1.50  fof(f119,plain,(
% 7.58/1.50    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.58/1.50    inference(definition_unfolding,[],[f84,f109])).
% 7.58/1.50  
% 7.58/1.50  fof(f16,axiom,(
% 7.58/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 7.58/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f42,plain,(
% 7.58/1.50    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.58/1.50    inference(ennf_transformation,[],[f16])).
% 7.58/1.50  
% 7.58/1.50  fof(f43,plain,(
% 7.58/1.50    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.58/1.50    inference(flattening,[],[f42])).
% 7.58/1.50  
% 7.58/1.50  fof(f92,plain,(
% 7.58/1.50    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.58/1.50    inference(cnf_transformation,[],[f43])).
% 7.58/1.50  
% 7.58/1.50  fof(f85,plain,(
% 7.58/1.50    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.58/1.50    inference(cnf_transformation,[],[f35])).
% 7.58/1.50  
% 7.58/1.50  fof(f118,plain,(
% 7.58/1.50    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.58/1.50    inference(definition_unfolding,[],[f85,f109])).
% 7.58/1.50  
% 7.58/1.50  fof(f93,plain,(
% 7.58/1.50    ( ! [X2,X0,X1] : (v2_funct_2(X2,X1) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.58/1.50    inference(cnf_transformation,[],[f43])).
% 7.58/1.50  
% 7.58/1.50  fof(f18,axiom,(
% 7.58/1.50    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 7.58/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f46,plain,(
% 7.58/1.50    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 7.58/1.50    inference(ennf_transformation,[],[f18])).
% 7.58/1.50  
% 7.58/1.50  fof(f47,plain,(
% 7.58/1.50    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.58/1.50    inference(flattening,[],[f46])).
% 7.58/1.50  
% 7.58/1.50  fof(f66,plain,(
% 7.58/1.50    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.58/1.50    inference(nnf_transformation,[],[f47])).
% 7.58/1.50  
% 7.58/1.50  fof(f100,plain,(
% 7.58/1.50    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.58/1.50    inference(cnf_transformation,[],[f66])).
% 7.58/1.50  
% 7.58/1.50  fof(f12,axiom,(
% 7.58/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.58/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f28,plain,(
% 7.58/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 7.58/1.50    inference(pure_predicate_removal,[],[f12])).
% 7.58/1.50  
% 7.58/1.50  fof(f37,plain,(
% 7.58/1.50    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.58/1.50    inference(ennf_transformation,[],[f28])).
% 7.58/1.50  
% 7.58/1.50  fof(f87,plain,(
% 7.58/1.50    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.58/1.50    inference(cnf_transformation,[],[f37])).
% 7.58/1.50  
% 7.58/1.50  fof(f117,plain,(
% 7.58/1.50    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0))),
% 7.58/1.50    inference(cnf_transformation,[],[f68])).
% 7.58/1.50  
% 7.58/1.50  fof(f15,axiom,(
% 7.58/1.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 7.58/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f40,plain,(
% 7.58/1.50    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 7.58/1.50    inference(ennf_transformation,[],[f15])).
% 7.58/1.50  
% 7.58/1.50  fof(f41,plain,(
% 7.58/1.50    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.58/1.50    inference(flattening,[],[f40])).
% 7.58/1.50  
% 7.58/1.50  fof(f90,plain,(
% 7.58/1.50    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.58/1.50    inference(cnf_transformation,[],[f41])).
% 7.58/1.50  
% 7.58/1.50  fof(f9,axiom,(
% 7.58/1.50    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 7.58/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f33,plain,(
% 7.58/1.50    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 7.58/1.50    inference(ennf_transformation,[],[f9])).
% 7.58/1.50  
% 7.58/1.50  fof(f64,plain,(
% 7.58/1.50    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 7.58/1.50    inference(nnf_transformation,[],[f33])).
% 7.58/1.50  
% 7.58/1.50  fof(f83,plain,(
% 7.58/1.50    ( ! [X0] : (k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 7.58/1.50    inference(cnf_transformation,[],[f64])).
% 7.58/1.50  
% 7.58/1.50  fof(f76,plain,(
% 7.58/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.58/1.50    inference(cnf_transformation,[],[f62])).
% 7.58/1.50  
% 7.58/1.50  fof(f1,axiom,(
% 7.58/1.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.58/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.58/1.50  
% 7.58/1.50  fof(f58,plain,(
% 7.58/1.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.58/1.50    inference(nnf_transformation,[],[f1])).
% 7.58/1.50  
% 7.58/1.50  fof(f59,plain,(
% 7.58/1.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.58/1.50    inference(flattening,[],[f58])).
% 7.58/1.50  
% 7.58/1.50  fof(f71,plain,(
% 7.58/1.50    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.58/1.50    inference(cnf_transformation,[],[f59])).
% 7.58/1.50  
% 7.58/1.50  cnf(c_44,negated_conjecture,
% 7.58/1.50      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 7.58/1.50      inference(cnf_transformation,[],[f116]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_2545,plain,
% 7.58/1.50      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_30,plain,
% 7.58/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.58/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.58/1.50      | k1_relset_1(X1,X2,X0) = X1
% 7.58/1.50      | k1_xboole_0 = X2 ),
% 7.58/1.50      inference(cnf_transformation,[],[f94]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_2556,plain,
% 7.58/1.50      ( k1_relset_1(X0,X1,X2) = X0
% 7.58/1.50      | k1_xboole_0 = X1
% 7.58/1.50      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.58/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_10804,plain,
% 7.58/1.50      ( k1_relset_1(sK0,sK0,sK1) = sK0
% 7.58/1.50      | sK0 = k1_xboole_0
% 7.58/1.50      | v1_funct_2(sK1,sK0,sK0) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_2545,c_2556]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_20,plain,
% 7.58/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.58/1.50      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.58/1.50      inference(cnf_transformation,[],[f89]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_2564,plain,
% 7.58/1.50      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.58/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_4314,plain,
% 7.58/1.50      ( k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_2545,c_2564]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_10815,plain,
% 7.58/1.50      ( k1_relat_1(sK1) = sK0
% 7.58/1.50      | sK0 = k1_xboole_0
% 7.58/1.50      | v1_funct_2(sK1,sK0,sK0) != iProver_top ),
% 7.58/1.50      inference(demodulation,[status(thm)],[c_10804,c_4314]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_46,negated_conjecture,
% 7.58/1.50      ( v1_funct_2(sK1,sK0,sK0) ),
% 7.58/1.50      inference(cnf_transformation,[],[f114]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_49,plain,
% 7.58/1.50      ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_11260,plain,
% 7.58/1.50      ( sK0 = k1_xboole_0 | k1_relat_1(sK1) = sK0 ),
% 7.58/1.50      inference(global_propositional_subsumption,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_10815,c_49]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_11261,plain,
% 7.58/1.50      ( k1_relat_1(sK1) = sK0 | sK0 = k1_xboole_0 ),
% 7.58/1.50      inference(renaming,[status(thm)],[c_11260]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_19,plain,
% 7.58/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.58/1.50      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 7.58/1.50      inference(cnf_transformation,[],[f88]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_2565,plain,
% 7.58/1.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.58/1.50      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_5124,plain,
% 7.58/1.50      ( m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(sK0)) = iProver_top
% 7.58/1.50      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_4314,c_2565]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_51,plain,
% 7.58/1.50      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_5532,plain,
% 7.58/1.50      ( m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(sK0)) = iProver_top ),
% 7.58/1.50      inference(global_propositional_subsumption,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_5124,c_51]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_9,plain,
% 7.58/1.50      ( ~ v5_relat_1(X0,X1)
% 7.58/1.50      | v5_relat_1(X2,X1)
% 7.58/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
% 7.58/1.50      | ~ v1_relat_1(X0) ),
% 7.58/1.50      inference(cnf_transformation,[],[f78]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_2575,plain,
% 7.58/1.50      ( v5_relat_1(X0,X1) != iProver_top
% 7.58/1.50      | v5_relat_1(X2,X1) = iProver_top
% 7.58/1.50      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 7.58/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_9556,plain,
% 7.58/1.50      ( v5_relat_1(k1_relat_1(sK1),X0) = iProver_top
% 7.58/1.50      | v5_relat_1(sK0,X0) != iProver_top
% 7.58/1.50      | v1_relat_1(sK0) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_5532,c_2575]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_11,plain,
% 7.58/1.50      ( ~ v5_relat_1(X0,X1)
% 7.58/1.50      | r1_tarski(k2_relat_1(X0),X1)
% 7.58/1.50      | ~ v1_relat_1(X0) ),
% 7.58/1.50      inference(cnf_transformation,[],[f79]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_2573,plain,
% 7.58/1.50      ( v5_relat_1(X0,X1) != iProver_top
% 7.58/1.50      | r1_tarski(k2_relat_1(X0),X1) = iProver_top
% 7.58/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_7,plain,
% 7.58/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.58/1.50      inference(cnf_transformation,[],[f77]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_2577,plain,
% 7.58/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 7.58/1.50      | r1_tarski(X0,X1) != iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_3,plain,
% 7.58/1.50      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.58/1.50      inference(cnf_transformation,[],[f122]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_38,plain,
% 7.58/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.58/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.58/1.50      | ~ v1_funct_1(X0)
% 7.58/1.50      | ~ v1_funct_1(X3)
% 7.58/1.50      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 7.58/1.50      inference(cnf_transformation,[],[f107]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_2550,plain,
% 7.58/1.50      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 7.58/1.50      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 7.58/1.50      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.58/1.50      | v1_funct_1(X5) != iProver_top
% 7.58/1.50      | v1_funct_1(X4) != iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_17294,plain,
% 7.58/1.50      ( k1_partfun1(X0,X1,X2,k1_xboole_0,X3,X4) = k5_relat_1(X3,X4)
% 7.58/1.50      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.58/1.50      | m1_subset_1(X4,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.58/1.50      | v1_funct_1(X4) != iProver_top
% 7.58/1.50      | v1_funct_1(X3) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_3,c_2550]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_17581,plain,
% 7.58/1.50      ( k1_partfun1(sK0,sK0,X0,k1_xboole_0,sK1,X1) = k5_relat_1(sK1,X1)
% 7.58/1.50      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.58/1.50      | v1_funct_1(X1) != iProver_top
% 7.58/1.50      | v1_funct_1(sK1) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_2545,c_17294]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_47,negated_conjecture,
% 7.58/1.50      ( v1_funct_1(sK1) ),
% 7.58/1.50      inference(cnf_transformation,[],[f113]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_48,plain,
% 7.58/1.50      ( v1_funct_1(sK1) = iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_17732,plain,
% 7.58/1.50      ( v1_funct_1(X1) != iProver_top
% 7.58/1.50      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.58/1.50      | k1_partfun1(sK0,sK0,X0,k1_xboole_0,sK1,X1) = k5_relat_1(sK1,X1) ),
% 7.58/1.50      inference(global_propositional_subsumption,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_17581,c_48]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_17733,plain,
% 7.58/1.50      ( k1_partfun1(sK0,sK0,X0,k1_xboole_0,sK1,X1) = k5_relat_1(sK1,X1)
% 7.58/1.50      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.58/1.50      | v1_funct_1(X1) != iProver_top ),
% 7.58/1.50      inference(renaming,[status(thm)],[c_17732]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_17742,plain,
% 7.58/1.50      ( k1_partfun1(sK0,sK0,X0,k1_xboole_0,sK1,X1) = k5_relat_1(sK1,X1)
% 7.58/1.50      | r1_tarski(X1,k1_xboole_0) != iProver_top
% 7.58/1.50      | v1_funct_1(X1) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_2577,c_17733]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_18349,plain,
% 7.58/1.50      ( k1_partfun1(sK0,sK0,X0,k1_xboole_0,sK1,k2_relat_1(X1)) = k5_relat_1(sK1,k2_relat_1(X1))
% 7.58/1.50      | v5_relat_1(X1,k1_xboole_0) != iProver_top
% 7.58/1.50      | v1_funct_1(k2_relat_1(X1)) != iProver_top
% 7.58/1.50      | v1_relat_1(X1) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_2573,c_17742]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_24483,plain,
% 7.58/1.50      ( k1_partfun1(sK0,sK0,X0,k1_xboole_0,sK1,k2_relat_1(k1_relat_1(sK1))) = k5_relat_1(sK1,k2_relat_1(k1_relat_1(sK1)))
% 7.58/1.50      | v5_relat_1(sK0,k1_xboole_0) != iProver_top
% 7.58/1.50      | v1_funct_1(k2_relat_1(k1_relat_1(sK1))) != iProver_top
% 7.58/1.50      | v1_relat_1(k1_relat_1(sK1)) != iProver_top
% 7.58/1.50      | v1_relat_1(sK0) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_9556,c_18349]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_17,plain,
% 7.58/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.58/1.50      | v1_relat_1(X0) ),
% 7.58/1.50      inference(cnf_transformation,[],[f86]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_2924,plain,
% 7.58/1.50      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.58/1.50      | v1_relat_1(k1_xboole_0) ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_17]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_2926,plain,
% 7.58/1.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.58/1.50      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_2924]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_6,plain,
% 7.58/1.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 7.58/1.50      inference(cnf_transformation,[],[f75]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_2925,plain,
% 7.58/1.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_6]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_2928,plain,
% 7.58/1.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_2925]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_37,plain,
% 7.58/1.50      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 7.58/1.50      inference(cnf_transformation,[],[f106]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_3844,plain,
% 7.58/1.50      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_37]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_5349,plain,
% 7.58/1.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_2925]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_9648,plain,
% 7.58/1.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_5349]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_39,plain,
% 7.58/1.50      ( ~ v1_funct_2(X0,X1,X1)
% 7.58/1.50      | ~ v3_funct_2(X0,X1,X1)
% 7.58/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 7.58/1.50      | ~ v1_funct_1(X0)
% 7.58/1.50      | k2_funct_2(X1,X0) = k2_funct_1(X0) ),
% 7.58/1.50      inference(cnf_transformation,[],[f108]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_2549,plain,
% 7.58/1.50      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
% 7.58/1.50      | v1_funct_2(X1,X0,X0) != iProver_top
% 7.58/1.50      | v3_funct_2(X1,X0,X0) != iProver_top
% 7.58/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 7.58/1.50      | v1_funct_1(X1) != iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_13961,plain,
% 7.58/1.50      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
% 7.58/1.50      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 7.58/1.50      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 7.58/1.50      | v1_funct_1(sK1) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_2545,c_2549]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_45,negated_conjecture,
% 7.58/1.50      ( v3_funct_2(sK1,sK0,sK0) ),
% 7.58/1.50      inference(cnf_transformation,[],[f115]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_3064,plain,
% 7.58/1.50      ( ~ v1_funct_2(sK1,X0,X0)
% 7.58/1.50      | ~ v3_funct_2(sK1,X0,X0)
% 7.58/1.50      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 7.58/1.50      | ~ v1_funct_1(sK1)
% 7.58/1.50      | k2_funct_2(X0,sK1) = k2_funct_1(sK1) ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_39]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_3265,plain,
% 7.58/1.50      ( ~ v1_funct_2(sK1,sK0,sK0)
% 7.58/1.50      | ~ v3_funct_2(sK1,sK0,sK0)
% 7.58/1.50      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.58/1.50      | ~ v1_funct_1(sK1)
% 7.58/1.50      | k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_3064]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_14050,plain,
% 7.58/1.50      ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
% 7.58/1.50      inference(global_propositional_subsumption,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_13961,c_47,c_46,c_45,c_44,c_3265]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_33,plain,
% 7.58/1.50      ( ~ v1_funct_2(X0,X1,X1)
% 7.58/1.50      | ~ v3_funct_2(X0,X1,X1)
% 7.58/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 7.58/1.50      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 7.58/1.50      | ~ v1_funct_1(X0) ),
% 7.58/1.50      inference(cnf_transformation,[],[f105]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_2555,plain,
% 7.58/1.50      ( v1_funct_2(X0,X1,X1) != iProver_top
% 7.58/1.50      | v3_funct_2(X0,X1,X1) != iProver_top
% 7.58/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 7.58/1.50      | m1_subset_1(k2_funct_2(X1,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X1))) = iProver_top
% 7.58/1.50      | v1_funct_1(X0) != iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_14083,plain,
% 7.58/1.50      ( v1_funct_2(sK1,sK0,sK0) != iProver_top
% 7.58/1.50      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 7.58/1.50      | m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 7.58/1.50      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 7.58/1.50      | v1_funct_1(sK1) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_14050,c_2555]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_50,plain,
% 7.58/1.50      ( v3_funct_2(sK1,sK0,sK0) = iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_15051,plain,
% 7.58/1.50      ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 7.58/1.50      inference(global_propositional_subsumption,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_14083,c_48,c_49,c_50,c_51]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_17293,plain,
% 7.58/1.50      ( k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1))
% 7.58/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.58/1.50      | v1_funct_1(X2) != iProver_top
% 7.58/1.50      | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_15051,c_2550]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_36,plain,
% 7.58/1.50      ( ~ v1_funct_2(X0,X1,X1)
% 7.58/1.50      | ~ v3_funct_2(X0,X1,X1)
% 7.58/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 7.58/1.50      | ~ v1_funct_1(X0)
% 7.58/1.50      | v1_funct_1(k2_funct_2(X1,X0)) ),
% 7.58/1.50      inference(cnf_transformation,[],[f102]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_2552,plain,
% 7.58/1.50      ( v1_funct_2(X0,X1,X1) != iProver_top
% 7.58/1.50      | v3_funct_2(X0,X1,X1) != iProver_top
% 7.58/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top
% 7.58/1.50      | v1_funct_1(X0) != iProver_top
% 7.58/1.50      | v1_funct_1(k2_funct_2(X1,X0)) = iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_6135,plain,
% 7.58/1.50      ( v1_funct_2(sK1,sK0,sK0) != iProver_top
% 7.58/1.50      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 7.58/1.50      | v1_funct_1(k2_funct_2(sK0,sK1)) = iProver_top
% 7.58/1.50      | v1_funct_1(sK1) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_2545,c_2552]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_3046,plain,
% 7.58/1.50      ( ~ v1_funct_2(sK1,X0,X0)
% 7.58/1.50      | ~ v3_funct_2(sK1,X0,X0)
% 7.58/1.50      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 7.58/1.50      | v1_funct_1(k2_funct_2(X0,sK1))
% 7.58/1.50      | ~ v1_funct_1(sK1) ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_36]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_3262,plain,
% 7.58/1.50      ( ~ v1_funct_2(sK1,sK0,sK0)
% 7.58/1.50      | ~ v3_funct_2(sK1,sK0,sK0)
% 7.58/1.50      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.58/1.50      | v1_funct_1(k2_funct_2(sK0,sK1))
% 7.58/1.50      | ~ v1_funct_1(sK1) ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_3046]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_3263,plain,
% 7.58/1.50      ( v1_funct_2(sK1,sK0,sK0) != iProver_top
% 7.58/1.50      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 7.58/1.50      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 7.58/1.50      | v1_funct_1(k2_funct_2(sK0,sK1)) = iProver_top
% 7.58/1.50      | v1_funct_1(sK1) != iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_3262]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_6554,plain,
% 7.58/1.50      ( v1_funct_1(k2_funct_2(sK0,sK1)) = iProver_top ),
% 7.58/1.50      inference(global_propositional_subsumption,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_6135,c_48,c_49,c_50,c_51,c_3263]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_14057,plain,
% 7.58/1.50      ( v1_funct_1(k2_funct_1(sK1)) = iProver_top ),
% 7.58/1.50      inference(demodulation,[status(thm)],[c_14050,c_6554]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_25900,plain,
% 7.58/1.50      ( v1_funct_1(X2) != iProver_top
% 7.58/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.58/1.50      | k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1)) ),
% 7.58/1.50      inference(global_propositional_subsumption,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_17293,c_14057]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_25901,plain,
% 7.58/1.50      ( k1_partfun1(X0,X1,sK0,sK0,X2,k2_funct_1(sK1)) = k5_relat_1(X2,k2_funct_1(sK1))
% 7.58/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.58/1.50      | v1_funct_1(X2) != iProver_top ),
% 7.58/1.50      inference(renaming,[status(thm)],[c_25900]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_25915,plain,
% 7.58/1.50      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k5_relat_1(sK1,k2_funct_1(sK1))
% 7.58/1.50      | v1_funct_1(sK1) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_2545,c_25901]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_2542,plain,
% 7.58/1.50      ( v1_funct_1(sK1) = iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_16,plain,
% 7.58/1.50      ( ~ v1_funct_1(X0)
% 7.58/1.50      | ~ v2_funct_1(X0)
% 7.58/1.50      | ~ v1_relat_1(X0)
% 7.58/1.50      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
% 7.58/1.50      inference(cnf_transformation,[],[f119]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_2568,plain,
% 7.58/1.50      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
% 7.58/1.50      | v1_funct_1(X0) != iProver_top
% 7.58/1.50      | v2_funct_1(X0) != iProver_top
% 7.58/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_8369,plain,
% 7.58/1.50      ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
% 7.58/1.50      | v2_funct_1(sK1) != iProver_top
% 7.58/1.50      | v1_relat_1(sK1) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_2542,c_2568]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_2940,plain,
% 7.58/1.50      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.58/1.50      | v1_relat_1(sK1) ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_17]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_2972,plain,
% 7.58/1.50      ( ~ v1_funct_1(sK1)
% 7.58/1.50      | ~ v2_funct_1(sK1)
% 7.58/1.50      | ~ v1_relat_1(sK1)
% 7.58/1.50      | k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_16]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_23,plain,
% 7.58/1.50      ( ~ v3_funct_2(X0,X1,X2)
% 7.58/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.58/1.50      | ~ v1_funct_1(X0)
% 7.58/1.50      | v2_funct_1(X0) ),
% 7.58/1.50      inference(cnf_transformation,[],[f92]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_3013,plain,
% 7.58/1.50      ( ~ v3_funct_2(sK1,X0,X1)
% 7.58/1.50      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.58/1.50      | ~ v1_funct_1(sK1)
% 7.58/1.50      | v2_funct_1(sK1) ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_23]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_3195,plain,
% 7.58/1.50      ( ~ v3_funct_2(sK1,sK0,sK0)
% 7.58/1.50      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.58/1.50      | ~ v1_funct_1(sK1)
% 7.58/1.50      | v2_funct_1(sK1) ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_3013]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_8587,plain,
% 7.58/1.50      ( k5_relat_1(sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
% 7.58/1.50      inference(global_propositional_subsumption,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_8369,c_47,c_45,c_44,c_2940,c_2972,c_3195]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_25948,plain,
% 7.58/1.50      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1))
% 7.58/1.50      | v1_funct_1(sK1) != iProver_top ),
% 7.58/1.50      inference(light_normalisation,[status(thm)],[c_25915,c_8587]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_26097,plain,
% 7.58/1.50      ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)) = k6_partfun1(k1_relat_1(sK1)) ),
% 7.58/1.50      inference(global_propositional_subsumption,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_25948,c_48]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_17290,plain,
% 7.58/1.50      ( k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1)
% 7.58/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.58/1.50      | v1_funct_1(X2) != iProver_top
% 7.58/1.50      | v1_funct_1(sK1) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_2545,c_2550]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_17855,plain,
% 7.58/1.50      ( v1_funct_1(X2) != iProver_top
% 7.58/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.58/1.50      | k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1) ),
% 7.58/1.50      inference(global_propositional_subsumption,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_17290,c_48]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_17856,plain,
% 7.58/1.50      ( k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1)
% 7.58/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.58/1.50      | v1_funct_1(X2) != iProver_top ),
% 7.58/1.50      inference(renaming,[status(thm)],[c_17855]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_17867,plain,
% 7.58/1.50      ( k1_partfun1(X0,X0,sK0,sK0,k2_funct_2(X0,X1),sK1) = k5_relat_1(k2_funct_2(X0,X1),sK1)
% 7.58/1.50      | v1_funct_2(X1,X0,X0) != iProver_top
% 7.58/1.50      | v3_funct_2(X1,X0,X0) != iProver_top
% 7.58/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 7.58/1.50      | v1_funct_1(X1) != iProver_top
% 7.58/1.50      | v1_funct_1(k2_funct_2(X0,X1)) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_2555,c_17856]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_19535,plain,
% 7.58/1.50      ( k1_partfun1(X0,X0,sK0,sK0,k2_funct_2(X0,X1),sK1) = k5_relat_1(k2_funct_2(X0,X1),sK1)
% 7.58/1.50      | v1_funct_2(X1,X0,X0) != iProver_top
% 7.58/1.50      | v3_funct_2(X1,X0,X0) != iProver_top
% 7.58/1.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 7.58/1.50      | v1_funct_1(X1) != iProver_top ),
% 7.58/1.50      inference(forward_subsumption_resolution,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_17867,c_2552]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_19544,plain,
% 7.58/1.50      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1) = k5_relat_1(k2_funct_2(sK0,sK1),sK1)
% 7.58/1.50      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 7.58/1.50      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 7.58/1.50      | v1_funct_1(sK1) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_2545,c_19535]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_15,plain,
% 7.58/1.50      ( ~ v1_funct_1(X0)
% 7.58/1.50      | ~ v2_funct_1(X0)
% 7.58/1.50      | ~ v1_relat_1(X0)
% 7.58/1.50      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
% 7.58/1.50      inference(cnf_transformation,[],[f118]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_2569,plain,
% 7.58/1.50      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
% 7.58/1.50      | v1_funct_1(X0) != iProver_top
% 7.58/1.50      | v2_funct_1(X0) != iProver_top
% 7.58/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_9526,plain,
% 7.58/1.50      ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(k2_relat_1(sK1))
% 7.58/1.50      | v2_funct_1(sK1) != iProver_top
% 7.58/1.50      | v1_relat_1(sK1) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_2542,c_2569]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_22,plain,
% 7.58/1.50      ( ~ v3_funct_2(X0,X1,X2)
% 7.58/1.50      | v2_funct_2(X0,X2)
% 7.58/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.58/1.50      | ~ v1_funct_1(X0) ),
% 7.58/1.50      inference(cnf_transformation,[],[f93]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_32,plain,
% 7.58/1.50      ( ~ v2_funct_2(X0,X1)
% 7.58/1.50      | ~ v5_relat_1(X0,X1)
% 7.58/1.50      | ~ v1_relat_1(X0)
% 7.58/1.50      | k2_relat_1(X0) = X1 ),
% 7.58/1.50      inference(cnf_transformation,[],[f100]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_578,plain,
% 7.58/1.50      ( ~ v3_funct_2(X0,X1,X2)
% 7.58/1.50      | ~ v5_relat_1(X3,X4)
% 7.58/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.58/1.50      | ~ v1_funct_1(X0)
% 7.58/1.50      | ~ v1_relat_1(X3)
% 7.58/1.50      | X3 != X0
% 7.58/1.50      | X4 != X2
% 7.58/1.50      | k2_relat_1(X3) = X4 ),
% 7.58/1.50      inference(resolution_lifted,[status(thm)],[c_22,c_32]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_579,plain,
% 7.58/1.50      ( ~ v3_funct_2(X0,X1,X2)
% 7.58/1.50      | ~ v5_relat_1(X0,X2)
% 7.58/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.58/1.50      | ~ v1_funct_1(X0)
% 7.58/1.50      | ~ v1_relat_1(X0)
% 7.58/1.50      | k2_relat_1(X0) = X2 ),
% 7.58/1.50      inference(unflattening,[status(thm)],[c_578]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_583,plain,
% 7.58/1.50      ( ~ v1_funct_1(X0)
% 7.58/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.58/1.50      | ~ v5_relat_1(X0,X2)
% 7.58/1.50      | ~ v3_funct_2(X0,X1,X2)
% 7.58/1.50      | k2_relat_1(X0) = X2 ),
% 7.58/1.50      inference(global_propositional_subsumption,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_579,c_17]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_584,plain,
% 7.58/1.50      ( ~ v3_funct_2(X0,X1,X2)
% 7.58/1.50      | ~ v5_relat_1(X0,X2)
% 7.58/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.58/1.50      | ~ v1_funct_1(X0)
% 7.58/1.50      | k2_relat_1(X0) = X2 ),
% 7.58/1.50      inference(renaming,[status(thm)],[c_583]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_18,plain,
% 7.58/1.50      ( v5_relat_1(X0,X1)
% 7.58/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 7.58/1.50      inference(cnf_transformation,[],[f87]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_599,plain,
% 7.58/1.50      ( ~ v3_funct_2(X0,X1,X2)
% 7.58/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.58/1.50      | ~ v1_funct_1(X0)
% 7.58/1.50      | k2_relat_1(X0) = X2 ),
% 7.58/1.50      inference(forward_subsumption_resolution,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_584,c_18]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_2541,plain,
% 7.58/1.50      ( k2_relat_1(X0) = X1
% 7.58/1.50      | v3_funct_2(X0,X2,X1) != iProver_top
% 7.58/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 7.58/1.50      | v1_funct_1(X0) != iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_599]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_3487,plain,
% 7.58/1.50      ( k2_relat_1(sK1) = sK0
% 7.58/1.50      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 7.58/1.50      | v1_funct_1(sK1) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_2545,c_2541]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_3028,plain,
% 7.58/1.50      ( ~ v3_funct_2(sK1,X0,X1)
% 7.58/1.50      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.58/1.50      | ~ v1_funct_1(sK1)
% 7.58/1.50      | k2_relat_1(sK1) = X1 ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_599]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_3198,plain,
% 7.58/1.50      ( ~ v3_funct_2(sK1,sK0,sK0)
% 7.58/1.50      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.58/1.50      | ~ v1_funct_1(sK1)
% 7.58/1.50      | k2_relat_1(sK1) = sK0 ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_3028]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_3805,plain,
% 7.58/1.50      ( k2_relat_1(sK1) = sK0 ),
% 7.58/1.50      inference(global_propositional_subsumption,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_3487,c_47,c_45,c_44,c_3198]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_9537,plain,
% 7.58/1.50      ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
% 7.58/1.50      | v2_funct_1(sK1) != iProver_top
% 7.58/1.50      | v1_relat_1(sK1) != iProver_top ),
% 7.58/1.50      inference(light_normalisation,[status(thm)],[c_9526,c_3805]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_2941,plain,
% 7.58/1.50      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 7.58/1.50      | v1_relat_1(sK1) = iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_2940]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_3196,plain,
% 7.58/1.50      ( v3_funct_2(sK1,sK0,sK0) != iProver_top
% 7.58/1.50      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 7.58/1.50      | v1_funct_1(sK1) != iProver_top
% 7.58/1.50      | v2_funct_1(sK1) = iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_3195]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_9878,plain,
% 7.58/1.50      ( k5_relat_1(k2_funct_1(sK1),sK1) = k6_partfun1(sK0) ),
% 7.58/1.50      inference(global_propositional_subsumption,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_9537,c_48,c_50,c_51,c_2941,c_3196]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_19570,plain,
% 7.58/1.50      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
% 7.58/1.50      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 7.58/1.50      | v3_funct_2(sK1,sK0,sK0) != iProver_top
% 7.58/1.50      | v1_funct_1(sK1) != iProver_top ),
% 7.58/1.50      inference(light_normalisation,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_19544,c_9878,c_14050]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_17873,plain,
% 7.58/1.50      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k5_relat_1(k2_funct_1(sK1),sK1)
% 7.58/1.50      | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_15051,c_17856]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_17890,plain,
% 7.58/1.50      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0)
% 7.58/1.50      | v1_funct_1(k2_funct_1(sK1)) != iProver_top ),
% 7.58/1.50      inference(light_normalisation,[status(thm)],[c_17873,c_9878]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_20098,plain,
% 7.58/1.50      ( k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1) = k6_partfun1(sK0) ),
% 7.58/1.50      inference(global_propositional_subsumption,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_19570,c_14057,c_17890]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_43,negated_conjecture,
% 7.58/1.50      ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0))
% 7.58/1.50      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) ),
% 7.58/1.50      inference(cnf_transformation,[],[f117]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_2546,plain,
% 7.58/1.50      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_2(sK0,sK1),sK1),k6_partfun1(sK0)) != iProver_top
% 7.58/1.50      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_2(sK0,sK1)),k6_partfun1(sK0)) != iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_14058,plain,
% 7.58/1.50      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,k2_funct_1(sK1),sK1),k6_partfun1(sK0)) != iProver_top
% 7.58/1.50      | r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top ),
% 7.58/1.50      inference(demodulation,[status(thm)],[c_14050,c_2546]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_20101,plain,
% 7.58/1.50      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,k2_funct_1(sK1)),k6_partfun1(sK0)) != iProver_top
% 7.58/1.50      | r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
% 7.58/1.50      inference(demodulation,[status(thm)],[c_20098,c_14058]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_26100,plain,
% 7.58/1.50      ( r2_relset_1(sK0,sK0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(sK0)) != iProver_top
% 7.58/1.50      | r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
% 7.58/1.50      inference(demodulation,[status(thm)],[c_26097,c_20101]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_26489,plain,
% 7.58/1.50      ( sK0 = k1_xboole_0
% 7.58/1.50      | r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_11261,c_26100]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_26490,plain,
% 7.58/1.50      ( ~ r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
% 7.58/1.50      | sK0 = k1_xboole_0 ),
% 7.58/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_26489]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_21,plain,
% 7.58/1.50      ( r2_relset_1(X0,X1,X2,X2)
% 7.58/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.58/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 7.58/1.50      inference(cnf_transformation,[],[f90]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_3036,plain,
% 7.58/1.50      ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0))
% 7.58/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
% 7.58/1.50      | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_21]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_33191,plain,
% 7.58/1.50      ( r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
% 7.58/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.58/1.50      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_3036]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_33195,plain,
% 7.58/1.50      ( r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
% 7.58/1.50      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.58/1.50      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_33191]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_1619,plain,
% 7.58/1.50      ( ~ v1_relat_1(X0) | v1_relat_1(X1) | X1 != X0 ),
% 7.58/1.50      theory(equality) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_34458,plain,
% 7.58/1.50      ( ~ v1_relat_1(X0) | v1_relat_1(sK0) | sK0 != X0 ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_1619]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_34459,plain,
% 7.58/1.50      ( sK0 != X0
% 7.58/1.50      | v1_relat_1(X0) != iProver_top
% 7.58/1.50      | v1_relat_1(sK0) = iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_34458]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_34461,plain,
% 7.58/1.50      ( sK0 != k1_xboole_0
% 7.58/1.50      | v1_relat_1(sK0) = iProver_top
% 7.58/1.50      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_34459]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_35995,plain,
% 7.58/1.50      ( v1_relat_1(k1_relat_1(sK1)) != iProver_top
% 7.58/1.50      | v1_funct_1(k2_relat_1(k1_relat_1(sK1))) != iProver_top
% 7.58/1.50      | v5_relat_1(sK0,k1_xboole_0) != iProver_top
% 7.58/1.50      | k1_partfun1(sK0,sK0,X0,k1_xboole_0,sK1,k2_relat_1(k1_relat_1(sK1))) = k5_relat_1(sK1,k2_relat_1(k1_relat_1(sK1))) ),
% 7.58/1.50      inference(global_propositional_subsumption,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_24483,c_2926,c_2928,c_3844,c_9648,c_26490,c_33195,
% 7.58/1.50                 c_34461]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_35996,plain,
% 7.58/1.50      ( k1_partfun1(sK0,sK0,X0,k1_xboole_0,sK1,k2_relat_1(k1_relat_1(sK1))) = k5_relat_1(sK1,k2_relat_1(k1_relat_1(sK1)))
% 7.58/1.50      | v5_relat_1(sK0,k1_xboole_0) != iProver_top
% 7.58/1.50      | v1_funct_1(k2_relat_1(k1_relat_1(sK1))) != iProver_top
% 7.58/1.50      | v1_relat_1(k1_relat_1(sK1)) != iProver_top ),
% 7.58/1.50      inference(renaming,[status(thm)],[c_35995]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_36005,plain,
% 7.58/1.50      ( k1_partfun1(sK0,sK0,X0,k1_xboole_0,sK1,k2_relat_1(k1_relat_1(sK1))) = k5_relat_1(sK1,k2_relat_1(k1_relat_1(sK1)))
% 7.58/1.50      | sK0 = k1_xboole_0
% 7.58/1.50      | v5_relat_1(sK0,k1_xboole_0) != iProver_top
% 7.58/1.50      | v1_funct_1(k2_relat_1(sK0)) != iProver_top
% 7.58/1.50      | v1_relat_1(k1_relat_1(sK1)) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_11261,c_35996]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_36226,plain,
% 7.58/1.50      ( sK0 = k1_xboole_0 ),
% 7.58/1.50      inference(global_propositional_subsumption,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_36005,c_3844,c_9648,c_26490,c_33195]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_36285,plain,
% 7.58/1.50      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_relat_1(sK1)),k6_partfun1(k1_xboole_0)) != iProver_top
% 7.58/1.50      | r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),k6_partfun1(k1_xboole_0)) != iProver_top ),
% 7.58/1.50      inference(demodulation,[status(thm)],[c_36226,c_26100]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_13,plain,
% 7.58/1.50      ( ~ v1_relat_1(X0)
% 7.58/1.50      | k1_relat_1(X0) = k1_xboole_0
% 7.58/1.50      | k2_relat_1(X0) != k1_xboole_0 ),
% 7.58/1.50      inference(cnf_transformation,[],[f83]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_2571,plain,
% 7.58/1.50      ( k1_relat_1(X0) = k1_xboole_0
% 7.58/1.50      | k2_relat_1(X0) != k1_xboole_0
% 7.58/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_4306,plain,
% 7.58/1.50      ( k1_relat_1(sK1) = k1_xboole_0
% 7.58/1.50      | sK0 != k1_xboole_0
% 7.58/1.50      | v1_relat_1(sK1) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_3805,c_2571]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_4307,plain,
% 7.58/1.50      ( ~ v1_relat_1(sK1)
% 7.58/1.50      | k1_relat_1(sK1) = k1_xboole_0
% 7.58/1.50      | sK0 != k1_xboole_0 ),
% 7.58/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_4306]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_4510,plain,
% 7.58/1.50      ( sK0 != k1_xboole_0 | k1_relat_1(sK1) = k1_xboole_0 ),
% 7.58/1.50      inference(global_propositional_subsumption,
% 7.58/1.50                [status(thm)],
% 7.58/1.50                [c_4306,c_44,c_2940,c_4307]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_4511,plain,
% 7.58/1.50      ( k1_relat_1(sK1) = k1_xboole_0 | sK0 != k1_xboole_0 ),
% 7.58/1.50      inference(renaming,[status(thm)],[c_4510]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_36386,plain,
% 7.58/1.50      ( k1_relat_1(sK1) = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 7.58/1.50      inference(demodulation,[status(thm)],[c_36226,c_4511]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_36410,plain,
% 7.58/1.50      ( k1_relat_1(sK1) = k1_xboole_0 ),
% 7.58/1.50      inference(equality_resolution_simp,[status(thm)],[c_36386]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_36767,plain,
% 7.58/1.50      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),k6_partfun1(k1_xboole_0)) != iProver_top ),
% 7.58/1.50      inference(light_normalisation,[status(thm)],[c_36285,c_36410]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_2551,plain,
% 7.58/1.50      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_3190,plain,
% 7.58/1.50      ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_3,c_2551]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_8,plain,
% 7.58/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.58/1.50      inference(cnf_transformation,[],[f76]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_2576,plain,
% 7.58/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.58/1.50      | r1_tarski(X0,X1) = iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_3280,plain,
% 7.58/1.50      ( r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0) = iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_3190,c_2576]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_2578,plain,
% 7.58/1.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_3277,plain,
% 7.58/1.50      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_2578,c_2576]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_0,plain,
% 7.58/1.50      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.58/1.50      inference(cnf_transformation,[],[f71]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_2580,plain,
% 7.58/1.50      ( X0 = X1
% 7.58/1.50      | r1_tarski(X0,X1) != iProver_top
% 7.58/1.50      | r1_tarski(X1,X0) != iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_5093,plain,
% 7.58/1.50      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_3277,c_2580]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_7698,plain,
% 7.58/1.50      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 7.58/1.50      inference(superposition,[status(thm)],[c_3280,c_5093]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_36769,plain,
% 7.58/1.50      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 7.58/1.50      inference(light_normalisation,[status(thm)],[c_36767,c_7698]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_2930,plain,
% 7.58/1.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_2928]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_112,plain,
% 7.58/1.50      ( r2_relset_1(X0,X1,X2,X2) = iProver_top
% 7.58/1.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.58/1.50      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.58/1.50      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(c_114,plain,
% 7.58/1.50      ( r2_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) = iProver_top
% 7.58/1.50      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 7.58/1.50      inference(instantiation,[status(thm)],[c_112]) ).
% 7.58/1.50  
% 7.58/1.50  cnf(contradiction,plain,
% 7.58/1.50      ( $false ),
% 7.58/1.50      inference(minisat,[status(thm)],[c_36769,c_2930,c_114]) ).
% 7.58/1.50  
% 7.58/1.50  
% 7.58/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.58/1.50  
% 7.58/1.50  ------                               Statistics
% 7.58/1.50  
% 7.58/1.50  ------ General
% 7.58/1.50  
% 7.58/1.50  abstr_ref_over_cycles:                  0
% 7.58/1.50  abstr_ref_under_cycles:                 0
% 7.58/1.50  gc_basic_clause_elim:                   0
% 7.58/1.50  forced_gc_time:                         0
% 7.58/1.50  parsing_time:                           0.018
% 7.58/1.50  unif_index_cands_time:                  0.
% 7.58/1.50  unif_index_add_time:                    0.
% 7.58/1.50  orderings_time:                         0.
% 7.58/1.50  out_proof_time:                         0.022
% 7.58/1.50  total_time:                             0.903
% 7.58/1.50  num_of_symbols:                         54
% 7.58/1.50  num_of_terms:                           26323
% 7.58/1.50  
% 7.58/1.50  ------ Preprocessing
% 7.58/1.50  
% 7.58/1.50  num_of_splits:                          0
% 7.58/1.50  num_of_split_atoms:                     0
% 7.58/1.50  num_of_reused_defs:                     0
% 7.58/1.50  num_eq_ax_congr_red:                    27
% 7.58/1.50  num_of_sem_filtered_clauses:            1
% 7.58/1.50  num_of_subtypes:                        0
% 7.58/1.50  monotx_restored_types:                  0
% 7.58/1.50  sat_num_of_epr_types:                   0
% 7.58/1.50  sat_num_of_non_cyclic_types:            0
% 7.58/1.50  sat_guarded_non_collapsed_types:        0
% 7.58/1.50  num_pure_diseq_elim:                    0
% 7.58/1.50  simp_replaced_by:                       0
% 7.58/1.50  res_preprocessed:                       207
% 7.58/1.50  prep_upred:                             0
% 7.58/1.50  prep_unflattend:                        22
% 7.58/1.50  smt_new_axioms:                         0
% 7.58/1.50  pred_elim_cands:                        9
% 7.58/1.50  pred_elim:                              1
% 7.58/1.50  pred_elim_cl:                           2
% 7.58/1.50  pred_elim_cycles:                       5
% 7.58/1.50  merged_defs:                            8
% 7.58/1.50  merged_defs_ncl:                        0
% 7.58/1.50  bin_hyper_res:                          8
% 7.58/1.50  prep_cycles:                            4
% 7.58/1.50  pred_elim_time:                         0.013
% 7.58/1.50  splitting_time:                         0.
% 7.58/1.50  sem_filter_time:                        0.
% 7.58/1.50  monotx_time:                            0.001
% 7.58/1.50  subtype_inf_time:                       0.
% 7.58/1.50  
% 7.58/1.50  ------ Problem properties
% 7.58/1.50  
% 7.58/1.50  clauses:                                43
% 7.58/1.50  conjectures:                            5
% 7.58/1.50  epr:                                    5
% 7.58/1.50  horn:                                   38
% 7.58/1.50  ground:                                 5
% 7.58/1.50  unary:                                  10
% 7.58/1.50  binary:                                 7
% 7.58/1.50  lits:                                   122
% 7.58/1.50  lits_eq:                                25
% 7.58/1.50  fd_pure:                                0
% 7.58/1.50  fd_pseudo:                              0
% 7.58/1.50  fd_cond:                                4
% 7.58/1.50  fd_pseudo_cond:                         2
% 7.58/1.50  ac_symbols:                             0
% 7.58/1.50  
% 7.58/1.50  ------ Propositional Solver
% 7.58/1.50  
% 7.58/1.50  prop_solver_calls:                      29
% 7.58/1.50  prop_fast_solver_calls:                 2423
% 7.58/1.50  smt_solver_calls:                       0
% 7.58/1.50  smt_fast_solver_calls:                  0
% 7.58/1.50  prop_num_of_clauses:                    11931
% 7.58/1.50  prop_preprocess_simplified:             24586
% 7.58/1.50  prop_fo_subsumed:                       119
% 7.58/1.50  prop_solver_time:                       0.
% 7.58/1.50  smt_solver_time:                        0.
% 7.58/1.50  smt_fast_solver_time:                   0.
% 7.58/1.50  prop_fast_solver_time:                  0.
% 7.58/1.50  prop_unsat_core_time:                   0.001
% 7.58/1.50  
% 7.58/1.50  ------ QBF
% 7.58/1.50  
% 7.58/1.50  qbf_q_res:                              0
% 7.58/1.50  qbf_num_tautologies:                    0
% 7.58/1.50  qbf_prep_cycles:                        0
% 7.58/1.50  
% 7.58/1.50  ------ BMC1
% 7.58/1.50  
% 7.58/1.50  bmc1_current_bound:                     -1
% 7.58/1.50  bmc1_last_solved_bound:                 -1
% 7.58/1.50  bmc1_unsat_core_size:                   -1
% 7.58/1.50  bmc1_unsat_core_parents_size:           -1
% 7.58/1.50  bmc1_merge_next_fun:                    0
% 7.58/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.58/1.50  
% 7.58/1.50  ------ Instantiation
% 7.58/1.50  
% 7.58/1.50  inst_num_of_clauses:                    3295
% 7.58/1.50  inst_num_in_passive:                    583
% 7.58/1.50  inst_num_in_active:                     1387
% 7.58/1.50  inst_num_in_unprocessed:                1328
% 7.58/1.50  inst_num_of_loops:                      1620
% 7.58/1.50  inst_num_of_learning_restarts:          0
% 7.58/1.50  inst_num_moves_active_passive:          230
% 7.58/1.50  inst_lit_activity:                      0
% 7.58/1.50  inst_lit_activity_moves:                0
% 7.58/1.50  inst_num_tautologies:                   0
% 7.58/1.50  inst_num_prop_implied:                  0
% 7.58/1.50  inst_num_existing_simplified:           0
% 7.58/1.50  inst_num_eq_res_simplified:             0
% 7.58/1.50  inst_num_child_elim:                    0
% 7.58/1.50  inst_num_of_dismatching_blockings:      2176
% 7.58/1.50  inst_num_of_non_proper_insts:           4050
% 7.58/1.50  inst_num_of_duplicates:                 0
% 7.58/1.50  inst_inst_num_from_inst_to_res:         0
% 7.58/1.50  inst_dismatching_checking_time:         0.
% 7.58/1.50  
% 7.58/1.50  ------ Resolution
% 7.58/1.50  
% 7.58/1.50  res_num_of_clauses:                     0
% 7.58/1.50  res_num_in_passive:                     0
% 7.58/1.50  res_num_in_active:                      0
% 7.58/1.50  res_num_of_loops:                       211
% 7.58/1.50  res_forward_subset_subsumed:            185
% 7.58/1.50  res_backward_subset_subsumed:           30
% 7.58/1.50  res_forward_subsumed:                   0
% 7.58/1.50  res_backward_subsumed:                  0
% 7.58/1.50  res_forward_subsumption_resolution:     1
% 7.58/1.50  res_backward_subsumption_resolution:    0
% 7.58/1.50  res_clause_to_clause_subsumption:       3575
% 7.58/1.50  res_orphan_elimination:                 0
% 7.58/1.50  res_tautology_del:                      191
% 7.58/1.50  res_num_eq_res_simplified:              0
% 7.58/1.50  res_num_sel_changes:                    0
% 7.58/1.50  res_moves_from_active_to_pass:          0
% 7.58/1.50  
% 7.58/1.50  ------ Superposition
% 7.58/1.50  
% 7.58/1.50  sup_time_total:                         0.
% 7.58/1.50  sup_time_generating:                    0.
% 7.58/1.50  sup_time_sim_full:                      0.
% 7.58/1.50  sup_time_sim_immed:                     0.
% 7.58/1.50  
% 7.58/1.50  sup_num_of_clauses:                     522
% 7.58/1.50  sup_num_in_active:                      124
% 7.58/1.50  sup_num_in_passive:                     398
% 7.58/1.50  sup_num_of_loops:                       322
% 7.58/1.50  sup_fw_superposition:                   737
% 7.58/1.50  sup_bw_superposition:                   300
% 7.58/1.50  sup_immediate_simplified:               437
% 7.58/1.50  sup_given_eliminated:                   0
% 7.58/1.50  comparisons_done:                       0
% 7.58/1.50  comparisons_avoided:                    3
% 7.58/1.50  
% 7.58/1.50  ------ Simplifications
% 7.58/1.50  
% 7.58/1.50  
% 7.58/1.50  sim_fw_subset_subsumed:                 45
% 7.58/1.50  sim_bw_subset_subsumed:                 31
% 7.58/1.50  sim_fw_subsumed:                        137
% 7.58/1.50  sim_bw_subsumed:                        3
% 7.58/1.50  sim_fw_subsumption_res:                 10
% 7.58/1.50  sim_bw_subsumption_res:                 0
% 7.58/1.50  sim_tautology_del:                      12
% 7.58/1.50  sim_eq_tautology_del:                   61
% 7.58/1.50  sim_eq_res_simp:                        3
% 7.58/1.50  sim_fw_demodulated:                     171
% 7.58/1.50  sim_bw_demodulated:                     194
% 7.58/1.50  sim_light_normalised:                   238
% 7.58/1.50  sim_joinable_taut:                      0
% 7.58/1.50  sim_joinable_simp:                      0
% 7.58/1.50  sim_ac_normalised:                      0
% 7.58/1.50  sim_smt_subsumption:                    0
% 7.58/1.50  
%------------------------------------------------------------------------------
