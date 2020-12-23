%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:54 EST 2020

% Result     : Theorem 39.30s
% Output     : CNFRefutation 39.30s
% Verified   : 
% Statistics : Number of formulae       :  400 (11667 expanded)
%              Number of clauses        :  321 (4417 expanded)
%              Number of leaves         :   24 (2062 expanded)
%              Depth                    :   38
%              Number of atoms          : 1116 (51743 expanded)
%              Number of equality atoms :  735 (15891 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

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
    inference(ennf_transformation,[],[f14])).

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

fof(f46,plain,(
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

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f17,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X2,X0)
       => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
            & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
            & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X2,X0)
         => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
              & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
              & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f40,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f41,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f40])).

fof(f47,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
          | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
          | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
        | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_tarski(sK2,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f41,f47])).

fof(f76,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f77,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f48])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f42])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f82,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f52])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f81,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f53])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f50,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f75,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f80,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f48])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f78,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f85,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f70])).

fof(f79,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f48])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_14,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_8,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_387,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_14,c_8])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_391,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_387,c_13])).

cnf(c_392,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_391])).

cnf(c_99025,plain,
    ( ~ m1_subset_1(k7_relat_1(X0,sK2),k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | r1_tarski(k2_relat_1(k7_relat_1(X0,sK2)),sK1) ),
    inference(instantiation,[status(thm)],[c_392])).

cnf(c_131908,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) ),
    inference(instantiation,[status(thm)],[c_99025])).

cnf(c_181552,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) ),
    inference(instantiation,[status(thm)],[c_131908])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_510,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X0
    | sK1 != X2
    | sK0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_30])).

cnf(c_511,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_510])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_513,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_511,c_29])).

cnf(c_1398,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1404,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3038,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1398,c_1404])).

cnf(c_3350,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_513,c_3038])).

cnf(c_1396,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_392])).

cnf(c_1810,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1398,c_1396])).

cnf(c_3,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_16,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1403,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4554,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_1403])).

cnf(c_6252,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1810,c_4554])).

cnf(c_34,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_1634,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1635,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1634])).

cnf(c_6272,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6252,c_34,c_1635])).

cnf(c_6273,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6272])).

cnf(c_6278,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3350,c_6273])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1402,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3678,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(k2_partfun1(X1,X2,X0,X3)),X2) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1402,c_1396])).

cnf(c_5,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1411,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1405,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2442,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_1405])).

cnf(c_2565,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1411,c_2442])).

cnf(c_15603,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(k2_relat_1(k2_partfun1(X1,k1_xboole_0,X0,X2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3678,c_2565])).

cnf(c_15813,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(k2_relat_1(k2_partfun1(X1,k1_xboole_0,X0,X2))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_15603,c_2])).

cnf(c_2441,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1398,c_1405])).

cnf(c_10,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1408,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2419,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1411,c_1396])).

cnf(c_5597,plain,
    ( r1_tarski(k2_relat_1(k1_relat_1(k7_relat_1(X0,k2_zfmisc_1(X1,X2)))),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1408,c_2419])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1412,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2866,plain,
    ( k1_relat_1(k7_relat_1(X0,k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1408,c_1412])).

cnf(c_3432,plain,
    ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2441,c_2866])).

cnf(c_4553,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_1403])).

cnf(c_5967,plain,
    ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_xboole_0)),k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3432,c_4553])).

cnf(c_1720,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X0)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1721,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1720])).

cnf(c_1723,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,k1_xboole_0)),k1_xboole_0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1721])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1717,plain,
    ( v1_relat_1(k7_relat_1(sK3,X0))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1733,plain,
    ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1717])).

cnf(c_1735,plain,
    ( v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1733])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1400,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2301,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1398,c_1400])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1685,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_1843,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_1685])).

cnf(c_2646,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2301,c_31,c_29,c_1843])).

cnf(c_3672,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2646,c_1402])).

cnf(c_32,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_4360,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3672,c_32,c_34])).

cnf(c_4370,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_4360,c_1396])).

cnf(c_6254,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),k1_xboole_0) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4370,c_4554])).

cnf(c_6269,plain,
    ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,k1_xboole_0)),k1_xboole_0) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6254])).

cnf(c_13150,plain,
    ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5967,c_34,c_1635,c_1723,c_1735,c_6269])).

cnf(c_1898,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k2_relat_1(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_1396])).

cnf(c_13156,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_xboole_0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_13150,c_1898])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1410,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_13155,plain,
    ( r1_tarski(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_13150,c_1410])).

cnf(c_13385,plain,
    ( k7_relat_1(sK3,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_13155,c_1412])).

cnf(c_13544,plain,
    ( r1_tarski(k2_relat_1(k1_xboole_0),X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13156,c_13385])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1413,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_13551,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k2_relat_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13544,c_1413])).

cnf(c_14737,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,k2_relat_1(k1_xboole_0))),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1408,c_13551])).

cnf(c_21382,plain,
    ( k1_relat_1(k7_relat_1(X0,k2_relat_1(k1_xboole_0))) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_14737,c_1412])).

cnf(c_21630,plain,
    ( k1_relat_1(k7_relat_1(sK3,k2_relat_1(k1_xboole_0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2441,c_21382])).

cnf(c_22060,plain,
    ( r1_tarski(k1_xboole_0,k2_relat_1(k1_xboole_0)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_21630,c_1408])).

cnf(c_22612,plain,
    ( r1_tarski(k1_xboole_0,k2_relat_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_22060,c_34,c_1635])).

cnf(c_22619,plain,
    ( r1_tarski(X0,k2_relat_1(k1_xboole_0)) = iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_22612,c_1413])).

cnf(c_23376,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k2_relat_1(k1_xboole_0)) = iProver_top
    | r1_tarski(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_22619,c_1413])).

cnf(c_67613,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k2_relat_1(k1_xboole_0)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1408,c_23376])).

cnf(c_3614,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3432,c_1408])).

cnf(c_3617,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3614,c_34,c_1635])).

cnf(c_1813,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_1396])).

cnf(c_2884,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1411,c_1813])).

cnf(c_7058,plain,
    ( k2_relat_1(X0) = k1_xboole_0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2884,c_1412])).

cnf(c_7816,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3617,c_7058])).

cnf(c_118925,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_xboole_0) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_67613,c_7816])).

cnf(c_118953,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = k1_xboole_0
    | r1_tarski(X1,k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_118925,c_1412])).

cnf(c_120866,plain,
    ( k1_relat_1(k7_relat_1(X0,k2_relat_1(k1_relat_1(k7_relat_1(X1,k2_zfmisc_1(X2,k1_xboole_0)))))) = k1_xboole_0
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5597,c_118953])).

cnf(c_120978,plain,
    ( k1_relat_1(k7_relat_1(X0,k2_relat_1(k1_relat_1(k7_relat_1(X1,k1_xboole_0))))) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_120866,c_2])).

cnf(c_121238,plain,
    ( k1_relat_1(k7_relat_1(sK3,k2_relat_1(k1_relat_1(k7_relat_1(X0,k1_xboole_0))))) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2441,c_120978])).

cnf(c_121375,plain,
    ( k1_relat_1(k7_relat_1(sK3,k2_relat_1(k1_relat_1(k7_relat_1(k2_relat_1(k2_partfun1(X0,k1_xboole_0,X1,X2)),k1_xboole_0))))) = k1_xboole_0
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_15813,c_121238])).

cnf(c_127619,plain,
    ( k1_relat_1(k7_relat_1(sK3,k2_relat_1(k1_relat_1(k7_relat_1(k2_relat_1(k2_partfun1(X0,k1_xboole_0,sK3,X1)),k1_xboole_0))))) = k1_xboole_0
    | sK1 = k1_xboole_0
    | r1_tarski(sK0,k1_xboole_0) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6278,c_121375])).

cnf(c_98,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_100,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_101,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_26,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_521,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != sK3
    | sK2 != sK0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_30])).

cnf(c_802,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1653,plain,
    ( sK2 != X0
    | sK2 = sK0
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_802])).

cnf(c_1654,plain,
    ( sK2 = sK0
    | sK2 != k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1653])).

cnf(c_1761,plain,
    ( ~ r1_tarski(sK3,k1_xboole_0)
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1764,plain,
    ( k1_xboole_0 = sK3
    | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1761])).

cnf(c_801,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1801,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_801])).

cnf(c_1921,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_801])).

cnf(c_1652,plain,
    ( sK0 != X0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_802])).

cnf(c_1927,plain,
    ( sK0 != sK0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1652])).

cnf(c_1928,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_801])).

cnf(c_2017,plain,
    ( ~ r1_tarski(sK0,k1_xboole_0)
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2020,plain,
    ( k1_xboole_0 = sK0
    | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2017])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1665,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(k2_partfun1(X0,X1,sK3,X2))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_1838,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1665])).

cnf(c_2149,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1838])).

cnf(c_3615,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3614])).

cnf(c_2077,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_802])).

cnf(c_4804,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2077])).

cnf(c_4805,plain,
    ( sK3 != sK3
    | sK3 = k1_xboole_0
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_4804])).

cnf(c_13248,plain,
    ( k2_zfmisc_1(sK2,sK1) = k2_zfmisc_1(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_801])).

cnf(c_806,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2268,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | X0 != X2
    | X1 != k1_zfmisc_1(X3) ),
    inference(instantiation,[status(thm)],[c_806])).

cnf(c_9958,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(X2,k1_zfmisc_1(X1))
    | X2 != X0
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_2268])).

cnf(c_16035,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_9958])).

cnf(c_16037,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_16035])).

cnf(c_22081,plain,
    ( r1_tarski(k1_xboole_0,k2_relat_1(k1_xboole_0))
    | ~ v1_relat_1(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_22060])).

cnf(c_805,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_27774,plain,
    ( k2_zfmisc_1(sK2,sK1) != k2_zfmisc_1(sK2,sK1)
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) = k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_805])).

cnf(c_28350,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(sK0,sK1,sK3,sK2) = k7_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_1843])).

cnf(c_35150,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(sK2,sK1))))
    | r1_tarski(k2_relat_1(X0),k2_zfmisc_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_392])).

cnf(c_35156,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_zfmisc_1(sK2,sK1))))
    | r1_tarski(k2_relat_1(k1_xboole_0),k2_zfmisc_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_35150])).

cnf(c_2263,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_72304,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(X0,k2_zfmisc_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_2263])).

cnf(c_72311,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_72304])).

cnf(c_73922,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),k1_xboole_0) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6254,c_34,c_1635,c_1733])).

cnf(c_73923,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_73922])).

cnf(c_73933,plain,
    ( m1_subset_1(k7_relat_1(sK3,k2_relat_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_21630,c_73923])).

cnf(c_73930,plain,
    ( m1_subset_1(k7_relat_1(sK3,k2_relat_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_14737,c_73923])).

cnf(c_75133,plain,
    ( m1_subset_1(k7_relat_1(sK3,k2_relat_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_73933,c_34,c_1635,c_73930])).

cnf(c_75138,plain,
    ( r1_tarski(k7_relat_1(sK3,k2_relat_1(k1_xboole_0)),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_75133,c_1410])).

cnf(c_76883,plain,
    ( k7_relat_1(sK3,k2_relat_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_75138,c_1412])).

cnf(c_28,negated_conjecture,
    ( r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1399,plain,
    ( r1_tarski(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_67615,plain,
    ( r1_tarski(sK2,k2_relat_1(k1_xboole_0)) = iProver_top
    | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1399,c_23376])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1406,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_13556,plain,
    ( k1_relat_1(k7_relat_1(X0,k2_relat_1(k1_xboole_0))) = k2_relat_1(k1_xboole_0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_13544,c_1406])).

cnf(c_14761,plain,
    ( k1_relat_1(k7_relat_1(sK3,k2_relat_1(k1_xboole_0))) = k2_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2441,c_13556])).

cnf(c_14871,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,k2_relat_1(k1_xboole_0)),X0)) = X0
    | r1_tarski(X0,k2_relat_1(k1_xboole_0)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,k2_relat_1(k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_14761,c_1406])).

cnf(c_4369,plain,
    ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4360,c_1405])).

cnf(c_15005,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,k2_relat_1(k1_xboole_0)),X0)) = X0
    | r1_tarski(X0,k2_relat_1(k1_xboole_0)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_14871,c_4369])).

cnf(c_68369,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,k2_relat_1(k1_xboole_0)),sK2)) = sK2
    | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_67615,c_15005])).

cnf(c_76937,plain,
    ( k1_relat_1(k7_relat_1(k1_xboole_0,sK2)) = sK2
    | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_76883,c_68369])).

cnf(c_3622,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3617,c_2565])).

cnf(c_11,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1407,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2210,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1407,c_1412])).

cnf(c_3641,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3622,c_2210])).

cnf(c_3640,plain,
    ( k1_relat_1(k7_relat_1(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3622,c_2866])).

cnf(c_3644,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3640,c_3641])).

cnf(c_76999,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_76937,c_3641,c_3644])).

cnf(c_88262,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | X0 != X2
    | X1 != k1_zfmisc_1(X3) ),
    inference(instantiation,[status(thm)],[c_806])).

cnf(c_88836,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(X2,k1_zfmisc_1(X3))
    | X2 != X0
    | k1_zfmisc_1(X3) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_88262])).

cnf(c_91181,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,k2_zfmisc_1(sK2,sK1))))
    | X2 != X0
    | k1_zfmisc_1(k2_zfmisc_1(X3,k2_zfmisc_1(sK2,sK1))) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_88836])).

cnf(c_91183,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_zfmisc_1(sK2,sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_zfmisc_1(sK2,sK1))) != k1_zfmisc_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_91181])).

cnf(c_89320,plain,
    ( X0 != X1
    | k2_partfun1(sK0,sK1,sK3,sK2) != X1
    | k2_partfun1(sK0,sK1,sK3,sK2) = X0 ),
    inference(instantiation,[status(thm)],[c_802])).

cnf(c_91302,plain,
    ( X0 != k7_relat_1(sK3,sK2)
    | k2_partfun1(sK0,sK1,sK3,sK2) = X0
    | k2_partfun1(sK0,sK1,sK3,sK2) != k7_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_89320])).

cnf(c_91303,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k7_relat_1(sK3,sK2)
    | k2_partfun1(sK0,sK1,sK3,sK2) = k1_xboole_0
    | k1_xboole_0 != k7_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_91302])).

cnf(c_94719,plain,
    ( ~ r1_tarski(k7_relat_1(sK3,sK2),k1_xboole_0)
    | k1_xboole_0 = k7_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_94720,plain,
    ( k1_xboole_0 = k7_relat_1(sK3,sK2)
    | r1_tarski(k7_relat_1(sK3,sK2),k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_94719])).

cnf(c_95587,plain,
    ( k2_zfmisc_1(X0,k2_zfmisc_1(sK2,sK1)) != X1
    | k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(sK2,sK1))) = k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_805])).

cnf(c_95588,plain,
    ( k2_zfmisc_1(k1_xboole_0,k2_zfmisc_1(sK2,sK1)) != k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_zfmisc_1(sK2,sK1))) = k1_zfmisc_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_95587])).

cnf(c_2330,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1398,c_1410])).

cnf(c_68365,plain,
    ( r1_tarski(X0,k2_relat_1(k1_xboole_0)) = iProver_top
    | r1_tarski(X0,sK2) != iProver_top
    | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_67615,c_1413])).

cnf(c_69336,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k2_relat_1(k1_xboole_0)) = iProver_top
    | r1_tarski(X1,sK2) != iProver_top
    | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_68365,c_1413])).

cnf(c_75538,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),sK2) != iProver_top
    | r1_tarski(sK3,k2_relat_1(k1_xboole_0)) = iProver_top
    | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2330,c_69336])).

cnf(c_102872,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),sK2) != iProver_top
    | r1_tarski(sK3,k1_xboole_0) = iProver_top
    | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7816,c_75538])).

cnf(c_6317,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(sK3,k1_xboole_0) = iProver_top
    | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6278,c_1410])).

cnf(c_803,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_9451,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK1,k1_xboole_0)
    | sK1 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_803])).

cnf(c_9452,plain,
    ( sK1 != X0
    | k1_xboole_0 != X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(sK1,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9451])).

cnf(c_9454,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK1,k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_9452])).

cnf(c_67620,plain,
    ( r1_tarski(k2_relat_1(sK3),k2_relat_1(k1_xboole_0)) = iProver_top
    | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1810,c_23376])).

cnf(c_68826,plain,
    ( r1_tarski(k2_relat_1(sK3),X0) = iProver_top
    | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_67620,c_13551])).

cnf(c_4555,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) = iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1403,c_1410])).

cnf(c_25363,plain,
    ( r1_tarski(X0,k1_xboole_0) = iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_4555])).

cnf(c_25476,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top
    | r1_tarski(sK3,k1_xboole_0) = iProver_top
    | r1_tarski(sK0,X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3350,c_25363])).

cnf(c_27633,plain,
    ( r1_tarski(sK0,X0) != iProver_top
    | r1_tarski(sK3,k1_xboole_0) = iProver_top
    | r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_25476,c_34,c_1635])).

cnf(c_27634,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top
    | r1_tarski(sK3,k1_xboole_0) = iProver_top
    | r1_tarski(sK0,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_27633])).

cnf(c_69856,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(sK3,k1_xboole_0) = iProver_top
    | r1_tarski(sK1,k1_xboole_0) != iProver_top
    | r1_tarski(sK0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_68826,c_27634])).

cnf(c_1627,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1628,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1627])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_442,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK3 != X0
    | sK1 != k1_xboole_0
    | sK0 != X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_30])).

cnf(c_443,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0 ),
    inference(unflattening,[status(thm)],[c_442])).

cnf(c_1394,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_443])).

cnf(c_1493,plain,
    ( sK3 = k1_xboole_0
    | sK1 != k1_xboole_0
    | sK0 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1394,c_2])).

cnf(c_27,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2031,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_802])).

cnf(c_2032,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2031])).

cnf(c_2069,plain,
    ( sK0 = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1493,c_27,c_100,c_101,c_1927,c_1928,c_2032])).

cnf(c_2070,plain,
    ( sK1 != k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_2069])).

cnf(c_1705,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))
    | X1 != k2_zfmisc_1(sK0,sK1)
    | X0 != sK3 ),
    inference(instantiation,[status(thm)],[c_803])).

cnf(c_2100,plain,
    ( r1_tarski(sK3,X0)
    | ~ r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))
    | X0 != k2_zfmisc_1(sK0,sK1)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1705])).

cnf(c_2101,plain,
    ( X0 != k2_zfmisc_1(sK0,sK1)
    | sK3 != sK3
    | r1_tarski(sK3,X0) = iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2100])).

cnf(c_2103,plain,
    ( sK3 != sK3
    | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    | r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) != iProver_top
    | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2101])).

cnf(c_2897,plain,
    ( X0 != X1
    | X0 = k2_zfmisc_1(sK0,sK1)
    | k2_zfmisc_1(sK0,sK1) != X1 ),
    inference(instantiation,[status(thm)],[c_802])).

cnf(c_2898,plain,
    ( k2_zfmisc_1(sK0,sK1) != k1_xboole_0
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2897])).

cnf(c_804,plain,
    ( X0 != X1
    | X2 != X3
    | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
    theory(equality)).

cnf(c_10843,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(X0,X1)
    | sK1 != X1
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_804])).

cnf(c_10845,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | sK1 != k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_10843])).

cnf(c_11613,plain,
    ( k2_zfmisc_1(X0,X1) != X2
    | k1_xboole_0 != X2
    | k1_xboole_0 = k2_zfmisc_1(X0,X1) ),
    inference(instantiation,[status(thm)],[c_802])).

cnf(c_11614,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_11613])).

cnf(c_3899,plain,
    ( r1_tarski(X0,k2_zfmisc_1(sK0,sK1)) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2330,c_1413])).

cnf(c_4559,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | r1_tarski(k1_relat_1(X2),X0) != iProver_top
    | r1_tarski(k2_relat_1(X2),X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1403,c_1404])).

cnf(c_29866,plain,
    ( k1_relset_1(k2_zfmisc_1(sK0,sK1),X0,X1) = k1_relat_1(X1)
    | r1_tarski(k1_relat_1(X1),sK3) != iProver_top
    | r1_tarski(k2_relat_1(X1),X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3899,c_4559])).

cnf(c_68824,plain,
    ( k1_relset_1(k2_zfmisc_1(sK0,sK1),k2_relat_1(k1_xboole_0),sK3) = k1_relat_1(sK3)
    | r1_tarski(k1_relat_1(sK3),sK3) != iProver_top
    | r1_tarski(sK1,k1_xboole_0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_67620,c_29866])).

cnf(c_79449,plain,
    ( r1_tarski(sK1,k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(sK3),sK3) != iProver_top
    | k1_relset_1(k2_zfmisc_1(sK0,sK1),k2_relat_1(k1_xboole_0),sK3) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_68824,c_34,c_1635])).

cnf(c_79450,plain,
    ( k1_relset_1(k2_zfmisc_1(sK0,sK1),k2_relat_1(k1_xboole_0),sK3) = k1_relat_1(sK3)
    | r1_tarski(k1_relat_1(sK3),sK3) != iProver_top
    | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_79449])).

cnf(c_79456,plain,
    ( k1_relset_1(k2_zfmisc_1(sK0,sK1),k2_relat_1(k1_xboole_0),sK3) = k1_relat_1(sK3)
    | sK1 = k1_xboole_0
    | r1_tarski(sK1,k1_xboole_0) != iProver_top
    | r1_tarski(sK0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3350,c_79450])).

cnf(c_1650,plain,
    ( sK1 != X0
    | sK1 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_802])).

cnf(c_1920,plain,
    ( sK1 != sK1
    | sK1 = k1_xboole_0
    | k1_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_1650])).

cnf(c_2028,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2029,plain,
    ( k1_xboole_0 = sK1
    | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2028])).

cnf(c_79698,plain,
    ( r1_tarski(sK1,k1_xboole_0) != iProver_top
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_79456,c_1920,c_1921,c_2029])).

cnf(c_79699,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_79698])).

cnf(c_91585,plain,
    ( k2_zfmisc_1(sK0,sK1) != X0
    | k2_zfmisc_1(sK0,sK1) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_802])).

cnf(c_91922,plain,
    ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X0,X1)
    | k2_zfmisc_1(sK0,sK1) = k1_xboole_0
    | k1_xboole_0 != k2_zfmisc_1(X0,X1) ),
    inference(instantiation,[status(thm)],[c_91585])).

cnf(c_91924,plain,
    ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | k2_zfmisc_1(sK0,sK1) = k1_xboole_0
    | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_91922])).

cnf(c_92262,plain,
    ( r1_tarski(sK1,k1_xboole_0) != iProver_top
    | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_69856,c_34,c_100,c_101,c_1628,c_1801,c_2070,c_2103,c_2898,c_10845,c_11614,c_79699,c_91924])).

cnf(c_92263,plain,
    ( r1_tarski(sK3,k1_xboole_0) = iProver_top
    | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_92262])).

cnf(c_104774,plain,
    ( r1_tarski(sK3,k1_xboole_0) = iProver_top
    | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_102872,c_34,c_100,c_101,c_1635,c_3614,c_6317,c_9454,c_92263])).

cnf(c_114471,plain,
    ( k2_zfmisc_1(k1_xboole_0,k2_zfmisc_1(sK2,sK1)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_89270,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,k2_zfmisc_1(sK2,sK1))
    | r1_tarski(X0,k2_zfmisc_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_124225,plain,
    ( r1_tarski(X0,k2_zfmisc_1(sK2,sK1))
    | ~ r1_tarski(X0,k2_relat_1(X1))
    | ~ r1_tarski(k2_relat_1(X1),k2_zfmisc_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_89270])).

cnf(c_124227,plain,
    ( ~ r1_tarski(k2_relat_1(k1_xboole_0),k2_zfmisc_1(sK2,sK1))
    | r1_tarski(k1_xboole_0,k2_zfmisc_1(sK2,sK1))
    | ~ r1_tarski(k1_xboole_0,k2_relat_1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_124225])).

cnf(c_4008,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3350,c_1406])).

cnf(c_4406,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | sK1 = k1_xboole_0
    | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4008,c_34,c_1635])).

cnf(c_4407,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4406])).

cnf(c_4415,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1399,c_4407])).

cnf(c_4527,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(sK2,sK2) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4415,c_1408])).

cnf(c_5032,plain,
    ( r1_tarski(sK2,sK2) = iProver_top
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4527,c_34,c_1635])).

cnf(c_5033,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(sK2,sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_5032])).

cnf(c_3897,plain,
    ( r1_tarski(X0,sK2) != iProver_top
    | r1_tarski(X0,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1399,c_1413])).

cnf(c_4049,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,sK2)),sK0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1408,c_3897])).

cnf(c_4416,plain,
    ( k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(X0,sK2)))) = k1_relat_1(k7_relat_1(X0,sK2))
    | sK1 = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4049,c_4407])).

cnf(c_18662,plain,
    ( k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,sK2)))) = k1_relat_1(k7_relat_1(sK3,sK2))
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2441,c_4416])).

cnf(c_29879,plain,
    ( k1_relset_1(X0,X1,k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,sK2)))) = k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,sK2))))
    | sK1 = k1_xboole_0
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,sK2)))),X1) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_18662,c_4559])).

cnf(c_119902,plain,
    ( k1_relset_1(X0,X1,k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,sK2)))) = k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,sK2))))
    | sK1 = k1_xboole_0
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,sK2)))),X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_29879,c_4369])).

cnf(c_119920,plain,
    ( k1_relset_1(X0,X1,k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,sK2)))) = k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,sK2))))
    | sK1 = k1_xboole_0
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4415,c_119902])).

cnf(c_120087,plain,
    ( k1_relset_1(X0,X1,k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,sK2)))) = k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,sK2))))
    | sK1 = k1_xboole_0
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4415,c_119920])).

cnf(c_120248,plain,
    ( k1_relset_1(X0,sK1,k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,sK2)))) = k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,sK2))))
    | sK1 = k1_xboole_0
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4370,c_120087])).

cnf(c_120418,plain,
    ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,sK2)))) = k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,sK2))))
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5033,c_120248])).

cnf(c_120488,plain,
    ( k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,sK2)))) = k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2))
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4415,c_120418])).

cnf(c_121552,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)),k1_relat_1(k7_relat_1(sK3,sK2))) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_120488,c_1408])).

cnf(c_131007,plain,
    ( r1_tarski(k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)),k1_relat_1(k7_relat_1(sK3,sK2))) = iProver_top
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_121552,c_34,c_1635])).

cnf(c_131008,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)),k1_relat_1(k7_relat_1(sK3,sK2))) = iProver_top ),
    inference(renaming,[status(thm)],[c_131007])).

cnf(c_131014,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4415,c_131008])).

cnf(c_69358,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,sK2) != iProver_top
    | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_68365,c_13551])).

cnf(c_131142,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)),X0) = iProver_top
    | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_131014,c_69358])).

cnf(c_121570,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,sK2))),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_120488,c_73923])).

cnf(c_138743,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4415,c_121570])).

cnf(c_9446,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK0,k1_xboole_0)
    | sK0 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_803])).

cnf(c_9447,plain,
    ( sK0 != X0
    | k1_xboole_0 != X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(sK0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9446])).

cnf(c_9449,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_9447])).

cnf(c_71102,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,sK2)),X1) = iProver_top
    | r1_tarski(sK0,k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1408,c_69358])).

cnf(c_98360,plain,
    ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(sK0,k1_xboole_0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_71102,c_73923])).

cnf(c_139127,plain,
    ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)),k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_138743,c_34,c_100,c_101,c_1635,c_2070,c_3614,c_9449,c_98360])).

cnf(c_139133,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_131142,c_139127])).

cnf(c_139447,plain,
    ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_139133,c_34,c_1635,c_98360])).

cnf(c_139453,plain,
    ( r1_tarski(k7_relat_1(sK3,sK2),k1_xboole_0) = iProver_top
    | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_139447,c_1410])).

cnf(c_97745,plain,
    ( X0 != X1
    | X0 = sK3
    | sK3 != X1 ),
    inference(instantiation,[status(thm)],[c_802])).

cnf(c_151200,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k2_partfun1(sK0,sK1,sK3,sK2) = sK3
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_97745])).

cnf(c_151201,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) = sK3
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_151200])).

cnf(c_151218,plain,
    ( r1_tarski(sK0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_127619,c_31,c_29,c_98,c_100,c_101,c_521,c_1634,c_1654,c_1764,c_1801,c_1921,c_1927,c_1928,c_2020,c_2149,c_3615,c_4805,c_13248,c_16037,c_22081,c_27774,c_28350,c_35156,c_72311,c_76999,c_91183,c_91303,c_94720,c_95588,c_104774,c_114471,c_124227,c_139453,c_151201])).

cnf(c_121572,plain,
    ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_120488,c_18662])).

cnf(c_20,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_494,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_relset_1(X1,X2,X0) != X1
    | sK2 != X1
    | sK1 != X2
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_26])).

cnf(c_495,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_494])).

cnf(c_1391,plain,
    ( k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | k1_xboole_0 = sK1
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_495])).

cnf(c_2653,plain,
    ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) != sK2
    | sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2646,c_1391])).

cnf(c_129514,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_121572,c_2653])).

cnf(c_129517,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_129514,c_4415])).

cnf(c_1401,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2801,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1398,c_1401])).

cnf(c_2818,plain,
    ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2801,c_2646])).

cnf(c_3421,plain,
    ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2818,c_32])).

cnf(c_129524,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_129517,c_3421])).

cnf(c_129527,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) != iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1403,c_129524])).

cnf(c_129541,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)
    | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1)
    | ~ v1_relat_1(k7_relat_1(sK3,sK2))
    | sK1 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_129527])).

cnf(c_92924,plain,
    ( k7_relat_1(sK3,sK2) = k7_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_801])).

cnf(c_85417,plain,
    ( v1_relat_1(k7_relat_1(sK3,sK2))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1717])).

cnf(c_1680,plain,
    ( m1_subset_1(k2_partfun1(X0,X1,sK3,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_1848,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1680])).

cnf(c_85088,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1848])).

cnf(c_2528,plain,
    ( X0 != X1
    | X0 = k2_partfun1(sK0,sK1,sK3,X2)
    | k2_partfun1(sK0,sK1,sK3,X2) != X1 ),
    inference(instantiation,[status(thm)],[c_802])).

cnf(c_5319,plain,
    ( X0 = k2_partfun1(sK0,sK1,sK3,X1)
    | X0 != k7_relat_1(sK3,X1)
    | k2_partfun1(sK0,sK1,sK3,X1) != k7_relat_1(sK3,X1) ),
    inference(instantiation,[status(thm)],[c_2528])).

cnf(c_6739,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) != k7_relat_1(sK3,X0)
    | k7_relat_1(sK3,X0) = k2_partfun1(sK0,sK1,sK3,X0)
    | k7_relat_1(sK3,X0) != k7_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_5319])).

cnf(c_54988,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k7_relat_1(sK3,sK2)
    | k7_relat_1(sK3,sK2) = k2_partfun1(sK0,sK1,sK3,sK2)
    | k7_relat_1(sK3,sK2) != k7_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_6739])).

cnf(c_2167,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,X2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | X0 != k2_partfun1(sK0,sK1,sK3,X2)
    | X1 != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_806])).

cnf(c_2576,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | X0 != k2_partfun1(sK0,sK1,sK3,X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_2167])).

cnf(c_18875,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k7_relat_1(sK3,sK2) != k2_partfun1(sK0,sK1,sK3,X0)
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_2576])).

cnf(c_54987,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k7_relat_1(sK3,sK2) != k2_partfun1(sK0,sK1,sK3,sK2)
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_18875])).

cnf(c_2577,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_801])).

cnf(c_1996,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1720])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_181552,c_151218,c_129541,c_92924,c_85417,c_85088,c_54988,c_54987,c_28350,c_9449,c_3614,c_2577,c_2070,c_1996,c_1635,c_1634,c_101,c_100,c_34,c_29,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : iproveropt_run.sh %d %s
% 0.11/0.31  % Computer   : n013.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % WCLimit    : 600
% 0.11/0.31  % DateTime   : Tue Dec  1 20:21:39 EST 2020
% 0.11/0.31  % CPUTime    : 
% 0.17/0.31  % Running in FOF mode
% 39.30/5.51  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 39.30/5.51  
% 39.30/5.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 39.30/5.51  
% 39.30/5.51  ------  iProver source info
% 39.30/5.51  
% 39.30/5.51  git: date: 2020-06-30 10:37:57 +0100
% 39.30/5.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 39.30/5.51  git: non_committed_changes: false
% 39.30/5.51  git: last_make_outside_of_git: false
% 39.30/5.51  
% 39.30/5.51  ------ 
% 39.30/5.51  
% 39.30/5.51  ------ Input Options
% 39.30/5.51  
% 39.30/5.51  --out_options                           all
% 39.30/5.51  --tptp_safe_out                         true
% 39.30/5.51  --problem_path                          ""
% 39.30/5.51  --include_path                          ""
% 39.30/5.51  --clausifier                            res/vclausify_rel
% 39.30/5.51  --clausifier_options                    --mode clausify
% 39.30/5.51  --stdin                                 false
% 39.30/5.51  --stats_out                             all
% 39.30/5.51  
% 39.30/5.51  ------ General Options
% 39.30/5.51  
% 39.30/5.51  --fof                                   false
% 39.30/5.51  --time_out_real                         305.
% 39.30/5.51  --time_out_virtual                      -1.
% 39.30/5.51  --symbol_type_check                     false
% 39.30/5.51  --clausify_out                          false
% 39.30/5.51  --sig_cnt_out                           false
% 39.30/5.51  --trig_cnt_out                          false
% 39.30/5.51  --trig_cnt_out_tolerance                1.
% 39.30/5.51  --trig_cnt_out_sk_spl                   false
% 39.30/5.51  --abstr_cl_out                          false
% 39.30/5.51  
% 39.30/5.51  ------ Global Options
% 39.30/5.51  
% 39.30/5.51  --schedule                              default
% 39.30/5.51  --add_important_lit                     false
% 39.30/5.51  --prop_solver_per_cl                    1000
% 39.30/5.51  --min_unsat_core                        false
% 39.30/5.51  --soft_assumptions                      false
% 39.30/5.51  --soft_lemma_size                       3
% 39.30/5.51  --prop_impl_unit_size                   0
% 39.30/5.51  --prop_impl_unit                        []
% 39.30/5.51  --share_sel_clauses                     true
% 39.30/5.51  --reset_solvers                         false
% 39.30/5.51  --bc_imp_inh                            [conj_cone]
% 39.30/5.51  --conj_cone_tolerance                   3.
% 39.30/5.51  --extra_neg_conj                        none
% 39.30/5.51  --large_theory_mode                     true
% 39.30/5.51  --prolific_symb_bound                   200
% 39.30/5.51  --lt_threshold                          2000
% 39.30/5.51  --clause_weak_htbl                      true
% 39.30/5.51  --gc_record_bc_elim                     false
% 39.30/5.51  
% 39.30/5.51  ------ Preprocessing Options
% 39.30/5.51  
% 39.30/5.51  --preprocessing_flag                    true
% 39.30/5.51  --time_out_prep_mult                    0.1
% 39.30/5.51  --splitting_mode                        input
% 39.30/5.51  --splitting_grd                         true
% 39.30/5.51  --splitting_cvd                         false
% 39.30/5.51  --splitting_cvd_svl                     false
% 39.30/5.51  --splitting_nvd                         32
% 39.30/5.51  --sub_typing                            true
% 39.30/5.51  --prep_gs_sim                           true
% 39.30/5.51  --prep_unflatten                        true
% 39.30/5.51  --prep_res_sim                          true
% 39.30/5.51  --prep_upred                            true
% 39.30/5.51  --prep_sem_filter                       exhaustive
% 39.30/5.51  --prep_sem_filter_out                   false
% 39.30/5.51  --pred_elim                             true
% 39.30/5.51  --res_sim_input                         true
% 39.30/5.51  --eq_ax_congr_red                       true
% 39.30/5.51  --pure_diseq_elim                       true
% 39.30/5.51  --brand_transform                       false
% 39.30/5.51  --non_eq_to_eq                          false
% 39.30/5.51  --prep_def_merge                        true
% 39.30/5.51  --prep_def_merge_prop_impl              false
% 39.30/5.51  --prep_def_merge_mbd                    true
% 39.30/5.51  --prep_def_merge_tr_red                 false
% 39.30/5.51  --prep_def_merge_tr_cl                  false
% 39.30/5.51  --smt_preprocessing                     true
% 39.30/5.51  --smt_ac_axioms                         fast
% 39.30/5.51  --preprocessed_out                      false
% 39.30/5.51  --preprocessed_stats                    false
% 39.30/5.51  
% 39.30/5.51  ------ Abstraction refinement Options
% 39.30/5.51  
% 39.30/5.51  --abstr_ref                             []
% 39.30/5.51  --abstr_ref_prep                        false
% 39.30/5.51  --abstr_ref_until_sat                   false
% 39.30/5.51  --abstr_ref_sig_restrict                funpre
% 39.30/5.51  --abstr_ref_af_restrict_to_split_sk     false
% 39.30/5.51  --abstr_ref_under                       []
% 39.30/5.51  
% 39.30/5.51  ------ SAT Options
% 39.30/5.51  
% 39.30/5.51  --sat_mode                              false
% 39.30/5.51  --sat_fm_restart_options                ""
% 39.30/5.51  --sat_gr_def                            false
% 39.30/5.51  --sat_epr_types                         true
% 39.30/5.51  --sat_non_cyclic_types                  false
% 39.30/5.51  --sat_finite_models                     false
% 39.30/5.51  --sat_fm_lemmas                         false
% 39.30/5.51  --sat_fm_prep                           false
% 39.30/5.51  --sat_fm_uc_incr                        true
% 39.30/5.51  --sat_out_model                         small
% 39.30/5.51  --sat_out_clauses                       false
% 39.30/5.51  
% 39.30/5.51  ------ QBF Options
% 39.30/5.51  
% 39.30/5.51  --qbf_mode                              false
% 39.30/5.51  --qbf_elim_univ                         false
% 39.30/5.51  --qbf_dom_inst                          none
% 39.30/5.51  --qbf_dom_pre_inst                      false
% 39.30/5.51  --qbf_sk_in                             false
% 39.30/5.51  --qbf_pred_elim                         true
% 39.30/5.51  --qbf_split                             512
% 39.30/5.51  
% 39.30/5.51  ------ BMC1 Options
% 39.30/5.51  
% 39.30/5.51  --bmc1_incremental                      false
% 39.30/5.51  --bmc1_axioms                           reachable_all
% 39.30/5.51  --bmc1_min_bound                        0
% 39.30/5.51  --bmc1_max_bound                        -1
% 39.30/5.51  --bmc1_max_bound_default                -1
% 39.30/5.51  --bmc1_symbol_reachability              true
% 39.30/5.51  --bmc1_property_lemmas                  false
% 39.30/5.51  --bmc1_k_induction                      false
% 39.30/5.51  --bmc1_non_equiv_states                 false
% 39.30/5.51  --bmc1_deadlock                         false
% 39.30/5.51  --bmc1_ucm                              false
% 39.30/5.51  --bmc1_add_unsat_core                   none
% 39.30/5.51  --bmc1_unsat_core_children              false
% 39.30/5.51  --bmc1_unsat_core_extrapolate_axioms    false
% 39.30/5.51  --bmc1_out_stat                         full
% 39.30/5.51  --bmc1_ground_init                      false
% 39.30/5.51  --bmc1_pre_inst_next_state              false
% 39.30/5.51  --bmc1_pre_inst_state                   false
% 39.30/5.51  --bmc1_pre_inst_reach_state             false
% 39.30/5.51  --bmc1_out_unsat_core                   false
% 39.30/5.51  --bmc1_aig_witness_out                  false
% 39.30/5.51  --bmc1_verbose                          false
% 39.30/5.51  --bmc1_dump_clauses_tptp                false
% 39.30/5.51  --bmc1_dump_unsat_core_tptp             false
% 39.30/5.51  --bmc1_dump_file                        -
% 39.30/5.51  --bmc1_ucm_expand_uc_limit              128
% 39.30/5.51  --bmc1_ucm_n_expand_iterations          6
% 39.30/5.51  --bmc1_ucm_extend_mode                  1
% 39.30/5.51  --bmc1_ucm_init_mode                    2
% 39.30/5.51  --bmc1_ucm_cone_mode                    none
% 39.30/5.51  --bmc1_ucm_reduced_relation_type        0
% 39.30/5.51  --bmc1_ucm_relax_model                  4
% 39.30/5.51  --bmc1_ucm_full_tr_after_sat            true
% 39.30/5.51  --bmc1_ucm_expand_neg_assumptions       false
% 39.30/5.51  --bmc1_ucm_layered_model                none
% 39.30/5.51  --bmc1_ucm_max_lemma_size               10
% 39.30/5.51  
% 39.30/5.51  ------ AIG Options
% 39.30/5.51  
% 39.30/5.51  --aig_mode                              false
% 39.30/5.51  
% 39.30/5.51  ------ Instantiation Options
% 39.30/5.51  
% 39.30/5.51  --instantiation_flag                    true
% 39.30/5.51  --inst_sos_flag                         false
% 39.30/5.51  --inst_sos_phase                        true
% 39.30/5.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 39.30/5.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 39.30/5.51  --inst_lit_sel_side                     num_symb
% 39.30/5.51  --inst_solver_per_active                1400
% 39.30/5.51  --inst_solver_calls_frac                1.
% 39.30/5.51  --inst_passive_queue_type               priority_queues
% 39.30/5.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 39.30/5.51  --inst_passive_queues_freq              [25;2]
% 39.30/5.51  --inst_dismatching                      true
% 39.30/5.51  --inst_eager_unprocessed_to_passive     true
% 39.30/5.51  --inst_prop_sim_given                   true
% 39.30/5.51  --inst_prop_sim_new                     false
% 39.30/5.51  --inst_subs_new                         false
% 39.30/5.51  --inst_eq_res_simp                      false
% 39.30/5.51  --inst_subs_given                       false
% 39.30/5.51  --inst_orphan_elimination               true
% 39.30/5.51  --inst_learning_loop_flag               true
% 39.30/5.51  --inst_learning_start                   3000
% 39.30/5.51  --inst_learning_factor                  2
% 39.30/5.51  --inst_start_prop_sim_after_learn       3
% 39.30/5.51  --inst_sel_renew                        solver
% 39.30/5.51  --inst_lit_activity_flag                true
% 39.30/5.51  --inst_restr_to_given                   false
% 39.30/5.51  --inst_activity_threshold               500
% 39.30/5.51  --inst_out_proof                        true
% 39.30/5.51  
% 39.30/5.51  ------ Resolution Options
% 39.30/5.51  
% 39.30/5.51  --resolution_flag                       true
% 39.30/5.51  --res_lit_sel                           adaptive
% 39.30/5.51  --res_lit_sel_side                      none
% 39.30/5.51  --res_ordering                          kbo
% 39.30/5.51  --res_to_prop_solver                    active
% 39.30/5.51  --res_prop_simpl_new                    false
% 39.30/5.51  --res_prop_simpl_given                  true
% 39.30/5.51  --res_passive_queue_type                priority_queues
% 39.30/5.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 39.30/5.51  --res_passive_queues_freq               [15;5]
% 39.30/5.51  --res_forward_subs                      full
% 39.30/5.51  --res_backward_subs                     full
% 39.30/5.51  --res_forward_subs_resolution           true
% 39.30/5.51  --res_backward_subs_resolution          true
% 39.30/5.51  --res_orphan_elimination                true
% 39.30/5.51  --res_time_limit                        2.
% 39.30/5.51  --res_out_proof                         true
% 39.30/5.51  
% 39.30/5.51  ------ Superposition Options
% 39.30/5.51  
% 39.30/5.51  --superposition_flag                    true
% 39.30/5.51  --sup_passive_queue_type                priority_queues
% 39.30/5.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 39.30/5.51  --sup_passive_queues_freq               [8;1;4]
% 39.30/5.51  --demod_completeness_check              fast
% 39.30/5.51  --demod_use_ground                      true
% 39.30/5.51  --sup_to_prop_solver                    passive
% 39.30/5.51  --sup_prop_simpl_new                    true
% 39.30/5.51  --sup_prop_simpl_given                  true
% 39.30/5.51  --sup_fun_splitting                     false
% 39.30/5.51  --sup_smt_interval                      50000
% 39.30/5.51  
% 39.30/5.51  ------ Superposition Simplification Setup
% 39.30/5.51  
% 39.30/5.51  --sup_indices_passive                   []
% 39.30/5.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 39.30/5.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 39.30/5.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 39.30/5.51  --sup_full_triv                         [TrivRules;PropSubs]
% 39.30/5.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 39.30/5.51  --sup_full_bw                           [BwDemod]
% 39.30/5.51  --sup_immed_triv                        [TrivRules]
% 39.30/5.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 39.30/5.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 39.30/5.51  --sup_immed_bw_main                     []
% 39.30/5.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 39.30/5.51  --sup_input_triv                        [Unflattening;TrivRules]
% 39.30/5.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 39.30/5.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 39.30/5.51  
% 39.30/5.51  ------ Combination Options
% 39.30/5.51  
% 39.30/5.51  --comb_res_mult                         3
% 39.30/5.51  --comb_sup_mult                         2
% 39.30/5.51  --comb_inst_mult                        10
% 39.30/5.51  
% 39.30/5.51  ------ Debug Options
% 39.30/5.51  
% 39.30/5.51  --dbg_backtrace                         false
% 39.30/5.51  --dbg_dump_prop_clauses                 false
% 39.30/5.51  --dbg_dump_prop_clauses_file            -
% 39.30/5.51  --dbg_out_stat                          false
% 39.30/5.51  ------ Parsing...
% 39.30/5.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 39.30/5.51  
% 39.30/5.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 39.30/5.51  
% 39.30/5.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 39.30/5.51  
% 39.30/5.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.30/5.51  ------ Proving...
% 39.30/5.51  ------ Problem Properties 
% 39.30/5.51  
% 39.30/5.51  
% 39.30/5.51  clauses                                 29
% 39.30/5.51  conjectures                             4
% 39.30/5.51  EPR                                     5
% 39.30/5.51  Horn                                    26
% 39.30/5.51  unary                                   5
% 39.30/5.51  binary                                  11
% 39.30/5.51  lits                                    75
% 39.30/5.51  lits eq                                 27
% 39.30/5.51  fd_pure                                 0
% 39.30/5.51  fd_pseudo                               0
% 39.30/5.51  fd_cond                                 2
% 39.30/5.51  fd_pseudo_cond                          0
% 39.30/5.51  AC symbols                              0
% 39.30/5.51  
% 39.30/5.51  ------ Schedule dynamic 5 is on 
% 39.30/5.51  
% 39.30/5.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 39.30/5.51  
% 39.30/5.51  
% 39.30/5.51  ------ 
% 39.30/5.51  Current options:
% 39.30/5.51  ------ 
% 39.30/5.51  
% 39.30/5.51  ------ Input Options
% 39.30/5.51  
% 39.30/5.51  --out_options                           all
% 39.30/5.51  --tptp_safe_out                         true
% 39.30/5.51  --problem_path                          ""
% 39.30/5.51  --include_path                          ""
% 39.30/5.51  --clausifier                            res/vclausify_rel
% 39.30/5.51  --clausifier_options                    --mode clausify
% 39.30/5.51  --stdin                                 false
% 39.30/5.51  --stats_out                             all
% 39.30/5.51  
% 39.30/5.51  ------ General Options
% 39.30/5.51  
% 39.30/5.51  --fof                                   false
% 39.30/5.51  --time_out_real                         305.
% 39.30/5.51  --time_out_virtual                      -1.
% 39.30/5.51  --symbol_type_check                     false
% 39.30/5.51  --clausify_out                          false
% 39.30/5.51  --sig_cnt_out                           false
% 39.30/5.51  --trig_cnt_out                          false
% 39.30/5.51  --trig_cnt_out_tolerance                1.
% 39.30/5.51  --trig_cnt_out_sk_spl                   false
% 39.30/5.51  --abstr_cl_out                          false
% 39.30/5.51  
% 39.30/5.51  ------ Global Options
% 39.30/5.51  
% 39.30/5.51  --schedule                              default
% 39.30/5.51  --add_important_lit                     false
% 39.30/5.51  --prop_solver_per_cl                    1000
% 39.30/5.51  --min_unsat_core                        false
% 39.30/5.51  --soft_assumptions                      false
% 39.30/5.51  --soft_lemma_size                       3
% 39.30/5.51  --prop_impl_unit_size                   0
% 39.30/5.51  --prop_impl_unit                        []
% 39.30/5.51  --share_sel_clauses                     true
% 39.30/5.51  --reset_solvers                         false
% 39.30/5.51  --bc_imp_inh                            [conj_cone]
% 39.30/5.51  --conj_cone_tolerance                   3.
% 39.30/5.51  --extra_neg_conj                        none
% 39.30/5.51  --large_theory_mode                     true
% 39.30/5.51  --prolific_symb_bound                   200
% 39.30/5.51  --lt_threshold                          2000
% 39.30/5.51  --clause_weak_htbl                      true
% 39.30/5.51  --gc_record_bc_elim                     false
% 39.30/5.51  
% 39.30/5.51  ------ Preprocessing Options
% 39.30/5.51  
% 39.30/5.51  --preprocessing_flag                    true
% 39.30/5.51  --time_out_prep_mult                    0.1
% 39.30/5.51  --splitting_mode                        input
% 39.30/5.51  --splitting_grd                         true
% 39.30/5.51  --splitting_cvd                         false
% 39.30/5.51  --splitting_cvd_svl                     false
% 39.30/5.51  --splitting_nvd                         32
% 39.30/5.51  --sub_typing                            true
% 39.30/5.51  --prep_gs_sim                           true
% 39.30/5.51  --prep_unflatten                        true
% 39.30/5.51  --prep_res_sim                          true
% 39.30/5.51  --prep_upred                            true
% 39.30/5.51  --prep_sem_filter                       exhaustive
% 39.30/5.51  --prep_sem_filter_out                   false
% 39.30/5.51  --pred_elim                             true
% 39.30/5.51  --res_sim_input                         true
% 39.30/5.51  --eq_ax_congr_red                       true
% 39.30/5.51  --pure_diseq_elim                       true
% 39.30/5.51  --brand_transform                       false
% 39.30/5.51  --non_eq_to_eq                          false
% 39.30/5.51  --prep_def_merge                        true
% 39.30/5.51  --prep_def_merge_prop_impl              false
% 39.30/5.51  --prep_def_merge_mbd                    true
% 39.30/5.51  --prep_def_merge_tr_red                 false
% 39.30/5.51  --prep_def_merge_tr_cl                  false
% 39.30/5.51  --smt_preprocessing                     true
% 39.30/5.51  --smt_ac_axioms                         fast
% 39.30/5.51  --preprocessed_out                      false
% 39.30/5.51  --preprocessed_stats                    false
% 39.30/5.51  
% 39.30/5.51  ------ Abstraction refinement Options
% 39.30/5.51  
% 39.30/5.51  --abstr_ref                             []
% 39.30/5.51  --abstr_ref_prep                        false
% 39.30/5.51  --abstr_ref_until_sat                   false
% 39.30/5.51  --abstr_ref_sig_restrict                funpre
% 39.30/5.51  --abstr_ref_af_restrict_to_split_sk     false
% 39.30/5.51  --abstr_ref_under                       []
% 39.30/5.51  
% 39.30/5.51  ------ SAT Options
% 39.30/5.51  
% 39.30/5.51  --sat_mode                              false
% 39.30/5.51  --sat_fm_restart_options                ""
% 39.30/5.51  --sat_gr_def                            false
% 39.30/5.51  --sat_epr_types                         true
% 39.30/5.51  --sat_non_cyclic_types                  false
% 39.30/5.51  --sat_finite_models                     false
% 39.30/5.51  --sat_fm_lemmas                         false
% 39.30/5.51  --sat_fm_prep                           false
% 39.30/5.51  --sat_fm_uc_incr                        true
% 39.30/5.51  --sat_out_model                         small
% 39.30/5.51  --sat_out_clauses                       false
% 39.30/5.51  
% 39.30/5.51  ------ QBF Options
% 39.30/5.51  
% 39.30/5.51  --qbf_mode                              false
% 39.30/5.51  --qbf_elim_univ                         false
% 39.30/5.51  --qbf_dom_inst                          none
% 39.30/5.51  --qbf_dom_pre_inst                      false
% 39.30/5.51  --qbf_sk_in                             false
% 39.30/5.51  --qbf_pred_elim                         true
% 39.30/5.51  --qbf_split                             512
% 39.30/5.51  
% 39.30/5.51  ------ BMC1 Options
% 39.30/5.51  
% 39.30/5.51  --bmc1_incremental                      false
% 39.30/5.51  --bmc1_axioms                           reachable_all
% 39.30/5.51  --bmc1_min_bound                        0
% 39.30/5.51  --bmc1_max_bound                        -1
% 39.30/5.51  --bmc1_max_bound_default                -1
% 39.30/5.51  --bmc1_symbol_reachability              true
% 39.30/5.51  --bmc1_property_lemmas                  false
% 39.30/5.51  --bmc1_k_induction                      false
% 39.30/5.51  --bmc1_non_equiv_states                 false
% 39.30/5.51  --bmc1_deadlock                         false
% 39.30/5.51  --bmc1_ucm                              false
% 39.30/5.51  --bmc1_add_unsat_core                   none
% 39.30/5.51  --bmc1_unsat_core_children              false
% 39.30/5.51  --bmc1_unsat_core_extrapolate_axioms    false
% 39.30/5.51  --bmc1_out_stat                         full
% 39.30/5.51  --bmc1_ground_init                      false
% 39.30/5.51  --bmc1_pre_inst_next_state              false
% 39.30/5.51  --bmc1_pre_inst_state                   false
% 39.30/5.51  --bmc1_pre_inst_reach_state             false
% 39.30/5.51  --bmc1_out_unsat_core                   false
% 39.30/5.51  --bmc1_aig_witness_out                  false
% 39.30/5.51  --bmc1_verbose                          false
% 39.30/5.51  --bmc1_dump_clauses_tptp                false
% 39.30/5.51  --bmc1_dump_unsat_core_tptp             false
% 39.30/5.51  --bmc1_dump_file                        -
% 39.30/5.51  --bmc1_ucm_expand_uc_limit              128
% 39.30/5.51  --bmc1_ucm_n_expand_iterations          6
% 39.30/5.51  --bmc1_ucm_extend_mode                  1
% 39.30/5.51  --bmc1_ucm_init_mode                    2
% 39.30/5.51  --bmc1_ucm_cone_mode                    none
% 39.30/5.51  --bmc1_ucm_reduced_relation_type        0
% 39.30/5.51  --bmc1_ucm_relax_model                  4
% 39.30/5.51  --bmc1_ucm_full_tr_after_sat            true
% 39.30/5.51  --bmc1_ucm_expand_neg_assumptions       false
% 39.30/5.51  --bmc1_ucm_layered_model                none
% 39.30/5.51  --bmc1_ucm_max_lemma_size               10
% 39.30/5.51  
% 39.30/5.51  ------ AIG Options
% 39.30/5.51  
% 39.30/5.51  --aig_mode                              false
% 39.30/5.51  
% 39.30/5.51  ------ Instantiation Options
% 39.30/5.51  
% 39.30/5.51  --instantiation_flag                    true
% 39.30/5.51  --inst_sos_flag                         false
% 39.30/5.51  --inst_sos_phase                        true
% 39.30/5.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 39.30/5.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 39.30/5.51  --inst_lit_sel_side                     none
% 39.30/5.51  --inst_solver_per_active                1400
% 39.30/5.51  --inst_solver_calls_frac                1.
% 39.30/5.51  --inst_passive_queue_type               priority_queues
% 39.30/5.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 39.30/5.51  --inst_passive_queues_freq              [25;2]
% 39.30/5.51  --inst_dismatching                      true
% 39.30/5.51  --inst_eager_unprocessed_to_passive     true
% 39.30/5.51  --inst_prop_sim_given                   true
% 39.30/5.51  --inst_prop_sim_new                     false
% 39.30/5.51  --inst_subs_new                         false
% 39.30/5.51  --inst_eq_res_simp                      false
% 39.30/5.51  --inst_subs_given                       false
% 39.30/5.51  --inst_orphan_elimination               true
% 39.30/5.51  --inst_learning_loop_flag               true
% 39.30/5.51  --inst_learning_start                   3000
% 39.30/5.51  --inst_learning_factor                  2
% 39.30/5.51  --inst_start_prop_sim_after_learn       3
% 39.30/5.51  --inst_sel_renew                        solver
% 39.30/5.51  --inst_lit_activity_flag                true
% 39.30/5.51  --inst_restr_to_given                   false
% 39.30/5.51  --inst_activity_threshold               500
% 39.30/5.51  --inst_out_proof                        true
% 39.30/5.51  
% 39.30/5.51  ------ Resolution Options
% 39.30/5.51  
% 39.30/5.51  --resolution_flag                       false
% 39.30/5.51  --res_lit_sel                           adaptive
% 39.30/5.51  --res_lit_sel_side                      none
% 39.30/5.51  --res_ordering                          kbo
% 39.30/5.51  --res_to_prop_solver                    active
% 39.30/5.51  --res_prop_simpl_new                    false
% 39.30/5.51  --res_prop_simpl_given                  true
% 39.30/5.51  --res_passive_queue_type                priority_queues
% 39.30/5.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 39.30/5.51  --res_passive_queues_freq               [15;5]
% 39.30/5.51  --res_forward_subs                      full
% 39.30/5.51  --res_backward_subs                     full
% 39.30/5.51  --res_forward_subs_resolution           true
% 39.30/5.51  --res_backward_subs_resolution          true
% 39.30/5.51  --res_orphan_elimination                true
% 39.30/5.51  --res_time_limit                        2.
% 39.30/5.51  --res_out_proof                         true
% 39.30/5.51  
% 39.30/5.51  ------ Superposition Options
% 39.30/5.51  
% 39.30/5.51  --superposition_flag                    true
% 39.30/5.51  --sup_passive_queue_type                priority_queues
% 39.30/5.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 39.30/5.51  --sup_passive_queues_freq               [8;1;4]
% 39.30/5.51  --demod_completeness_check              fast
% 39.30/5.51  --demod_use_ground                      true
% 39.30/5.51  --sup_to_prop_solver                    passive
% 39.30/5.51  --sup_prop_simpl_new                    true
% 39.30/5.51  --sup_prop_simpl_given                  true
% 39.30/5.51  --sup_fun_splitting                     false
% 39.30/5.51  --sup_smt_interval                      50000
% 39.30/5.51  
% 39.30/5.51  ------ Superposition Simplification Setup
% 39.30/5.51  
% 39.30/5.51  --sup_indices_passive                   []
% 39.30/5.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 39.30/5.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 39.30/5.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 39.30/5.51  --sup_full_triv                         [TrivRules;PropSubs]
% 39.30/5.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 39.30/5.51  --sup_full_bw                           [BwDemod]
% 39.30/5.51  --sup_immed_triv                        [TrivRules]
% 39.30/5.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 39.30/5.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 39.30/5.51  --sup_immed_bw_main                     []
% 39.30/5.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 39.30/5.51  --sup_input_triv                        [Unflattening;TrivRules]
% 39.30/5.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 39.30/5.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 39.30/5.51  
% 39.30/5.51  ------ Combination Options
% 39.30/5.51  
% 39.30/5.51  --comb_res_mult                         3
% 39.30/5.51  --comb_sup_mult                         2
% 39.30/5.51  --comb_inst_mult                        10
% 39.30/5.51  
% 39.30/5.51  ------ Debug Options
% 39.30/5.51  
% 39.30/5.51  --dbg_backtrace                         false
% 39.30/5.51  --dbg_dump_prop_clauses                 false
% 39.30/5.51  --dbg_dump_prop_clauses_file            -
% 39.30/5.51  --dbg_out_stat                          false
% 39.30/5.51  
% 39.30/5.51  
% 39.30/5.51  
% 39.30/5.51  
% 39.30/5.51  ------ Proving...
% 39.30/5.51  
% 39.30/5.51  
% 39.30/5.51  % SZS status Theorem for theBenchmark.p
% 39.30/5.51  
% 39.30/5.51  % SZS output start CNFRefutation for theBenchmark.p
% 39.30/5.51  
% 39.30/5.51  fof(f11,axiom,(
% 39.30/5.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 39.30/5.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.30/5.51  
% 39.30/5.51  fof(f19,plain,(
% 39.30/5.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 39.30/5.51    inference(pure_predicate_removal,[],[f11])).
% 39.30/5.51  
% 39.30/5.51  fof(f30,plain,(
% 39.30/5.51    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 39.30/5.51    inference(ennf_transformation,[],[f19])).
% 39.30/5.51  
% 39.30/5.51  fof(f63,plain,(
% 39.30/5.51    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 39.30/5.51    inference(cnf_transformation,[],[f30])).
% 39.30/5.51  
% 39.30/5.51  fof(f5,axiom,(
% 39.30/5.51    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 39.30/5.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.30/5.51  
% 39.30/5.51  fof(f23,plain,(
% 39.30/5.51    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 39.30/5.51    inference(ennf_transformation,[],[f5])).
% 39.30/5.51  
% 39.30/5.51  fof(f45,plain,(
% 39.30/5.51    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 39.30/5.51    inference(nnf_transformation,[],[f23])).
% 39.30/5.51  
% 39.30/5.51  fof(f56,plain,(
% 39.30/5.51    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 39.30/5.51    inference(cnf_transformation,[],[f45])).
% 39.30/5.51  
% 39.30/5.51  fof(f10,axiom,(
% 39.30/5.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 39.30/5.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.30/5.51  
% 39.30/5.51  fof(f29,plain,(
% 39.30/5.51    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 39.30/5.51    inference(ennf_transformation,[],[f10])).
% 39.30/5.51  
% 39.30/5.51  fof(f62,plain,(
% 39.30/5.51    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 39.30/5.51    inference(cnf_transformation,[],[f29])).
% 39.30/5.51  
% 39.30/5.51  fof(f14,axiom,(
% 39.30/5.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 39.30/5.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.30/5.51  
% 39.30/5.51  fof(f34,plain,(
% 39.30/5.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 39.30/5.51    inference(ennf_transformation,[],[f14])).
% 39.30/5.51  
% 39.30/5.51  fof(f35,plain,(
% 39.30/5.51    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 39.30/5.51    inference(flattening,[],[f34])).
% 39.30/5.51  
% 39.30/5.51  fof(f46,plain,(
% 39.30/5.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 39.30/5.51    inference(nnf_transformation,[],[f35])).
% 39.30/5.51  
% 39.30/5.51  fof(f66,plain,(
% 39.30/5.51    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 39.30/5.51    inference(cnf_transformation,[],[f46])).
% 39.30/5.51  
% 39.30/5.51  fof(f17,conjecture,(
% 39.30/5.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 39.30/5.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.30/5.51  
% 39.30/5.51  fof(f18,negated_conjecture,(
% 39.30/5.51    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 39.30/5.51    inference(negated_conjecture,[],[f17])).
% 39.30/5.51  
% 39.30/5.51  fof(f40,plain,(
% 39.30/5.51    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 39.30/5.51    inference(ennf_transformation,[],[f18])).
% 39.30/5.51  
% 39.30/5.51  fof(f41,plain,(
% 39.30/5.51    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 39.30/5.51    inference(flattening,[],[f40])).
% 39.30/5.51  
% 39.30/5.51  fof(f47,plain,(
% 39.30/5.51    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 39.30/5.51    introduced(choice_axiom,[])).
% 39.30/5.51  
% 39.30/5.51  fof(f48,plain,(
% 39.30/5.51    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 39.30/5.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f41,f47])).
% 39.30/5.51  
% 39.30/5.51  fof(f76,plain,(
% 39.30/5.51    v1_funct_2(sK3,sK0,sK1)),
% 39.30/5.51    inference(cnf_transformation,[],[f48])).
% 39.30/5.51  
% 39.30/5.51  fof(f77,plain,(
% 39.30/5.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 39.30/5.51    inference(cnf_transformation,[],[f48])).
% 39.30/5.51  
% 39.30/5.51  fof(f12,axiom,(
% 39.30/5.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 39.30/5.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.30/5.51  
% 39.30/5.51  fof(f31,plain,(
% 39.30/5.51    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 39.30/5.51    inference(ennf_transformation,[],[f12])).
% 39.30/5.51  
% 39.30/5.51  fof(f64,plain,(
% 39.30/5.51    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 39.30/5.51    inference(cnf_transformation,[],[f31])).
% 39.30/5.51  
% 39.30/5.51  fof(f3,axiom,(
% 39.30/5.51    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 39.30/5.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.30/5.51  
% 39.30/5.51  fof(f42,plain,(
% 39.30/5.51    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 39.30/5.51    inference(nnf_transformation,[],[f3])).
% 39.30/5.51  
% 39.30/5.51  fof(f43,plain,(
% 39.30/5.51    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 39.30/5.51    inference(flattening,[],[f42])).
% 39.30/5.51  
% 39.30/5.51  fof(f52,plain,(
% 39.30/5.51    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 39.30/5.51    inference(cnf_transformation,[],[f43])).
% 39.30/5.51  
% 39.30/5.51  fof(f82,plain,(
% 39.30/5.51    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 39.30/5.51    inference(equality_resolution,[],[f52])).
% 39.30/5.51  
% 39.30/5.51  fof(f13,axiom,(
% 39.30/5.51    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 39.30/5.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.30/5.51  
% 39.30/5.51  fof(f32,plain,(
% 39.30/5.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 39.30/5.51    inference(ennf_transformation,[],[f13])).
% 39.30/5.51  
% 39.30/5.51  fof(f33,plain,(
% 39.30/5.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 39.30/5.51    inference(flattening,[],[f32])).
% 39.30/5.51  
% 39.30/5.51  fof(f65,plain,(
% 39.30/5.51    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 39.30/5.51    inference(cnf_transformation,[],[f33])).
% 39.30/5.51  
% 39.30/5.51  fof(f15,axiom,(
% 39.30/5.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 39.30/5.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.30/5.51  
% 39.30/5.51  fof(f36,plain,(
% 39.30/5.51    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 39.30/5.51    inference(ennf_transformation,[],[f15])).
% 39.30/5.51  
% 39.30/5.51  fof(f37,plain,(
% 39.30/5.51    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 39.30/5.51    inference(flattening,[],[f36])).
% 39.30/5.51  
% 39.30/5.51  fof(f73,plain,(
% 39.30/5.51    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 39.30/5.51    inference(cnf_transformation,[],[f37])).
% 39.30/5.51  
% 39.30/5.51  fof(f4,axiom,(
% 39.30/5.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 39.30/5.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.30/5.51  
% 39.30/5.51  fof(f44,plain,(
% 39.30/5.51    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 39.30/5.51    inference(nnf_transformation,[],[f4])).
% 39.30/5.51  
% 39.30/5.51  fof(f55,plain,(
% 39.30/5.51    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 39.30/5.51    inference(cnf_transformation,[],[f44])).
% 39.30/5.51  
% 39.30/5.51  fof(f53,plain,(
% 39.30/5.51    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 39.30/5.51    inference(cnf_transformation,[],[f43])).
% 39.30/5.51  
% 39.30/5.51  fof(f81,plain,(
% 39.30/5.51    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 39.30/5.51    inference(equality_resolution,[],[f53])).
% 39.30/5.51  
% 39.30/5.51  fof(f7,axiom,(
% 39.30/5.51    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 39.30/5.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.30/5.51  
% 39.30/5.51  fof(f25,plain,(
% 39.30/5.51    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 39.30/5.51    inference(ennf_transformation,[],[f7])).
% 39.30/5.51  
% 39.30/5.51  fof(f59,plain,(
% 39.30/5.51    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 39.30/5.51    inference(cnf_transformation,[],[f25])).
% 39.30/5.51  
% 39.30/5.51  fof(f2,axiom,(
% 39.30/5.51    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 39.30/5.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.30/5.51  
% 39.30/5.51  fof(f22,plain,(
% 39.30/5.51    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 39.30/5.51    inference(ennf_transformation,[],[f2])).
% 39.30/5.51  
% 39.30/5.51  fof(f50,plain,(
% 39.30/5.51    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 39.30/5.51    inference(cnf_transformation,[],[f22])).
% 39.30/5.51  
% 39.30/5.51  fof(f6,axiom,(
% 39.30/5.51    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 39.30/5.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.30/5.51  
% 39.30/5.51  fof(f24,plain,(
% 39.30/5.51    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 39.30/5.51    inference(ennf_transformation,[],[f6])).
% 39.30/5.51  
% 39.30/5.51  fof(f58,plain,(
% 39.30/5.51    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 39.30/5.51    inference(cnf_transformation,[],[f24])).
% 39.30/5.51  
% 39.30/5.51  fof(f16,axiom,(
% 39.30/5.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 39.30/5.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.30/5.51  
% 39.30/5.51  fof(f38,plain,(
% 39.30/5.51    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 39.30/5.51    inference(ennf_transformation,[],[f16])).
% 39.30/5.51  
% 39.30/5.51  fof(f39,plain,(
% 39.30/5.51    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 39.30/5.51    inference(flattening,[],[f38])).
% 39.30/5.51  
% 39.30/5.51  fof(f74,plain,(
% 39.30/5.51    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 39.30/5.51    inference(cnf_transformation,[],[f39])).
% 39.30/5.51  
% 39.30/5.51  fof(f75,plain,(
% 39.30/5.51    v1_funct_1(sK3)),
% 39.30/5.51    inference(cnf_transformation,[],[f48])).
% 39.30/5.51  
% 39.30/5.51  fof(f54,plain,(
% 39.30/5.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 39.30/5.51    inference(cnf_transformation,[],[f44])).
% 39.30/5.51  
% 39.30/5.51  fof(f1,axiom,(
% 39.30/5.51    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 39.30/5.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.30/5.51  
% 39.30/5.51  fof(f20,plain,(
% 39.30/5.51    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 39.30/5.51    inference(ennf_transformation,[],[f1])).
% 39.30/5.51  
% 39.30/5.51  fof(f21,plain,(
% 39.30/5.51    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 39.30/5.51    inference(flattening,[],[f20])).
% 39.30/5.51  
% 39.30/5.51  fof(f49,plain,(
% 39.30/5.51    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 39.30/5.51    inference(cnf_transformation,[],[f21])).
% 39.30/5.51  
% 39.30/5.51  fof(f51,plain,(
% 39.30/5.51    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 39.30/5.51    inference(cnf_transformation,[],[f43])).
% 39.30/5.51  
% 39.30/5.51  fof(f80,plain,(
% 39.30/5.51    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 39.30/5.51    inference(cnf_transformation,[],[f48])).
% 39.30/5.51  
% 39.30/5.51  fof(f72,plain,(
% 39.30/5.51    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 39.30/5.51    inference(cnf_transformation,[],[f37])).
% 39.30/5.51  
% 39.30/5.51  fof(f78,plain,(
% 39.30/5.51    r1_tarski(sK2,sK0)),
% 39.30/5.51    inference(cnf_transformation,[],[f48])).
% 39.30/5.51  
% 39.30/5.51  fof(f9,axiom,(
% 39.30/5.51    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 39.30/5.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.30/5.51  
% 39.30/5.51  fof(f27,plain,(
% 39.30/5.51    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 39.30/5.51    inference(ennf_transformation,[],[f9])).
% 39.30/5.51  
% 39.30/5.51  fof(f28,plain,(
% 39.30/5.51    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 39.30/5.51    inference(flattening,[],[f27])).
% 39.30/5.51  
% 39.30/5.51  fof(f61,plain,(
% 39.30/5.51    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 39.30/5.51    inference(cnf_transformation,[],[f28])).
% 39.30/5.51  
% 39.30/5.51  fof(f8,axiom,(
% 39.30/5.51    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 39.30/5.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.30/5.51  
% 39.30/5.51  fof(f26,plain,(
% 39.30/5.51    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 39.30/5.51    inference(ennf_transformation,[],[f8])).
% 39.30/5.51  
% 39.30/5.51  fof(f60,plain,(
% 39.30/5.51    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 39.30/5.51    inference(cnf_transformation,[],[f26])).
% 39.30/5.51  
% 39.30/5.51  fof(f70,plain,(
% 39.30/5.51    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 39.30/5.51    inference(cnf_transformation,[],[f46])).
% 39.30/5.51  
% 39.30/5.51  fof(f85,plain,(
% 39.30/5.51    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 39.30/5.51    inference(equality_resolution,[],[f70])).
% 39.30/5.51  
% 39.30/5.51  fof(f79,plain,(
% 39.30/5.51    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 39.30/5.51    inference(cnf_transformation,[],[f48])).
% 39.30/5.51  
% 39.30/5.51  fof(f68,plain,(
% 39.30/5.51    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 39.30/5.51    inference(cnf_transformation,[],[f46])).
% 39.30/5.51  
% 39.30/5.51  cnf(c_14,plain,
% 39.30/5.51      ( v5_relat_1(X0,X1)
% 39.30/5.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 39.30/5.51      inference(cnf_transformation,[],[f63]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_8,plain,
% 39.30/5.51      ( ~ v5_relat_1(X0,X1)
% 39.30/5.51      | r1_tarski(k2_relat_1(X0),X1)
% 39.30/5.51      | ~ v1_relat_1(X0) ),
% 39.30/5.51      inference(cnf_transformation,[],[f56]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_387,plain,
% 39.30/5.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.30/5.51      | r1_tarski(k2_relat_1(X0),X2)
% 39.30/5.51      | ~ v1_relat_1(X0) ),
% 39.30/5.51      inference(resolution,[status(thm)],[c_14,c_8]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_13,plain,
% 39.30/5.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.30/5.51      | v1_relat_1(X0) ),
% 39.30/5.51      inference(cnf_transformation,[],[f62]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_391,plain,
% 39.30/5.51      ( r1_tarski(k2_relat_1(X0),X2)
% 39.30/5.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 39.30/5.51      inference(global_propositional_subsumption,
% 39.30/5.51                [status(thm)],
% 39.30/5.51                [c_387,c_13]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_392,plain,
% 39.30/5.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.30/5.51      | r1_tarski(k2_relat_1(X0),X2) ),
% 39.30/5.51      inference(renaming,[status(thm)],[c_391]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_99025,plain,
% 39.30/5.51      ( ~ m1_subset_1(k7_relat_1(X0,sK2),k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 39.30/5.51      | r1_tarski(k2_relat_1(k7_relat_1(X0,sK2)),sK1) ),
% 39.30/5.51      inference(instantiation,[status(thm)],[c_392]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_131908,plain,
% 39.30/5.51      ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
% 39.30/5.51      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) ),
% 39.30/5.51      inference(instantiation,[status(thm)],[c_99025]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_181552,plain,
% 39.30/5.51      ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 39.30/5.51      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) ),
% 39.30/5.51      inference(instantiation,[status(thm)],[c_131908]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_22,plain,
% 39.30/5.51      ( ~ v1_funct_2(X0,X1,X2)
% 39.30/5.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.30/5.51      | k1_relset_1(X1,X2,X0) = X1
% 39.30/5.51      | k1_xboole_0 = X2 ),
% 39.30/5.51      inference(cnf_transformation,[],[f66]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_30,negated_conjecture,
% 39.30/5.51      ( v1_funct_2(sK3,sK0,sK1) ),
% 39.30/5.51      inference(cnf_transformation,[],[f76]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_510,plain,
% 39.30/5.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.30/5.51      | k1_relset_1(X1,X2,X0) = X1
% 39.30/5.51      | sK3 != X0
% 39.30/5.51      | sK1 != X2
% 39.30/5.51      | sK0 != X1
% 39.30/5.51      | k1_xboole_0 = X2 ),
% 39.30/5.51      inference(resolution_lifted,[status(thm)],[c_22,c_30]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_511,plain,
% 39.30/5.51      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 39.30/5.51      | k1_relset_1(sK0,sK1,sK3) = sK0
% 39.30/5.51      | k1_xboole_0 = sK1 ),
% 39.30/5.51      inference(unflattening,[status(thm)],[c_510]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_29,negated_conjecture,
% 39.30/5.51      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 39.30/5.51      inference(cnf_transformation,[],[f77]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_513,plain,
% 39.30/5.51      ( k1_relset_1(sK0,sK1,sK3) = sK0 | k1_xboole_0 = sK1 ),
% 39.30/5.51      inference(global_propositional_subsumption,
% 39.30/5.51                [status(thm)],
% 39.30/5.51                [c_511,c_29]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_1398,plain,
% 39.30/5.51      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 39.30/5.51      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_15,plain,
% 39.30/5.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.30/5.51      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 39.30/5.51      inference(cnf_transformation,[],[f64]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_1404,plain,
% 39.30/5.51      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 39.30/5.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 39.30/5.51      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_3038,plain,
% 39.30/5.51      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 39.30/5.51      inference(superposition,[status(thm)],[c_1398,c_1404]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_3350,plain,
% 39.30/5.51      ( k1_relat_1(sK3) = sK0 | sK1 = k1_xboole_0 ),
% 39.30/5.51      inference(superposition,[status(thm)],[c_513,c_3038]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_1396,plain,
% 39.30/5.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 39.30/5.51      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 39.30/5.51      inference(predicate_to_equality,[status(thm)],[c_392]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_1810,plain,
% 39.30/5.51      ( r1_tarski(k2_relat_1(sK3),sK1) = iProver_top ),
% 39.30/5.51      inference(superposition,[status(thm)],[c_1398,c_1396]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_3,plain,
% 39.30/5.51      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 39.30/5.51      inference(cnf_transformation,[],[f82]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_16,plain,
% 39.30/5.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.30/5.51      | ~ r1_tarski(k1_relat_1(X0),X1)
% 39.30/5.51      | ~ r1_tarski(k2_relat_1(X0),X2)
% 39.30/5.51      | ~ v1_relat_1(X0) ),
% 39.30/5.51      inference(cnf_transformation,[],[f65]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_1403,plain,
% 39.30/5.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 39.30/5.51      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 39.30/5.51      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 39.30/5.51      | v1_relat_1(X0) != iProver_top ),
% 39.30/5.51      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_4554,plain,
% 39.30/5.51      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 39.30/5.51      | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
% 39.30/5.51      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 39.30/5.51      | v1_relat_1(X0) != iProver_top ),
% 39.30/5.51      inference(superposition,[status(thm)],[c_3,c_1403]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_6252,plain,
% 39.30/5.51      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 39.30/5.51      | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top
% 39.30/5.51      | v1_relat_1(sK3) != iProver_top ),
% 39.30/5.51      inference(superposition,[status(thm)],[c_1810,c_4554]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_34,plain,
% 39.30/5.51      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 39.30/5.51      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_1634,plain,
% 39.30/5.51      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 39.30/5.51      | v1_relat_1(sK3) ),
% 39.30/5.51      inference(instantiation,[status(thm)],[c_13]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_1635,plain,
% 39.30/5.51      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 39.30/5.51      | v1_relat_1(sK3) = iProver_top ),
% 39.30/5.51      inference(predicate_to_equality,[status(thm)],[c_1634]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_6272,plain,
% 39.30/5.51      ( r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top
% 39.30/5.51      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 39.30/5.51      inference(global_propositional_subsumption,
% 39.30/5.51                [status(thm)],
% 39.30/5.51                [c_6252,c_34,c_1635]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_6273,plain,
% 39.30/5.51      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 39.30/5.51      | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top ),
% 39.30/5.51      inference(renaming,[status(thm)],[c_6272]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_6278,plain,
% 39.30/5.51      ( sK1 = k1_xboole_0
% 39.30/5.51      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 39.30/5.51      | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
% 39.30/5.51      inference(superposition,[status(thm)],[c_3350,c_6273]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_23,plain,
% 39.30/5.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.30/5.51      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.30/5.51      | ~ v1_funct_1(X0) ),
% 39.30/5.51      inference(cnf_transformation,[],[f73]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_1402,plain,
% 39.30/5.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 39.30/5.51      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 39.30/5.51      | v1_funct_1(X0) != iProver_top ),
% 39.30/5.51      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_3678,plain,
% 39.30/5.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 39.30/5.51      | r1_tarski(k2_relat_1(k2_partfun1(X1,X2,X0,X3)),X2) = iProver_top
% 39.30/5.51      | v1_funct_1(X0) != iProver_top ),
% 39.30/5.51      inference(superposition,[status(thm)],[c_1402,c_1396]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_5,plain,
% 39.30/5.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 39.30/5.51      inference(cnf_transformation,[],[f55]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_1411,plain,
% 39.30/5.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 39.30/5.51      | r1_tarski(X0,X1) != iProver_top ),
% 39.30/5.51      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_2,plain,
% 39.30/5.51      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 39.30/5.51      inference(cnf_transformation,[],[f81]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_1405,plain,
% 39.30/5.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 39.30/5.51      | v1_relat_1(X0) = iProver_top ),
% 39.30/5.51      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_2442,plain,
% 39.30/5.51      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 39.30/5.51      | v1_relat_1(X0) = iProver_top ),
% 39.30/5.51      inference(superposition,[status(thm)],[c_2,c_1405]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_2565,plain,
% 39.30/5.51      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 39.30/5.51      | v1_relat_1(X0) = iProver_top ),
% 39.30/5.51      inference(superposition,[status(thm)],[c_1411,c_2442]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_15603,plain,
% 39.30/5.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) != iProver_top
% 39.30/5.51      | v1_funct_1(X0) != iProver_top
% 39.30/5.51      | v1_relat_1(k2_relat_1(k2_partfun1(X1,k1_xboole_0,X0,X2))) = iProver_top ),
% 39.30/5.51      inference(superposition,[status(thm)],[c_3678,c_2565]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_15813,plain,
% 39.30/5.51      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 39.30/5.51      | v1_funct_1(X0) != iProver_top
% 39.30/5.51      | v1_relat_1(k2_relat_1(k2_partfun1(X1,k1_xboole_0,X0,X2))) = iProver_top ),
% 39.30/5.51      inference(demodulation,[status(thm)],[c_15603,c_2]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_2441,plain,
% 39.30/5.51      ( v1_relat_1(sK3) = iProver_top ),
% 39.30/5.51      inference(superposition,[status(thm)],[c_1398,c_1405]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_10,plain,
% 39.30/5.51      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 39.30/5.51      inference(cnf_transformation,[],[f59]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_1408,plain,
% 39.30/5.51      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
% 39.30/5.51      | v1_relat_1(X0) != iProver_top ),
% 39.30/5.51      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_2419,plain,
% 39.30/5.51      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 39.30/5.51      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 39.30/5.51      inference(superposition,[status(thm)],[c_1411,c_1396]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_5597,plain,
% 39.30/5.51      ( r1_tarski(k2_relat_1(k1_relat_1(k7_relat_1(X0,k2_zfmisc_1(X1,X2)))),X2) = iProver_top
% 39.30/5.51      | v1_relat_1(X0) != iProver_top ),
% 39.30/5.51      inference(superposition,[status(thm)],[c_1408,c_2419]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_1,plain,
% 39.30/5.51      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 39.30/5.51      inference(cnf_transformation,[],[f50]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_1412,plain,
% 39.30/5.51      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 39.30/5.51      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_2866,plain,
% 39.30/5.51      ( k1_relat_1(k7_relat_1(X0,k1_xboole_0)) = k1_xboole_0
% 39.30/5.51      | v1_relat_1(X0) != iProver_top ),
% 39.30/5.51      inference(superposition,[status(thm)],[c_1408,c_1412]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_3432,plain,
% 39.30/5.51      ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
% 39.30/5.51      inference(superposition,[status(thm)],[c_2441,c_2866]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_4553,plain,
% 39.30/5.51      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 39.30/5.51      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 39.30/5.51      | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 39.30/5.51      | v1_relat_1(X0) != iProver_top ),
% 39.30/5.51      inference(superposition,[status(thm)],[c_2,c_1403]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_5967,plain,
% 39.30/5.51      ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 39.30/5.51      | r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_xboole_0)),k1_xboole_0) != iProver_top
% 39.30/5.51      | r1_tarski(k1_xboole_0,X0) != iProver_top
% 39.30/5.51      | v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
% 39.30/5.51      inference(superposition,[status(thm)],[c_3432,c_4553]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_1720,plain,
% 39.30/5.51      ( r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X0)
% 39.30/5.51      | ~ v1_relat_1(sK3) ),
% 39.30/5.51      inference(instantiation,[status(thm)],[c_10]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_1721,plain,
% 39.30/5.51      ( r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X0) = iProver_top
% 39.30/5.51      | v1_relat_1(sK3) != iProver_top ),
% 39.30/5.51      inference(predicate_to_equality,[status(thm)],[c_1720]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_1723,plain,
% 39.30/5.51      ( r1_tarski(k1_relat_1(k7_relat_1(sK3,k1_xboole_0)),k1_xboole_0) = iProver_top
% 39.30/5.51      | v1_relat_1(sK3) != iProver_top ),
% 39.30/5.51      inference(instantiation,[status(thm)],[c_1721]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_9,plain,
% 39.30/5.51      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 39.30/5.51      inference(cnf_transformation,[],[f58]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_1717,plain,
% 39.30/5.51      ( v1_relat_1(k7_relat_1(sK3,X0)) | ~ v1_relat_1(sK3) ),
% 39.30/5.51      inference(instantiation,[status(thm)],[c_9]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_1733,plain,
% 39.30/5.51      ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top
% 39.30/5.51      | v1_relat_1(sK3) != iProver_top ),
% 39.30/5.51      inference(predicate_to_equality,[status(thm)],[c_1717]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_1735,plain,
% 39.30/5.51      ( v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = iProver_top
% 39.30/5.51      | v1_relat_1(sK3) != iProver_top ),
% 39.30/5.51      inference(instantiation,[status(thm)],[c_1733]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_25,plain,
% 39.30/5.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.30/5.51      | ~ v1_funct_1(X0)
% 39.30/5.51      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 39.30/5.51      inference(cnf_transformation,[],[f74]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_1400,plain,
% 39.30/5.51      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 39.30/5.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 39.30/5.51      | v1_funct_1(X2) != iProver_top ),
% 39.30/5.51      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_2301,plain,
% 39.30/5.51      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
% 39.30/5.51      | v1_funct_1(sK3) != iProver_top ),
% 39.30/5.51      inference(superposition,[status(thm)],[c_1398,c_1400]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_31,negated_conjecture,
% 39.30/5.51      ( v1_funct_1(sK3) ),
% 39.30/5.51      inference(cnf_transformation,[],[f75]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_1685,plain,
% 39.30/5.51      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 39.30/5.51      | ~ v1_funct_1(sK3)
% 39.30/5.51      | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
% 39.30/5.51      inference(instantiation,[status(thm)],[c_25]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_1843,plain,
% 39.30/5.51      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 39.30/5.51      | ~ v1_funct_1(sK3)
% 39.30/5.51      | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 39.30/5.51      inference(instantiation,[status(thm)],[c_1685]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_2646,plain,
% 39.30/5.51      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 39.30/5.51      inference(global_propositional_subsumption,
% 39.30/5.51                [status(thm)],
% 39.30/5.51                [c_2301,c_31,c_29,c_1843]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_3672,plain,
% 39.30/5.51      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 39.30/5.51      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 39.30/5.51      | v1_funct_1(sK3) != iProver_top ),
% 39.30/5.51      inference(superposition,[status(thm)],[c_2646,c_1402]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_32,plain,
% 39.30/5.51      ( v1_funct_1(sK3) = iProver_top ),
% 39.30/5.51      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_4360,plain,
% 39.30/5.51      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 39.30/5.51      inference(global_propositional_subsumption,
% 39.30/5.51                [status(thm)],
% 39.30/5.51                [c_3672,c_32,c_34]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_4370,plain,
% 39.30/5.51      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) = iProver_top ),
% 39.30/5.51      inference(superposition,[status(thm)],[c_4360,c_1396]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_6254,plain,
% 39.30/5.51      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 39.30/5.51      | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),k1_xboole_0) != iProver_top
% 39.30/5.51      | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
% 39.30/5.51      inference(superposition,[status(thm)],[c_4370,c_4554]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_6269,plain,
% 39.30/5.51      ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 39.30/5.51      | r1_tarski(k1_relat_1(k7_relat_1(sK3,k1_xboole_0)),k1_xboole_0) != iProver_top
% 39.30/5.51      | v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
% 39.30/5.51      inference(instantiation,[status(thm)],[c_6254]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_13150,plain,
% 39.30/5.51      ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 39.30/5.51      inference(global_propositional_subsumption,
% 39.30/5.51                [status(thm)],
% 39.30/5.51                [c_5967,c_34,c_1635,c_1723,c_1735,c_6269]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_1898,plain,
% 39.30/5.51      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 39.30/5.51      | r1_tarski(k2_relat_1(X0),X1) = iProver_top ),
% 39.30/5.51      inference(superposition,[status(thm)],[c_3,c_1396]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_13156,plain,
% 39.30/5.51      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_xboole_0)),X0) = iProver_top ),
% 39.30/5.51      inference(superposition,[status(thm)],[c_13150,c_1898]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_6,plain,
% 39.30/5.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 39.30/5.51      inference(cnf_transformation,[],[f54]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_1410,plain,
% 39.30/5.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 39.30/5.51      | r1_tarski(X0,X1) = iProver_top ),
% 39.30/5.51      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_13155,plain,
% 39.30/5.51      ( r1_tarski(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 39.30/5.51      inference(superposition,[status(thm)],[c_13150,c_1410]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_13385,plain,
% 39.30/5.51      ( k7_relat_1(sK3,k1_xboole_0) = k1_xboole_0 ),
% 39.30/5.51      inference(superposition,[status(thm)],[c_13155,c_1412]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_13544,plain,
% 39.30/5.51      ( r1_tarski(k2_relat_1(k1_xboole_0),X0) = iProver_top ),
% 39.30/5.51      inference(light_normalisation,[status(thm)],[c_13156,c_13385]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_0,plain,
% 39.30/5.51      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 39.30/5.51      inference(cnf_transformation,[],[f49]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_1413,plain,
% 39.30/5.51      ( r1_tarski(X0,X1) != iProver_top
% 39.30/5.51      | r1_tarski(X2,X0) != iProver_top
% 39.30/5.51      | r1_tarski(X2,X1) = iProver_top ),
% 39.30/5.51      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_13551,plain,
% 39.30/5.51      ( r1_tarski(X0,X1) = iProver_top
% 39.30/5.51      | r1_tarski(X0,k2_relat_1(k1_xboole_0)) != iProver_top ),
% 39.30/5.51      inference(superposition,[status(thm)],[c_13544,c_1413]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_14737,plain,
% 39.30/5.51      ( r1_tarski(k1_relat_1(k7_relat_1(X0,k2_relat_1(k1_xboole_0))),X1) = iProver_top
% 39.30/5.51      | v1_relat_1(X0) != iProver_top ),
% 39.30/5.51      inference(superposition,[status(thm)],[c_1408,c_13551]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_21382,plain,
% 39.30/5.51      ( k1_relat_1(k7_relat_1(X0,k2_relat_1(k1_xboole_0))) = k1_xboole_0
% 39.30/5.51      | v1_relat_1(X0) != iProver_top ),
% 39.30/5.51      inference(superposition,[status(thm)],[c_14737,c_1412]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_21630,plain,
% 39.30/5.51      ( k1_relat_1(k7_relat_1(sK3,k2_relat_1(k1_xboole_0))) = k1_xboole_0 ),
% 39.30/5.51      inference(superposition,[status(thm)],[c_2441,c_21382]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_22060,plain,
% 39.30/5.51      ( r1_tarski(k1_xboole_0,k2_relat_1(k1_xboole_0)) = iProver_top
% 39.30/5.51      | v1_relat_1(sK3) != iProver_top ),
% 39.30/5.51      inference(superposition,[status(thm)],[c_21630,c_1408]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_22612,plain,
% 39.30/5.51      ( r1_tarski(k1_xboole_0,k2_relat_1(k1_xboole_0)) = iProver_top ),
% 39.30/5.51      inference(global_propositional_subsumption,
% 39.30/5.51                [status(thm)],
% 39.30/5.51                [c_22060,c_34,c_1635]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_22619,plain,
% 39.30/5.51      ( r1_tarski(X0,k2_relat_1(k1_xboole_0)) = iProver_top
% 39.30/5.51      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 39.30/5.51      inference(superposition,[status(thm)],[c_22612,c_1413]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_23376,plain,
% 39.30/5.51      ( r1_tarski(X0,X1) != iProver_top
% 39.30/5.51      | r1_tarski(X0,k2_relat_1(k1_xboole_0)) = iProver_top
% 39.30/5.51      | r1_tarski(X1,k1_xboole_0) != iProver_top ),
% 39.30/5.51      inference(superposition,[status(thm)],[c_22619,c_1413]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_67613,plain,
% 39.30/5.51      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 39.30/5.51      | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k2_relat_1(k1_xboole_0)) = iProver_top
% 39.30/5.51      | v1_relat_1(X1) != iProver_top ),
% 39.30/5.51      inference(superposition,[status(thm)],[c_1408,c_23376]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_3614,plain,
% 39.30/5.51      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top
% 39.30/5.51      | v1_relat_1(sK3) != iProver_top ),
% 39.30/5.51      inference(superposition,[status(thm)],[c_3432,c_1408]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_3617,plain,
% 39.30/5.51      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 39.30/5.51      inference(global_propositional_subsumption,
% 39.30/5.51                [status(thm)],
% 39.30/5.51                [c_3614,c_34,c_1635]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_1813,plain,
% 39.30/5.51      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 39.30/5.51      | r1_tarski(k2_relat_1(X0),k1_xboole_0) = iProver_top ),
% 39.30/5.51      inference(superposition,[status(thm)],[c_2,c_1396]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_2884,plain,
% 39.30/5.51      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 39.30/5.51      | r1_tarski(k2_relat_1(X0),k1_xboole_0) = iProver_top ),
% 39.30/5.51      inference(superposition,[status(thm)],[c_1411,c_1813]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_7058,plain,
% 39.30/5.51      ( k2_relat_1(X0) = k1_xboole_0
% 39.30/5.51      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 39.30/5.51      inference(superposition,[status(thm)],[c_2884,c_1412]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_7816,plain,
% 39.30/5.51      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 39.30/5.51      inference(superposition,[status(thm)],[c_3617,c_7058]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_118925,plain,
% 39.30/5.51      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 39.30/5.51      | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_xboole_0) = iProver_top
% 39.30/5.51      | v1_relat_1(X1) != iProver_top ),
% 39.30/5.51      inference(light_normalisation,[status(thm)],[c_67613,c_7816]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_118953,plain,
% 39.30/5.51      ( k1_relat_1(k7_relat_1(X0,X1)) = k1_xboole_0
% 39.30/5.51      | r1_tarski(X1,k1_xboole_0) != iProver_top
% 39.30/5.51      | v1_relat_1(X0) != iProver_top ),
% 39.30/5.51      inference(superposition,[status(thm)],[c_118925,c_1412]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_120866,plain,
% 39.30/5.51      ( k1_relat_1(k7_relat_1(X0,k2_relat_1(k1_relat_1(k7_relat_1(X1,k2_zfmisc_1(X2,k1_xboole_0)))))) = k1_xboole_0
% 39.30/5.51      | v1_relat_1(X1) != iProver_top
% 39.30/5.51      | v1_relat_1(X0) != iProver_top ),
% 39.30/5.51      inference(superposition,[status(thm)],[c_5597,c_118953]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_120978,plain,
% 39.30/5.51      ( k1_relat_1(k7_relat_1(X0,k2_relat_1(k1_relat_1(k7_relat_1(X1,k1_xboole_0))))) = k1_xboole_0
% 39.30/5.51      | v1_relat_1(X0) != iProver_top
% 39.30/5.51      | v1_relat_1(X1) != iProver_top ),
% 39.30/5.51      inference(demodulation,[status(thm)],[c_120866,c_2]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_121238,plain,
% 39.30/5.51      ( k1_relat_1(k7_relat_1(sK3,k2_relat_1(k1_relat_1(k7_relat_1(X0,k1_xboole_0))))) = k1_xboole_0
% 39.30/5.51      | v1_relat_1(X0) != iProver_top ),
% 39.30/5.51      inference(superposition,[status(thm)],[c_2441,c_120978]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_121375,plain,
% 39.30/5.51      ( k1_relat_1(k7_relat_1(sK3,k2_relat_1(k1_relat_1(k7_relat_1(k2_relat_1(k2_partfun1(X0,k1_xboole_0,X1,X2)),k1_xboole_0))))) = k1_xboole_0
% 39.30/5.51      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 39.30/5.51      | v1_funct_1(X1) != iProver_top ),
% 39.30/5.51      inference(superposition,[status(thm)],[c_15813,c_121238]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_127619,plain,
% 39.30/5.51      ( k1_relat_1(k7_relat_1(sK3,k2_relat_1(k1_relat_1(k7_relat_1(k2_relat_1(k2_partfun1(X0,k1_xboole_0,sK3,X1)),k1_xboole_0))))) = k1_xboole_0
% 39.30/5.51      | sK1 = k1_xboole_0
% 39.30/5.51      | r1_tarski(sK0,k1_xboole_0) != iProver_top
% 39.30/5.51      | v1_funct_1(sK3) != iProver_top ),
% 39.30/5.51      inference(superposition,[status(thm)],[c_6278,c_121375]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_98,plain,
% 39.30/5.51      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 39.30/5.51      | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 39.30/5.51      inference(instantiation,[status(thm)],[c_5]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_4,plain,
% 39.30/5.51      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 39.30/5.51      | k1_xboole_0 = X0
% 39.30/5.51      | k1_xboole_0 = X1 ),
% 39.30/5.51      inference(cnf_transformation,[],[f51]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_100,plain,
% 39.30/5.51      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 39.30/5.51      | k1_xboole_0 = k1_xboole_0 ),
% 39.30/5.51      inference(instantiation,[status(thm)],[c_4]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_101,plain,
% 39.30/5.51      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 39.30/5.51      inference(instantiation,[status(thm)],[c_3]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_26,negated_conjecture,
% 39.30/5.51      ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
% 39.30/5.51      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 39.30/5.51      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
% 39.30/5.51      inference(cnf_transformation,[],[f80]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_521,plain,
% 39.30/5.51      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 39.30/5.51      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 39.30/5.51      | k2_partfun1(sK0,sK1,sK3,sK2) != sK3
% 39.30/5.51      | sK2 != sK0
% 39.30/5.51      | sK1 != sK1 ),
% 39.30/5.51      inference(resolution_lifted,[status(thm)],[c_26,c_30]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_802,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_1653,plain,
% 39.30/5.51      ( sK2 != X0 | sK2 = sK0 | sK0 != X0 ),
% 39.30/5.51      inference(instantiation,[status(thm)],[c_802]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_1654,plain,
% 39.30/5.51      ( sK2 = sK0 | sK2 != k1_xboole_0 | sK0 != k1_xboole_0 ),
% 39.30/5.51      inference(instantiation,[status(thm)],[c_1653]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_1761,plain,
% 39.30/5.51      ( ~ r1_tarski(sK3,k1_xboole_0) | k1_xboole_0 = sK3 ),
% 39.30/5.51      inference(instantiation,[status(thm)],[c_1]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_1764,plain,
% 39.30/5.51      ( k1_xboole_0 = sK3 | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
% 39.30/5.51      inference(predicate_to_equality,[status(thm)],[c_1761]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_801,plain,( X0 = X0 ),theory(equality) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_1801,plain,
% 39.30/5.51      ( sK3 = sK3 ),
% 39.30/5.51      inference(instantiation,[status(thm)],[c_801]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_1921,plain,
% 39.30/5.51      ( sK1 = sK1 ),
% 39.30/5.51      inference(instantiation,[status(thm)],[c_801]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_1652,plain,
% 39.30/5.51      ( sK0 != X0 | sK0 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 39.30/5.51      inference(instantiation,[status(thm)],[c_802]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_1927,plain,
% 39.30/5.51      ( sK0 != sK0 | sK0 = k1_xboole_0 | k1_xboole_0 != sK0 ),
% 39.30/5.51      inference(instantiation,[status(thm)],[c_1652]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_1928,plain,
% 39.30/5.51      ( sK0 = sK0 ),
% 39.30/5.51      inference(instantiation,[status(thm)],[c_801]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_2017,plain,
% 39.30/5.51      ( ~ r1_tarski(sK0,k1_xboole_0) | k1_xboole_0 = sK0 ),
% 39.30/5.51      inference(instantiation,[status(thm)],[c_1]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_2020,plain,
% 39.30/5.51      ( k1_xboole_0 = sK0 | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
% 39.30/5.51      inference(predicate_to_equality,[status(thm)],[c_2017]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_24,plain,
% 39.30/5.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.30/5.51      | ~ v1_funct_1(X0)
% 39.30/5.51      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
% 39.30/5.51      inference(cnf_transformation,[],[f72]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_1665,plain,
% 39.30/5.51      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 39.30/5.51      | v1_funct_1(k2_partfun1(X0,X1,sK3,X2))
% 39.30/5.51      | ~ v1_funct_1(sK3) ),
% 39.30/5.51      inference(instantiation,[status(thm)],[c_24]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_1838,plain,
% 39.30/5.51      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 39.30/5.51      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
% 39.30/5.51      | ~ v1_funct_1(sK3) ),
% 39.30/5.51      inference(instantiation,[status(thm)],[c_1665]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_2149,plain,
% 39.30/5.51      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 39.30/5.51      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 39.30/5.51      | ~ v1_funct_1(sK3) ),
% 39.30/5.51      inference(instantiation,[status(thm)],[c_1838]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_3615,plain,
% 39.30/5.51      ( r1_tarski(k1_xboole_0,k1_xboole_0) | ~ v1_relat_1(sK3) ),
% 39.30/5.51      inference(predicate_to_equality_rev,[status(thm)],[c_3614]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_2077,plain,
% 39.30/5.51      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 39.30/5.51      inference(instantiation,[status(thm)],[c_802]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_4804,plain,
% 39.30/5.51      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 39.30/5.51      inference(instantiation,[status(thm)],[c_2077]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_4805,plain,
% 39.30/5.51      ( sK3 != sK3 | sK3 = k1_xboole_0 | k1_xboole_0 != sK3 ),
% 39.30/5.51      inference(instantiation,[status(thm)],[c_4804]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_13248,plain,
% 39.30/5.51      ( k2_zfmisc_1(sK2,sK1) = k2_zfmisc_1(sK2,sK1) ),
% 39.30/5.51      inference(instantiation,[status(thm)],[c_801]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_806,plain,
% 39.30/5.51      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 39.30/5.51      theory(equality) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_2268,plain,
% 39.30/5.51      ( m1_subset_1(X0,X1)
% 39.30/5.51      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
% 39.30/5.51      | X0 != X2
% 39.30/5.51      | X1 != k1_zfmisc_1(X3) ),
% 39.30/5.51      inference(instantiation,[status(thm)],[c_806]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_9958,plain,
% 39.30/5.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 39.30/5.51      | m1_subset_1(X2,k1_zfmisc_1(X1))
% 39.30/5.51      | X2 != X0
% 39.30/5.51      | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
% 39.30/5.51      inference(instantiation,[status(thm)],[c_2268]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_16035,plain,
% 39.30/5.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 39.30/5.51      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 39.30/5.51      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 39.30/5.51      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) ),
% 39.30/5.51      inference(instantiation,[status(thm)],[c_9958]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_16037,plain,
% 39.30/5.51      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 39.30/5.51      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 39.30/5.51      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 39.30/5.51      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) ),
% 39.30/5.51      inference(instantiation,[status(thm)],[c_16035]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_22081,plain,
% 39.30/5.51      ( r1_tarski(k1_xboole_0,k2_relat_1(k1_xboole_0))
% 39.30/5.51      | ~ v1_relat_1(sK3) ),
% 39.30/5.51      inference(predicate_to_equality_rev,[status(thm)],[c_22060]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_805,plain,
% 39.30/5.51      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 39.30/5.51      theory(equality) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_27774,plain,
% 39.30/5.51      ( k2_zfmisc_1(sK2,sK1) != k2_zfmisc_1(sK2,sK1)
% 39.30/5.51      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) = k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) ),
% 39.30/5.51      inference(instantiation,[status(thm)],[c_805]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_28350,plain,
% 39.30/5.51      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 39.30/5.51      | ~ v1_funct_1(sK3)
% 39.30/5.51      | k2_partfun1(sK0,sK1,sK3,sK2) = k7_relat_1(sK3,sK2) ),
% 39.30/5.51      inference(instantiation,[status(thm)],[c_1843]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_35150,plain,
% 39.30/5.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(sK2,sK1))))
% 39.30/5.51      | r1_tarski(k2_relat_1(X0),k2_zfmisc_1(sK2,sK1)) ),
% 39.30/5.51      inference(instantiation,[status(thm)],[c_392]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_35156,plain,
% 39.30/5.51      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_zfmisc_1(sK2,sK1))))
% 39.30/5.51      | r1_tarski(k2_relat_1(k1_xboole_0),k2_zfmisc_1(sK2,sK1)) ),
% 39.30/5.51      inference(instantiation,[status(thm)],[c_35150]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_2263,plain,
% 39.30/5.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.30/5.51      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
% 39.30/5.51      inference(instantiation,[status(thm)],[c_5]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_72304,plain,
% 39.30/5.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 39.30/5.51      | ~ r1_tarski(X0,k2_zfmisc_1(sK2,sK1)) ),
% 39.30/5.51      inference(instantiation,[status(thm)],[c_2263]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_72311,plain,
% 39.30/5.51      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 39.30/5.51      | ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(sK2,sK1)) ),
% 39.30/5.51      inference(instantiation,[status(thm)],[c_72304]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_73922,plain,
% 39.30/5.51      ( r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),k1_xboole_0) != iProver_top
% 39.30/5.51      | m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 39.30/5.51      inference(global_propositional_subsumption,
% 39.30/5.51                [status(thm)],
% 39.30/5.51                [c_6254,c_34,c_1635,c_1733]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_73923,plain,
% 39.30/5.51      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 39.30/5.51      | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),k1_xboole_0) != iProver_top ),
% 39.30/5.51      inference(renaming,[status(thm)],[c_73922]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_73933,plain,
% 39.30/5.51      ( m1_subset_1(k7_relat_1(sK3,k2_relat_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 39.30/5.51      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 39.30/5.51      inference(superposition,[status(thm)],[c_21630,c_73923]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_73930,plain,
% 39.30/5.51      ( m1_subset_1(k7_relat_1(sK3,k2_relat_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 39.30/5.51      | v1_relat_1(sK3) != iProver_top ),
% 39.30/5.51      inference(superposition,[status(thm)],[c_14737,c_73923]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_75133,plain,
% 39.30/5.51      ( m1_subset_1(k7_relat_1(sK3,k2_relat_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 39.30/5.51      inference(global_propositional_subsumption,
% 39.30/5.51                [status(thm)],
% 39.30/5.51                [c_73933,c_34,c_1635,c_73930]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_75138,plain,
% 39.30/5.51      ( r1_tarski(k7_relat_1(sK3,k2_relat_1(k1_xboole_0)),k1_xboole_0) = iProver_top ),
% 39.30/5.51      inference(superposition,[status(thm)],[c_75133,c_1410]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_76883,plain,
% 39.30/5.51      ( k7_relat_1(sK3,k2_relat_1(k1_xboole_0)) = k1_xboole_0 ),
% 39.30/5.51      inference(superposition,[status(thm)],[c_75138,c_1412]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_28,negated_conjecture,
% 39.30/5.51      ( r1_tarski(sK2,sK0) ),
% 39.30/5.51      inference(cnf_transformation,[],[f78]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_1399,plain,
% 39.30/5.51      ( r1_tarski(sK2,sK0) = iProver_top ),
% 39.30/5.51      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_67615,plain,
% 39.30/5.51      ( r1_tarski(sK2,k2_relat_1(k1_xboole_0)) = iProver_top
% 39.30/5.51      | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
% 39.30/5.51      inference(superposition,[status(thm)],[c_1399,c_23376]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_12,plain,
% 39.30/5.51      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 39.30/5.51      | ~ v1_relat_1(X1)
% 39.30/5.51      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 39.30/5.51      inference(cnf_transformation,[],[f61]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_1406,plain,
% 39.30/5.51      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 39.30/5.51      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 39.30/5.51      | v1_relat_1(X0) != iProver_top ),
% 39.30/5.51      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_13556,plain,
% 39.30/5.51      ( k1_relat_1(k7_relat_1(X0,k2_relat_1(k1_xboole_0))) = k2_relat_1(k1_xboole_0)
% 39.30/5.51      | v1_relat_1(X0) != iProver_top ),
% 39.30/5.51      inference(superposition,[status(thm)],[c_13544,c_1406]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_14761,plain,
% 39.30/5.51      ( k1_relat_1(k7_relat_1(sK3,k2_relat_1(k1_xboole_0))) = k2_relat_1(k1_xboole_0) ),
% 39.30/5.51      inference(superposition,[status(thm)],[c_2441,c_13556]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_14871,plain,
% 39.30/5.51      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,k2_relat_1(k1_xboole_0)),X0)) = X0
% 39.30/5.51      | r1_tarski(X0,k2_relat_1(k1_xboole_0)) != iProver_top
% 39.30/5.51      | v1_relat_1(k7_relat_1(sK3,k2_relat_1(k1_xboole_0))) != iProver_top ),
% 39.30/5.51      inference(superposition,[status(thm)],[c_14761,c_1406]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_4369,plain,
% 39.30/5.51      ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 39.30/5.51      inference(superposition,[status(thm)],[c_4360,c_1405]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_15005,plain,
% 39.30/5.51      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,k2_relat_1(k1_xboole_0)),X0)) = X0
% 39.30/5.51      | r1_tarski(X0,k2_relat_1(k1_xboole_0)) != iProver_top ),
% 39.30/5.51      inference(forward_subsumption_resolution,
% 39.30/5.51                [status(thm)],
% 39.30/5.51                [c_14871,c_4369]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_68369,plain,
% 39.30/5.51      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,k2_relat_1(k1_xboole_0)),sK2)) = sK2
% 39.30/5.51      | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
% 39.30/5.51      inference(superposition,[status(thm)],[c_67615,c_15005]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_76937,plain,
% 39.30/5.51      ( k1_relat_1(k7_relat_1(k1_xboole_0,sK2)) = sK2
% 39.30/5.51      | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
% 39.30/5.51      inference(demodulation,[status(thm)],[c_76883,c_68369]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_3622,plain,
% 39.30/5.51      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 39.30/5.51      inference(superposition,[status(thm)],[c_3617,c_2565]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_11,plain,
% 39.30/5.51      ( r1_tarski(k7_relat_1(X0,X1),X0) | ~ v1_relat_1(X0) ),
% 39.30/5.51      inference(cnf_transformation,[],[f60]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_1407,plain,
% 39.30/5.51      ( r1_tarski(k7_relat_1(X0,X1),X0) = iProver_top
% 39.30/5.51      | v1_relat_1(X0) != iProver_top ),
% 39.30/5.51      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_2210,plain,
% 39.30/5.51      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0
% 39.30/5.51      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 39.30/5.51      inference(superposition,[status(thm)],[c_1407,c_1412]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_3641,plain,
% 39.30/5.51      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 39.30/5.51      inference(superposition,[status(thm)],[c_3622,c_2210]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_3640,plain,
% 39.30/5.51      ( k1_relat_1(k7_relat_1(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
% 39.30/5.51      inference(superposition,[status(thm)],[c_3622,c_2866]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_3644,plain,
% 39.30/5.51      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 39.30/5.51      inference(demodulation,[status(thm)],[c_3640,c_3641]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_76999,plain,
% 39.30/5.51      ( sK2 = k1_xboole_0 | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
% 39.30/5.51      inference(demodulation,[status(thm)],[c_76937,c_3641,c_3644]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_88262,plain,
% 39.30/5.51      ( m1_subset_1(X0,X1)
% 39.30/5.51      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
% 39.30/5.51      | X0 != X2
% 39.30/5.51      | X1 != k1_zfmisc_1(X3) ),
% 39.30/5.51      inference(instantiation,[status(thm)],[c_806]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_88836,plain,
% 39.30/5.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 39.30/5.51      | m1_subset_1(X2,k1_zfmisc_1(X3))
% 39.30/5.51      | X2 != X0
% 39.30/5.51      | k1_zfmisc_1(X3) != k1_zfmisc_1(X1) ),
% 39.30/5.51      inference(instantiation,[status(thm)],[c_88262]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_91181,plain,
% 39.30/5.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 39.30/5.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,k2_zfmisc_1(sK2,sK1))))
% 39.30/5.51      | X2 != X0
% 39.30/5.51      | k1_zfmisc_1(k2_zfmisc_1(X3,k2_zfmisc_1(sK2,sK1))) != k1_zfmisc_1(X1) ),
% 39.30/5.51      inference(instantiation,[status(thm)],[c_88836]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_91183,plain,
% 39.30/5.51      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_zfmisc_1(sK2,sK1))))
% 39.30/5.51      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 39.30/5.51      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_zfmisc_1(sK2,sK1))) != k1_zfmisc_1(k1_xboole_0)
% 39.30/5.51      | k1_xboole_0 != k1_xboole_0 ),
% 39.30/5.51      inference(instantiation,[status(thm)],[c_91181]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_89320,plain,
% 39.30/5.51      ( X0 != X1
% 39.30/5.51      | k2_partfun1(sK0,sK1,sK3,sK2) != X1
% 39.30/5.51      | k2_partfun1(sK0,sK1,sK3,sK2) = X0 ),
% 39.30/5.51      inference(instantiation,[status(thm)],[c_802]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_91302,plain,
% 39.30/5.51      ( X0 != k7_relat_1(sK3,sK2)
% 39.30/5.51      | k2_partfun1(sK0,sK1,sK3,sK2) = X0
% 39.30/5.51      | k2_partfun1(sK0,sK1,sK3,sK2) != k7_relat_1(sK3,sK2) ),
% 39.30/5.51      inference(instantiation,[status(thm)],[c_89320]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_91303,plain,
% 39.30/5.51      ( k2_partfun1(sK0,sK1,sK3,sK2) != k7_relat_1(sK3,sK2)
% 39.30/5.51      | k2_partfun1(sK0,sK1,sK3,sK2) = k1_xboole_0
% 39.30/5.51      | k1_xboole_0 != k7_relat_1(sK3,sK2) ),
% 39.30/5.51      inference(instantiation,[status(thm)],[c_91302]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_94719,plain,
% 39.30/5.51      ( ~ r1_tarski(k7_relat_1(sK3,sK2),k1_xboole_0)
% 39.30/5.51      | k1_xboole_0 = k7_relat_1(sK3,sK2) ),
% 39.30/5.51      inference(instantiation,[status(thm)],[c_1]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_94720,plain,
% 39.30/5.51      ( k1_xboole_0 = k7_relat_1(sK3,sK2)
% 39.30/5.51      | r1_tarski(k7_relat_1(sK3,sK2),k1_xboole_0) != iProver_top ),
% 39.30/5.51      inference(predicate_to_equality,[status(thm)],[c_94719]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_95587,plain,
% 39.30/5.51      ( k2_zfmisc_1(X0,k2_zfmisc_1(sK2,sK1)) != X1
% 39.30/5.51      | k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(sK2,sK1))) = k1_zfmisc_1(X1) ),
% 39.30/5.51      inference(instantiation,[status(thm)],[c_805]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_95588,plain,
% 39.30/5.51      ( k2_zfmisc_1(k1_xboole_0,k2_zfmisc_1(sK2,sK1)) != k1_xboole_0
% 39.30/5.51      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_zfmisc_1(sK2,sK1))) = k1_zfmisc_1(k1_xboole_0) ),
% 39.30/5.51      inference(instantiation,[status(thm)],[c_95587]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_2330,plain,
% 39.30/5.51      ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 39.30/5.51      inference(superposition,[status(thm)],[c_1398,c_1410]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_68365,plain,
% 39.30/5.51      ( r1_tarski(X0,k2_relat_1(k1_xboole_0)) = iProver_top
% 39.30/5.51      | r1_tarski(X0,sK2) != iProver_top
% 39.30/5.51      | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
% 39.30/5.51      inference(superposition,[status(thm)],[c_67615,c_1413]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_69336,plain,
% 39.30/5.51      ( r1_tarski(X0,X1) != iProver_top
% 39.30/5.51      | r1_tarski(X0,k2_relat_1(k1_xboole_0)) = iProver_top
% 39.30/5.51      | r1_tarski(X1,sK2) != iProver_top
% 39.30/5.51      | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
% 39.30/5.51      inference(superposition,[status(thm)],[c_68365,c_1413]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_75538,plain,
% 39.30/5.51      ( r1_tarski(k2_zfmisc_1(sK0,sK1),sK2) != iProver_top
% 39.30/5.51      | r1_tarski(sK3,k2_relat_1(k1_xboole_0)) = iProver_top
% 39.30/5.51      | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
% 39.30/5.51      inference(superposition,[status(thm)],[c_2330,c_69336]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_102872,plain,
% 39.30/5.51      ( r1_tarski(k2_zfmisc_1(sK0,sK1),sK2) != iProver_top
% 39.30/5.51      | r1_tarski(sK3,k1_xboole_0) = iProver_top
% 39.30/5.51      | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
% 39.30/5.51      inference(demodulation,[status(thm)],[c_7816,c_75538]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_6317,plain,
% 39.30/5.51      ( sK1 = k1_xboole_0
% 39.30/5.51      | r1_tarski(sK3,k1_xboole_0) = iProver_top
% 39.30/5.51      | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
% 39.30/5.51      inference(superposition,[status(thm)],[c_6278,c_1410]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_803,plain,
% 39.30/5.51      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 39.30/5.51      theory(equality) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_9451,plain,
% 39.30/5.51      ( ~ r1_tarski(X0,X1)
% 39.30/5.51      | r1_tarski(sK1,k1_xboole_0)
% 39.30/5.51      | sK1 != X0
% 39.30/5.51      | k1_xboole_0 != X1 ),
% 39.30/5.51      inference(instantiation,[status(thm)],[c_803]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_9452,plain,
% 39.30/5.51      ( sK1 != X0
% 39.30/5.51      | k1_xboole_0 != X1
% 39.30/5.51      | r1_tarski(X0,X1) != iProver_top
% 39.30/5.51      | r1_tarski(sK1,k1_xboole_0) = iProver_top ),
% 39.30/5.51      inference(predicate_to_equality,[status(thm)],[c_9451]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_9454,plain,
% 39.30/5.51      ( sK1 != k1_xboole_0
% 39.30/5.51      | k1_xboole_0 != k1_xboole_0
% 39.30/5.51      | r1_tarski(sK1,k1_xboole_0) = iProver_top
% 39.30/5.51      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 39.30/5.51      inference(instantiation,[status(thm)],[c_9452]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_67620,plain,
% 39.30/5.51      ( r1_tarski(k2_relat_1(sK3),k2_relat_1(k1_xboole_0)) = iProver_top
% 39.30/5.51      | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
% 39.30/5.51      inference(superposition,[status(thm)],[c_1810,c_23376]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_68826,plain,
% 39.30/5.51      ( r1_tarski(k2_relat_1(sK3),X0) = iProver_top
% 39.30/5.51      | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
% 39.30/5.51      inference(superposition,[status(thm)],[c_67620,c_13551]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_4555,plain,
% 39.30/5.51      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) = iProver_top
% 39.30/5.51      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 39.30/5.51      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 39.30/5.51      | v1_relat_1(X0) != iProver_top ),
% 39.30/5.51      inference(superposition,[status(thm)],[c_1403,c_1410]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_25363,plain,
% 39.30/5.51      ( r1_tarski(X0,k1_xboole_0) = iProver_top
% 39.30/5.51      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 39.30/5.51      | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 39.30/5.51      | v1_relat_1(X0) != iProver_top ),
% 39.30/5.51      inference(superposition,[status(thm)],[c_2,c_4555]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_25476,plain,
% 39.30/5.51      ( sK1 = k1_xboole_0
% 39.30/5.51      | r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top
% 39.30/5.51      | r1_tarski(sK3,k1_xboole_0) = iProver_top
% 39.30/5.51      | r1_tarski(sK0,X0) != iProver_top
% 39.30/5.51      | v1_relat_1(sK3) != iProver_top ),
% 39.30/5.51      inference(superposition,[status(thm)],[c_3350,c_25363]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_27633,plain,
% 39.30/5.51      ( r1_tarski(sK0,X0) != iProver_top
% 39.30/5.51      | r1_tarski(sK3,k1_xboole_0) = iProver_top
% 39.30/5.51      | r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top
% 39.30/5.51      | sK1 = k1_xboole_0 ),
% 39.30/5.51      inference(global_propositional_subsumption,
% 39.30/5.51                [status(thm)],
% 39.30/5.51                [c_25476,c_34,c_1635]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_27634,plain,
% 39.30/5.51      ( sK1 = k1_xboole_0
% 39.30/5.51      | r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top
% 39.30/5.51      | r1_tarski(sK3,k1_xboole_0) = iProver_top
% 39.30/5.51      | r1_tarski(sK0,X0) != iProver_top ),
% 39.30/5.51      inference(renaming,[status(thm)],[c_27633]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_69856,plain,
% 39.30/5.51      ( sK1 = k1_xboole_0
% 39.30/5.51      | r1_tarski(sK3,k1_xboole_0) = iProver_top
% 39.30/5.51      | r1_tarski(sK1,k1_xboole_0) != iProver_top
% 39.30/5.51      | r1_tarski(sK0,X0) != iProver_top ),
% 39.30/5.51      inference(superposition,[status(thm)],[c_68826,c_27634]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_1627,plain,
% 39.30/5.51      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 39.30/5.51      | r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
% 39.30/5.51      inference(instantiation,[status(thm)],[c_6]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_1628,plain,
% 39.30/5.51      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 39.30/5.51      | r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 39.30/5.51      inference(predicate_to_equality,[status(thm)],[c_1627]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_18,plain,
% 39.30/5.51      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 39.30/5.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 39.30/5.51      | k1_xboole_0 = X1
% 39.30/5.51      | k1_xboole_0 = X0 ),
% 39.30/5.51      inference(cnf_transformation,[],[f85]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_442,plain,
% 39.30/5.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 39.30/5.51      | sK3 != X0
% 39.30/5.51      | sK1 != k1_xboole_0
% 39.30/5.51      | sK0 != X1
% 39.30/5.51      | k1_xboole_0 = X0
% 39.30/5.51      | k1_xboole_0 = X1 ),
% 39.30/5.51      inference(resolution_lifted,[status(thm)],[c_18,c_30]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_443,plain,
% 39.30/5.51      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
% 39.30/5.51      | sK1 != k1_xboole_0
% 39.30/5.51      | k1_xboole_0 = sK3
% 39.30/5.51      | k1_xboole_0 = sK0 ),
% 39.30/5.51      inference(unflattening,[status(thm)],[c_442]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_1394,plain,
% 39.30/5.51      ( sK1 != k1_xboole_0
% 39.30/5.51      | k1_xboole_0 = sK3
% 39.30/5.51      | k1_xboole_0 = sK0
% 39.30/5.51      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
% 39.30/5.51      inference(predicate_to_equality,[status(thm)],[c_443]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_1493,plain,
% 39.30/5.51      ( sK3 = k1_xboole_0
% 39.30/5.51      | sK1 != k1_xboole_0
% 39.30/5.51      | sK0 = k1_xboole_0
% 39.30/5.51      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 39.30/5.51      inference(demodulation,[status(thm)],[c_1394,c_2]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_27,negated_conjecture,
% 39.30/5.51      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 39.30/5.51      inference(cnf_transformation,[],[f79]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_2031,plain,
% 39.30/5.51      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 39.30/5.51      inference(instantiation,[status(thm)],[c_802]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_2032,plain,
% 39.30/5.51      ( sK1 != k1_xboole_0
% 39.30/5.51      | k1_xboole_0 = sK1
% 39.30/5.51      | k1_xboole_0 != k1_xboole_0 ),
% 39.30/5.51      inference(instantiation,[status(thm)],[c_2031]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_2069,plain,
% 39.30/5.51      ( sK0 = k1_xboole_0 | sK1 != k1_xboole_0 ),
% 39.30/5.51      inference(global_propositional_subsumption,
% 39.30/5.51                [status(thm)],
% 39.30/5.51                [c_1493,c_27,c_100,c_101,c_1927,c_1928,c_2032]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_2070,plain,
% 39.30/5.51      ( sK1 != k1_xboole_0 | sK0 = k1_xboole_0 ),
% 39.30/5.51      inference(renaming,[status(thm)],[c_2069]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_1705,plain,
% 39.30/5.51      ( r1_tarski(X0,X1)
% 39.30/5.51      | ~ r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))
% 39.30/5.51      | X1 != k2_zfmisc_1(sK0,sK1)
% 39.30/5.51      | X0 != sK3 ),
% 39.30/5.51      inference(instantiation,[status(thm)],[c_803]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_2100,plain,
% 39.30/5.51      ( r1_tarski(sK3,X0)
% 39.30/5.51      | ~ r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))
% 39.30/5.51      | X0 != k2_zfmisc_1(sK0,sK1)
% 39.30/5.51      | sK3 != sK3 ),
% 39.30/5.51      inference(instantiation,[status(thm)],[c_1705]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_2101,plain,
% 39.30/5.51      ( X0 != k2_zfmisc_1(sK0,sK1)
% 39.30/5.51      | sK3 != sK3
% 39.30/5.51      | r1_tarski(sK3,X0) = iProver_top
% 39.30/5.51      | r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) != iProver_top ),
% 39.30/5.51      inference(predicate_to_equality,[status(thm)],[c_2100]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_2103,plain,
% 39.30/5.51      ( sK3 != sK3
% 39.30/5.51      | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
% 39.30/5.51      | r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) != iProver_top
% 39.30/5.51      | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 39.30/5.51      inference(instantiation,[status(thm)],[c_2101]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_2897,plain,
% 39.30/5.51      ( X0 != X1
% 39.30/5.51      | X0 = k2_zfmisc_1(sK0,sK1)
% 39.30/5.51      | k2_zfmisc_1(sK0,sK1) != X1 ),
% 39.30/5.51      inference(instantiation,[status(thm)],[c_802]) ).
% 39.30/5.51  
% 39.30/5.51  cnf(c_2898,plain,
% 39.30/5.51      ( k2_zfmisc_1(sK0,sK1) != k1_xboole_0
% 39.30/5.51      | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
% 39.30/5.51      | k1_xboole_0 != k1_xboole_0 ),
% 39.30/5.52      inference(instantiation,[status(thm)],[c_2897]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_804,plain,
% 39.30/5.52      ( X0 != X1 | X2 != X3 | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
% 39.30/5.52      theory(equality) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_10843,plain,
% 39.30/5.52      ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(X0,X1)
% 39.30/5.52      | sK1 != X1
% 39.30/5.52      | sK0 != X0 ),
% 39.30/5.52      inference(instantiation,[status(thm)],[c_804]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_10845,plain,
% 39.30/5.52      ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
% 39.30/5.52      | sK1 != k1_xboole_0
% 39.30/5.52      | sK0 != k1_xboole_0 ),
% 39.30/5.52      inference(instantiation,[status(thm)],[c_10843]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_11613,plain,
% 39.30/5.52      ( k2_zfmisc_1(X0,X1) != X2
% 39.30/5.52      | k1_xboole_0 != X2
% 39.30/5.52      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ),
% 39.30/5.52      inference(instantiation,[status(thm)],[c_802]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_11614,plain,
% 39.30/5.52      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 39.30/5.52      | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
% 39.30/5.52      | k1_xboole_0 != k1_xboole_0 ),
% 39.30/5.52      inference(instantiation,[status(thm)],[c_11613]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_3899,plain,
% 39.30/5.52      ( r1_tarski(X0,k2_zfmisc_1(sK0,sK1)) = iProver_top
% 39.30/5.52      | r1_tarski(X0,sK3) != iProver_top ),
% 39.30/5.52      inference(superposition,[status(thm)],[c_2330,c_1413]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_4559,plain,
% 39.30/5.52      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 39.30/5.52      | r1_tarski(k1_relat_1(X2),X0) != iProver_top
% 39.30/5.52      | r1_tarski(k2_relat_1(X2),X1) != iProver_top
% 39.30/5.52      | v1_relat_1(X2) != iProver_top ),
% 39.30/5.52      inference(superposition,[status(thm)],[c_1403,c_1404]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_29866,plain,
% 39.30/5.52      ( k1_relset_1(k2_zfmisc_1(sK0,sK1),X0,X1) = k1_relat_1(X1)
% 39.30/5.52      | r1_tarski(k1_relat_1(X1),sK3) != iProver_top
% 39.30/5.52      | r1_tarski(k2_relat_1(X1),X0) != iProver_top
% 39.30/5.52      | v1_relat_1(X1) != iProver_top ),
% 39.30/5.52      inference(superposition,[status(thm)],[c_3899,c_4559]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_68824,plain,
% 39.30/5.52      ( k1_relset_1(k2_zfmisc_1(sK0,sK1),k2_relat_1(k1_xboole_0),sK3) = k1_relat_1(sK3)
% 39.30/5.52      | r1_tarski(k1_relat_1(sK3),sK3) != iProver_top
% 39.30/5.52      | r1_tarski(sK1,k1_xboole_0) != iProver_top
% 39.30/5.52      | v1_relat_1(sK3) != iProver_top ),
% 39.30/5.52      inference(superposition,[status(thm)],[c_67620,c_29866]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_79449,plain,
% 39.30/5.52      ( r1_tarski(sK1,k1_xboole_0) != iProver_top
% 39.30/5.52      | r1_tarski(k1_relat_1(sK3),sK3) != iProver_top
% 39.30/5.52      | k1_relset_1(k2_zfmisc_1(sK0,sK1),k2_relat_1(k1_xboole_0),sK3) = k1_relat_1(sK3) ),
% 39.30/5.52      inference(global_propositional_subsumption,
% 39.30/5.52                [status(thm)],
% 39.30/5.52                [c_68824,c_34,c_1635]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_79450,plain,
% 39.30/5.52      ( k1_relset_1(k2_zfmisc_1(sK0,sK1),k2_relat_1(k1_xboole_0),sK3) = k1_relat_1(sK3)
% 39.30/5.52      | r1_tarski(k1_relat_1(sK3),sK3) != iProver_top
% 39.30/5.52      | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
% 39.30/5.52      inference(renaming,[status(thm)],[c_79449]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_79456,plain,
% 39.30/5.52      ( k1_relset_1(k2_zfmisc_1(sK0,sK1),k2_relat_1(k1_xboole_0),sK3) = k1_relat_1(sK3)
% 39.30/5.52      | sK1 = k1_xboole_0
% 39.30/5.52      | r1_tarski(sK1,k1_xboole_0) != iProver_top
% 39.30/5.52      | r1_tarski(sK0,sK3) != iProver_top ),
% 39.30/5.52      inference(superposition,[status(thm)],[c_3350,c_79450]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_1650,plain,
% 39.30/5.52      ( sK1 != X0 | sK1 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 39.30/5.52      inference(instantiation,[status(thm)],[c_802]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_1920,plain,
% 39.30/5.52      ( sK1 != sK1 | sK1 = k1_xboole_0 | k1_xboole_0 != sK1 ),
% 39.30/5.52      inference(instantiation,[status(thm)],[c_1650]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_2028,plain,
% 39.30/5.52      ( ~ r1_tarski(sK1,k1_xboole_0) | k1_xboole_0 = sK1 ),
% 39.30/5.52      inference(instantiation,[status(thm)],[c_1]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_2029,plain,
% 39.30/5.52      ( k1_xboole_0 = sK1 | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
% 39.30/5.52      inference(predicate_to_equality,[status(thm)],[c_2028]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_79698,plain,
% 39.30/5.52      ( r1_tarski(sK1,k1_xboole_0) != iProver_top | sK1 = k1_xboole_0 ),
% 39.30/5.52      inference(global_propositional_subsumption,
% 39.30/5.52                [status(thm)],
% 39.30/5.52                [c_79456,c_1920,c_1921,c_2029]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_79699,plain,
% 39.30/5.52      ( sK1 = k1_xboole_0 | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
% 39.30/5.52      inference(renaming,[status(thm)],[c_79698]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_91585,plain,
% 39.30/5.52      ( k2_zfmisc_1(sK0,sK1) != X0
% 39.30/5.52      | k2_zfmisc_1(sK0,sK1) = k1_xboole_0
% 39.30/5.52      | k1_xboole_0 != X0 ),
% 39.30/5.52      inference(instantiation,[status(thm)],[c_802]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_91922,plain,
% 39.30/5.52      ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X0,X1)
% 39.30/5.52      | k2_zfmisc_1(sK0,sK1) = k1_xboole_0
% 39.30/5.52      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ),
% 39.30/5.52      inference(instantiation,[status(thm)],[c_91585]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_91924,plain,
% 39.30/5.52      ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
% 39.30/5.52      | k2_zfmisc_1(sK0,sK1) = k1_xboole_0
% 39.30/5.52      | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0) ),
% 39.30/5.52      inference(instantiation,[status(thm)],[c_91922]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_92262,plain,
% 39.30/5.52      ( r1_tarski(sK1,k1_xboole_0) != iProver_top
% 39.30/5.52      | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 39.30/5.52      inference(global_propositional_subsumption,
% 39.30/5.52                [status(thm)],
% 39.30/5.52                [c_69856,c_34,c_100,c_101,c_1628,c_1801,c_2070,c_2103,
% 39.30/5.52                 c_2898,c_10845,c_11614,c_79699,c_91924]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_92263,plain,
% 39.30/5.52      ( r1_tarski(sK3,k1_xboole_0) = iProver_top
% 39.30/5.52      | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
% 39.30/5.52      inference(renaming,[status(thm)],[c_92262]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_104774,plain,
% 39.30/5.52      ( r1_tarski(sK3,k1_xboole_0) = iProver_top
% 39.30/5.52      | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
% 39.30/5.52      inference(global_propositional_subsumption,
% 39.30/5.52                [status(thm)],
% 39.30/5.52                [c_102872,c_34,c_100,c_101,c_1635,c_3614,c_6317,c_9454,
% 39.30/5.52                 c_92263]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_114471,plain,
% 39.30/5.52      ( k2_zfmisc_1(k1_xboole_0,k2_zfmisc_1(sK2,sK1)) = k1_xboole_0 ),
% 39.30/5.52      inference(instantiation,[status(thm)],[c_3]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_89270,plain,
% 39.30/5.52      ( ~ r1_tarski(X0,X1)
% 39.30/5.52      | ~ r1_tarski(X1,k2_zfmisc_1(sK2,sK1))
% 39.30/5.52      | r1_tarski(X0,k2_zfmisc_1(sK2,sK1)) ),
% 39.30/5.52      inference(instantiation,[status(thm)],[c_0]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_124225,plain,
% 39.30/5.52      ( r1_tarski(X0,k2_zfmisc_1(sK2,sK1))
% 39.30/5.52      | ~ r1_tarski(X0,k2_relat_1(X1))
% 39.30/5.52      | ~ r1_tarski(k2_relat_1(X1),k2_zfmisc_1(sK2,sK1)) ),
% 39.30/5.52      inference(instantiation,[status(thm)],[c_89270]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_124227,plain,
% 39.30/5.52      ( ~ r1_tarski(k2_relat_1(k1_xboole_0),k2_zfmisc_1(sK2,sK1))
% 39.30/5.52      | r1_tarski(k1_xboole_0,k2_zfmisc_1(sK2,sK1))
% 39.30/5.52      | ~ r1_tarski(k1_xboole_0,k2_relat_1(k1_xboole_0)) ),
% 39.30/5.52      inference(instantiation,[status(thm)],[c_124225]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_4008,plain,
% 39.30/5.52      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 39.30/5.52      | sK1 = k1_xboole_0
% 39.30/5.52      | r1_tarski(X0,sK0) != iProver_top
% 39.30/5.52      | v1_relat_1(sK3) != iProver_top ),
% 39.30/5.52      inference(superposition,[status(thm)],[c_3350,c_1406]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_4406,plain,
% 39.30/5.52      ( r1_tarski(X0,sK0) != iProver_top
% 39.30/5.52      | sK1 = k1_xboole_0
% 39.30/5.52      | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
% 39.30/5.52      inference(global_propositional_subsumption,
% 39.30/5.52                [status(thm)],
% 39.30/5.52                [c_4008,c_34,c_1635]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_4407,plain,
% 39.30/5.52      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 39.30/5.52      | sK1 = k1_xboole_0
% 39.30/5.52      | r1_tarski(X0,sK0) != iProver_top ),
% 39.30/5.52      inference(renaming,[status(thm)],[c_4406]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_4415,plain,
% 39.30/5.52      ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2 | sK1 = k1_xboole_0 ),
% 39.30/5.52      inference(superposition,[status(thm)],[c_1399,c_4407]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_4527,plain,
% 39.30/5.52      ( sK1 = k1_xboole_0
% 39.30/5.52      | r1_tarski(sK2,sK2) = iProver_top
% 39.30/5.52      | v1_relat_1(sK3) != iProver_top ),
% 39.30/5.52      inference(superposition,[status(thm)],[c_4415,c_1408]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_5032,plain,
% 39.30/5.52      ( r1_tarski(sK2,sK2) = iProver_top | sK1 = k1_xboole_0 ),
% 39.30/5.52      inference(global_propositional_subsumption,
% 39.30/5.52                [status(thm)],
% 39.30/5.52                [c_4527,c_34,c_1635]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_5033,plain,
% 39.30/5.52      ( sK1 = k1_xboole_0 | r1_tarski(sK2,sK2) = iProver_top ),
% 39.30/5.52      inference(renaming,[status(thm)],[c_5032]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_3897,plain,
% 39.30/5.52      ( r1_tarski(X0,sK2) != iProver_top
% 39.30/5.52      | r1_tarski(X0,sK0) = iProver_top ),
% 39.30/5.52      inference(superposition,[status(thm)],[c_1399,c_1413]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_4049,plain,
% 39.30/5.52      ( r1_tarski(k1_relat_1(k7_relat_1(X0,sK2)),sK0) = iProver_top
% 39.30/5.52      | v1_relat_1(X0) != iProver_top ),
% 39.30/5.52      inference(superposition,[status(thm)],[c_1408,c_3897]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_4416,plain,
% 39.30/5.52      ( k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(X0,sK2)))) = k1_relat_1(k7_relat_1(X0,sK2))
% 39.30/5.52      | sK1 = k1_xboole_0
% 39.30/5.52      | v1_relat_1(X0) != iProver_top ),
% 39.30/5.52      inference(superposition,[status(thm)],[c_4049,c_4407]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_18662,plain,
% 39.30/5.52      ( k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,sK2)))) = k1_relat_1(k7_relat_1(sK3,sK2))
% 39.30/5.52      | sK1 = k1_xboole_0 ),
% 39.30/5.52      inference(superposition,[status(thm)],[c_2441,c_4416]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_29879,plain,
% 39.30/5.52      ( k1_relset_1(X0,X1,k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,sK2)))) = k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,sK2))))
% 39.30/5.52      | sK1 = k1_xboole_0
% 39.30/5.52      | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
% 39.30/5.52      | r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,sK2)))),X1) != iProver_top
% 39.30/5.52      | v1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,sK2)))) != iProver_top ),
% 39.30/5.52      inference(superposition,[status(thm)],[c_18662,c_4559]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_119902,plain,
% 39.30/5.52      ( k1_relset_1(X0,X1,k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,sK2)))) = k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,sK2))))
% 39.30/5.52      | sK1 = k1_xboole_0
% 39.30/5.52      | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
% 39.30/5.52      | r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,sK2)))),X1) != iProver_top ),
% 39.30/5.52      inference(forward_subsumption_resolution,
% 39.30/5.52                [status(thm)],
% 39.30/5.52                [c_29879,c_4369]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_119920,plain,
% 39.30/5.52      ( k1_relset_1(X0,X1,k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,sK2)))) = k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,sK2))))
% 39.30/5.52      | sK1 = k1_xboole_0
% 39.30/5.52      | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
% 39.30/5.52      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1) != iProver_top ),
% 39.30/5.52      inference(superposition,[status(thm)],[c_4415,c_119902]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_120087,plain,
% 39.30/5.52      ( k1_relset_1(X0,X1,k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,sK2)))) = k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,sK2))))
% 39.30/5.52      | sK1 = k1_xboole_0
% 39.30/5.52      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1) != iProver_top
% 39.30/5.52      | r1_tarski(sK2,X0) != iProver_top ),
% 39.30/5.52      inference(superposition,[status(thm)],[c_4415,c_119920]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_120248,plain,
% 39.30/5.52      ( k1_relset_1(X0,sK1,k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,sK2)))) = k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,sK2))))
% 39.30/5.52      | sK1 = k1_xboole_0
% 39.30/5.52      | r1_tarski(sK2,X0) != iProver_top ),
% 39.30/5.52      inference(superposition,[status(thm)],[c_4370,c_120087]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_120418,plain,
% 39.30/5.52      ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,sK2)))) = k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,sK2))))
% 39.30/5.52      | sK1 = k1_xboole_0 ),
% 39.30/5.52      inference(superposition,[status(thm)],[c_5033,c_120248]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_120488,plain,
% 39.30/5.52      ( k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,sK2)))) = k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2))
% 39.30/5.52      | sK1 = k1_xboole_0 ),
% 39.30/5.52      inference(superposition,[status(thm)],[c_4415,c_120418]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_121552,plain,
% 39.30/5.52      ( sK1 = k1_xboole_0
% 39.30/5.52      | r1_tarski(k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)),k1_relat_1(k7_relat_1(sK3,sK2))) = iProver_top
% 39.30/5.52      | v1_relat_1(sK3) != iProver_top ),
% 39.30/5.52      inference(superposition,[status(thm)],[c_120488,c_1408]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_131007,plain,
% 39.30/5.52      ( r1_tarski(k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)),k1_relat_1(k7_relat_1(sK3,sK2))) = iProver_top
% 39.30/5.52      | sK1 = k1_xboole_0 ),
% 39.30/5.52      inference(global_propositional_subsumption,
% 39.30/5.52                [status(thm)],
% 39.30/5.52                [c_121552,c_34,c_1635]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_131008,plain,
% 39.30/5.52      ( sK1 = k1_xboole_0
% 39.30/5.52      | r1_tarski(k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)),k1_relat_1(k7_relat_1(sK3,sK2))) = iProver_top ),
% 39.30/5.52      inference(renaming,[status(thm)],[c_131007]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_131014,plain,
% 39.30/5.52      ( sK1 = k1_xboole_0
% 39.30/5.52      | r1_tarski(k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)),sK2) = iProver_top ),
% 39.30/5.52      inference(superposition,[status(thm)],[c_4415,c_131008]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_69358,plain,
% 39.30/5.52      ( r1_tarski(X0,X1) = iProver_top
% 39.30/5.52      | r1_tarski(X0,sK2) != iProver_top
% 39.30/5.52      | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
% 39.30/5.52      inference(superposition,[status(thm)],[c_68365,c_13551]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_131142,plain,
% 39.30/5.52      ( sK1 = k1_xboole_0
% 39.30/5.52      | r1_tarski(k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)),X0) = iProver_top
% 39.30/5.52      | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
% 39.30/5.52      inference(superposition,[status(thm)],[c_131014,c_69358]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_121570,plain,
% 39.30/5.52      ( sK1 = k1_xboole_0
% 39.30/5.52      | m1_subset_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,sK2))),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 39.30/5.52      | r1_tarski(k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)),k1_xboole_0) != iProver_top ),
% 39.30/5.52      inference(superposition,[status(thm)],[c_120488,c_73923]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_138743,plain,
% 39.30/5.52      ( sK1 = k1_xboole_0
% 39.30/5.52      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 39.30/5.52      | r1_tarski(k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)),k1_xboole_0) != iProver_top ),
% 39.30/5.52      inference(superposition,[status(thm)],[c_4415,c_121570]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_9446,plain,
% 39.30/5.52      ( ~ r1_tarski(X0,X1)
% 39.30/5.52      | r1_tarski(sK0,k1_xboole_0)
% 39.30/5.52      | sK0 != X0
% 39.30/5.52      | k1_xboole_0 != X1 ),
% 39.30/5.52      inference(instantiation,[status(thm)],[c_803]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_9447,plain,
% 39.30/5.52      ( sK0 != X0
% 39.30/5.52      | k1_xboole_0 != X1
% 39.30/5.52      | r1_tarski(X0,X1) != iProver_top
% 39.30/5.52      | r1_tarski(sK0,k1_xboole_0) = iProver_top ),
% 39.30/5.52      inference(predicate_to_equality,[status(thm)],[c_9446]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_9449,plain,
% 39.30/5.52      ( sK0 != k1_xboole_0
% 39.30/5.52      | k1_xboole_0 != k1_xboole_0
% 39.30/5.52      | r1_tarski(sK0,k1_xboole_0) = iProver_top
% 39.30/5.52      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 39.30/5.52      inference(instantiation,[status(thm)],[c_9447]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_71102,plain,
% 39.30/5.52      ( r1_tarski(k1_relat_1(k7_relat_1(X0,sK2)),X1) = iProver_top
% 39.30/5.52      | r1_tarski(sK0,k1_xboole_0) != iProver_top
% 39.30/5.52      | v1_relat_1(X0) != iProver_top ),
% 39.30/5.52      inference(superposition,[status(thm)],[c_1408,c_69358]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_98360,plain,
% 39.30/5.52      ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 39.30/5.52      | r1_tarski(sK0,k1_xboole_0) != iProver_top
% 39.30/5.52      | v1_relat_1(sK3) != iProver_top ),
% 39.30/5.52      inference(superposition,[status(thm)],[c_71102,c_73923]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_139127,plain,
% 39.30/5.52      ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 39.30/5.52      | r1_tarski(k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)),k1_xboole_0) != iProver_top ),
% 39.30/5.52      inference(global_propositional_subsumption,
% 39.30/5.52                [status(thm)],
% 39.30/5.52                [c_138743,c_34,c_100,c_101,c_1635,c_2070,c_3614,c_9449,
% 39.30/5.52                 c_98360]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_139133,plain,
% 39.30/5.52      ( sK1 = k1_xboole_0
% 39.30/5.52      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 39.30/5.52      | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
% 39.30/5.52      inference(superposition,[status(thm)],[c_131142,c_139127]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_139447,plain,
% 39.30/5.52      ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 39.30/5.52      | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
% 39.30/5.52      inference(global_propositional_subsumption,
% 39.30/5.52                [status(thm)],
% 39.30/5.52                [c_139133,c_34,c_1635,c_98360]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_139453,plain,
% 39.30/5.52      ( r1_tarski(k7_relat_1(sK3,sK2),k1_xboole_0) = iProver_top
% 39.30/5.52      | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
% 39.30/5.52      inference(superposition,[status(thm)],[c_139447,c_1410]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_97745,plain,
% 39.30/5.52      ( X0 != X1 | X0 = sK3 | sK3 != X1 ),
% 39.30/5.52      inference(instantiation,[status(thm)],[c_802]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_151200,plain,
% 39.30/5.52      ( k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 39.30/5.52      | k2_partfun1(sK0,sK1,sK3,sK2) = sK3
% 39.30/5.52      | sK3 != X0 ),
% 39.30/5.52      inference(instantiation,[status(thm)],[c_97745]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_151201,plain,
% 39.30/5.52      ( k2_partfun1(sK0,sK1,sK3,sK2) = sK3
% 39.30/5.52      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 39.30/5.52      | sK3 != k1_xboole_0 ),
% 39.30/5.52      inference(instantiation,[status(thm)],[c_151200]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_151218,plain,
% 39.30/5.52      ( r1_tarski(sK0,k1_xboole_0) != iProver_top ),
% 39.30/5.52      inference(global_propositional_subsumption,
% 39.30/5.52                [status(thm)],
% 39.30/5.52                [c_127619,c_31,c_29,c_98,c_100,c_101,c_521,c_1634,c_1654,
% 39.30/5.52                 c_1764,c_1801,c_1921,c_1927,c_1928,c_2020,c_2149,c_3615,
% 39.30/5.52                 c_4805,c_13248,c_16037,c_22081,c_27774,c_28350,c_35156,
% 39.30/5.52                 c_72311,c_76999,c_91183,c_91303,c_94720,c_95588,
% 39.30/5.52                 c_104774,c_114471,c_124227,c_139453,c_151201]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_121572,plain,
% 39.30/5.52      ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
% 39.30/5.52      | sK1 = k1_xboole_0 ),
% 39.30/5.52      inference(superposition,[status(thm)],[c_120488,c_18662]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_20,plain,
% 39.30/5.52      ( v1_funct_2(X0,X1,X2)
% 39.30/5.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.30/5.52      | k1_relset_1(X1,X2,X0) != X1
% 39.30/5.52      | k1_xboole_0 = X2 ),
% 39.30/5.52      inference(cnf_transformation,[],[f68]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_494,plain,
% 39.30/5.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.30/5.52      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 39.30/5.52      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 39.30/5.52      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 39.30/5.52      | k1_relset_1(X1,X2,X0) != X1
% 39.30/5.52      | sK2 != X1
% 39.30/5.52      | sK1 != X2
% 39.30/5.52      | k1_xboole_0 = X2 ),
% 39.30/5.52      inference(resolution_lifted,[status(thm)],[c_20,c_26]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_495,plain,
% 39.30/5.52      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 39.30/5.52      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 39.30/5.52      | k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 39.30/5.52      | k1_xboole_0 = sK1 ),
% 39.30/5.52      inference(unflattening,[status(thm)],[c_494]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_1391,plain,
% 39.30/5.52      ( k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 39.30/5.52      | k1_xboole_0 = sK1
% 39.30/5.52      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 39.30/5.52      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 39.30/5.52      inference(predicate_to_equality,[status(thm)],[c_495]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_2653,plain,
% 39.30/5.52      ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) != sK2
% 39.30/5.52      | sK1 = k1_xboole_0
% 39.30/5.52      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 39.30/5.52      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 39.30/5.52      inference(demodulation,[status(thm)],[c_2646,c_1391]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_129514,plain,
% 39.30/5.52      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 39.30/5.52      | sK1 = k1_xboole_0
% 39.30/5.52      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 39.30/5.52      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 39.30/5.52      inference(superposition,[status(thm)],[c_121572,c_2653]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_129517,plain,
% 39.30/5.52      ( sK1 = k1_xboole_0
% 39.30/5.52      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 39.30/5.52      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 39.30/5.52      inference(global_propositional_subsumption,
% 39.30/5.52                [status(thm)],
% 39.30/5.52                [c_129514,c_4415]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_1401,plain,
% 39.30/5.52      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 39.30/5.52      | v1_funct_1(X0) != iProver_top
% 39.30/5.52      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
% 39.30/5.52      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_2801,plain,
% 39.30/5.52      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
% 39.30/5.52      | v1_funct_1(sK3) != iProver_top ),
% 39.30/5.52      inference(superposition,[status(thm)],[c_1398,c_1401]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_2818,plain,
% 39.30/5.52      ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top
% 39.30/5.52      | v1_funct_1(sK3) != iProver_top ),
% 39.30/5.52      inference(light_normalisation,[status(thm)],[c_2801,c_2646]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_3421,plain,
% 39.30/5.52      ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 39.30/5.52      inference(global_propositional_subsumption,
% 39.30/5.52                [status(thm)],
% 39.30/5.52                [c_2818,c_32]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_129524,plain,
% 39.30/5.52      ( sK1 = k1_xboole_0
% 39.30/5.52      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 39.30/5.52      inference(forward_subsumption_resolution,
% 39.30/5.52                [status(thm)],
% 39.30/5.52                [c_129517,c_3421]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_129527,plain,
% 39.30/5.52      ( sK1 = k1_xboole_0
% 39.30/5.52      | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) != iProver_top
% 39.30/5.52      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
% 39.30/5.52      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 39.30/5.52      inference(superposition,[status(thm)],[c_1403,c_129524]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_129541,plain,
% 39.30/5.52      ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)
% 39.30/5.52      | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1)
% 39.30/5.52      | ~ v1_relat_1(k7_relat_1(sK3,sK2))
% 39.30/5.52      | sK1 = k1_xboole_0 ),
% 39.30/5.52      inference(predicate_to_equality_rev,[status(thm)],[c_129527]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_92924,plain,
% 39.30/5.52      ( k7_relat_1(sK3,sK2) = k7_relat_1(sK3,sK2) ),
% 39.30/5.52      inference(instantiation,[status(thm)],[c_801]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_85417,plain,
% 39.30/5.52      ( v1_relat_1(k7_relat_1(sK3,sK2)) | ~ v1_relat_1(sK3) ),
% 39.30/5.52      inference(instantiation,[status(thm)],[c_1717]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_1680,plain,
% 39.30/5.52      ( m1_subset_1(k2_partfun1(X0,X1,sK3,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 39.30/5.52      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 39.30/5.52      | ~ v1_funct_1(sK3) ),
% 39.30/5.52      inference(instantiation,[status(thm)],[c_23]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_1848,plain,
% 39.30/5.52      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 39.30/5.52      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 39.30/5.52      | ~ v1_funct_1(sK3) ),
% 39.30/5.52      inference(instantiation,[status(thm)],[c_1680]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_85088,plain,
% 39.30/5.52      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 39.30/5.52      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 39.30/5.52      | ~ v1_funct_1(sK3) ),
% 39.30/5.52      inference(instantiation,[status(thm)],[c_1848]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_2528,plain,
% 39.30/5.52      ( X0 != X1
% 39.30/5.52      | X0 = k2_partfun1(sK0,sK1,sK3,X2)
% 39.30/5.52      | k2_partfun1(sK0,sK1,sK3,X2) != X1 ),
% 39.30/5.52      inference(instantiation,[status(thm)],[c_802]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_5319,plain,
% 39.30/5.52      ( X0 = k2_partfun1(sK0,sK1,sK3,X1)
% 39.30/5.52      | X0 != k7_relat_1(sK3,X1)
% 39.30/5.52      | k2_partfun1(sK0,sK1,sK3,X1) != k7_relat_1(sK3,X1) ),
% 39.30/5.52      inference(instantiation,[status(thm)],[c_2528]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_6739,plain,
% 39.30/5.52      ( k2_partfun1(sK0,sK1,sK3,X0) != k7_relat_1(sK3,X0)
% 39.30/5.52      | k7_relat_1(sK3,X0) = k2_partfun1(sK0,sK1,sK3,X0)
% 39.30/5.52      | k7_relat_1(sK3,X0) != k7_relat_1(sK3,X0) ),
% 39.30/5.52      inference(instantiation,[status(thm)],[c_5319]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_54988,plain,
% 39.30/5.52      ( k2_partfun1(sK0,sK1,sK3,sK2) != k7_relat_1(sK3,sK2)
% 39.30/5.52      | k7_relat_1(sK3,sK2) = k2_partfun1(sK0,sK1,sK3,sK2)
% 39.30/5.52      | k7_relat_1(sK3,sK2) != k7_relat_1(sK3,sK2) ),
% 39.30/5.52      inference(instantiation,[status(thm)],[c_6739]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_2167,plain,
% 39.30/5.52      ( m1_subset_1(X0,X1)
% 39.30/5.52      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,X2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 39.30/5.52      | X0 != k2_partfun1(sK0,sK1,sK3,X2)
% 39.30/5.52      | X1 != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 39.30/5.52      inference(instantiation,[status(thm)],[c_806]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_2576,plain,
% 39.30/5.52      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 39.30/5.52      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 39.30/5.52      | X0 != k2_partfun1(sK0,sK1,sK3,X1)
% 39.30/5.52      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 39.30/5.52      inference(instantiation,[status(thm)],[c_2167]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_18875,plain,
% 39.30/5.52      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 39.30/5.52      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 39.30/5.52      | k7_relat_1(sK3,sK2) != k2_partfun1(sK0,sK1,sK3,X0)
% 39.30/5.52      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 39.30/5.52      inference(instantiation,[status(thm)],[c_2576]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_54987,plain,
% 39.30/5.52      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 39.30/5.52      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 39.30/5.52      | k7_relat_1(sK3,sK2) != k2_partfun1(sK0,sK1,sK3,sK2)
% 39.30/5.52      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 39.30/5.52      inference(instantiation,[status(thm)],[c_18875]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_2577,plain,
% 39.30/5.52      ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 39.30/5.52      inference(instantiation,[status(thm)],[c_801]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(c_1996,plain,
% 39.30/5.52      ( r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)
% 39.30/5.52      | ~ v1_relat_1(sK3) ),
% 39.30/5.52      inference(instantiation,[status(thm)],[c_1720]) ).
% 39.30/5.52  
% 39.30/5.52  cnf(contradiction,plain,
% 39.30/5.52      ( $false ),
% 39.30/5.52      inference(minisat,
% 39.30/5.52                [status(thm)],
% 39.30/5.52                [c_181552,c_151218,c_129541,c_92924,c_85417,c_85088,
% 39.30/5.52                 c_54988,c_54987,c_28350,c_9449,c_3614,c_2577,c_2070,
% 39.30/5.52                 c_1996,c_1635,c_1634,c_101,c_100,c_34,c_29,c_31]) ).
% 39.30/5.52  
% 39.30/5.52  
% 39.30/5.52  % SZS output end CNFRefutation for theBenchmark.p
% 39.30/5.52  
% 39.30/5.52  ------                               Statistics
% 39.30/5.52  
% 39.30/5.52  ------ General
% 39.30/5.52  
% 39.30/5.52  abstr_ref_over_cycles:                  0
% 39.30/5.52  abstr_ref_under_cycles:                 0
% 39.30/5.52  gc_basic_clause_elim:                   0
% 39.30/5.52  forced_gc_time:                         0
% 39.30/5.52  parsing_time:                           0.012
% 39.30/5.52  unif_index_cands_time:                  0.
% 39.30/5.52  unif_index_add_time:                    0.
% 39.30/5.52  orderings_time:                         0.
% 39.30/5.52  out_proof_time:                         0.065
% 39.30/5.52  total_time:                             4.732
% 39.30/5.52  num_of_symbols:                         49
% 39.30/5.52  num_of_terms:                           117720
% 39.30/5.52  
% 39.30/5.52  ------ Preprocessing
% 39.30/5.52  
% 39.30/5.52  num_of_splits:                          0
% 39.30/5.52  num_of_split_atoms:                     0
% 39.30/5.52  num_of_reused_defs:                     0
% 39.30/5.52  num_eq_ax_congr_red:                    13
% 39.30/5.52  num_of_sem_filtered_clauses:            1
% 39.30/5.52  num_of_subtypes:                        0
% 39.30/5.52  monotx_restored_types:                  0
% 39.30/5.52  sat_num_of_epr_types:                   0
% 39.30/5.52  sat_num_of_non_cyclic_types:            0
% 39.30/5.52  sat_guarded_non_collapsed_types:        0
% 39.30/5.52  num_pure_diseq_elim:                    0
% 39.30/5.52  simp_replaced_by:                       0
% 39.30/5.52  res_preprocessed:                       142
% 39.30/5.52  prep_upred:                             0
% 39.30/5.52  prep_unflattend:                        33
% 39.30/5.52  smt_new_axioms:                         0
% 39.30/5.52  pred_elim_cands:                        4
% 39.30/5.52  pred_elim:                              2
% 39.30/5.52  pred_elim_cl:                           3
% 39.30/5.52  pred_elim_cycles:                       4
% 39.30/5.52  merged_defs:                            8
% 39.30/5.52  merged_defs_ncl:                        0
% 39.30/5.52  bin_hyper_res:                          8
% 39.30/5.52  prep_cycles:                            4
% 39.30/5.52  pred_elim_time:                         0.009
% 39.30/5.52  splitting_time:                         0.
% 39.30/5.52  sem_filter_time:                        0.
% 39.30/5.52  monotx_time:                            0.001
% 39.30/5.52  subtype_inf_time:                       0.
% 39.30/5.52  
% 39.30/5.52  ------ Problem properties
% 39.30/5.52  
% 39.30/5.52  clauses:                                29
% 39.30/5.52  conjectures:                            4
% 39.30/5.52  epr:                                    5
% 39.30/5.52  horn:                                   26
% 39.30/5.52  ground:                                 11
% 39.30/5.52  unary:                                  5
% 39.30/5.52  binary:                                 11
% 39.30/5.52  lits:                                   75
% 39.30/5.52  lits_eq:                                27
% 39.30/5.52  fd_pure:                                0
% 39.30/5.52  fd_pseudo:                              0
% 39.30/5.52  fd_cond:                                2
% 39.30/5.52  fd_pseudo_cond:                         0
% 39.30/5.52  ac_symbols:                             0
% 39.30/5.52  
% 39.30/5.52  ------ Propositional Solver
% 39.30/5.52  
% 39.30/5.52  prop_solver_calls:                      62
% 39.30/5.52  prop_fast_solver_calls:                 6148
% 39.30/5.52  smt_solver_calls:                       0
% 39.30/5.52  smt_fast_solver_calls:                  0
% 39.30/5.52  prop_num_of_clauses:                    61262
% 39.30/5.52  prop_preprocess_simplified:             78629
% 39.30/5.52  prop_fo_subsumed:                       423
% 39.30/5.52  prop_solver_time:                       0.
% 39.30/5.52  smt_solver_time:                        0.
% 39.30/5.52  smt_fast_solver_time:                   0.
% 39.30/5.52  prop_fast_solver_time:                  0.
% 39.30/5.52  prop_unsat_core_time:                   0.007
% 39.30/5.52  
% 39.30/5.52  ------ QBF
% 39.30/5.52  
% 39.30/5.52  qbf_q_res:                              0
% 39.30/5.52  qbf_num_tautologies:                    0
% 39.30/5.52  qbf_prep_cycles:                        0
% 39.30/5.52  
% 39.30/5.52  ------ BMC1
% 39.30/5.52  
% 39.30/5.52  bmc1_current_bound:                     -1
% 39.30/5.52  bmc1_last_solved_bound:                 -1
% 39.30/5.52  bmc1_unsat_core_size:                   -1
% 39.30/5.52  bmc1_unsat_core_parents_size:           -1
% 39.30/5.52  bmc1_merge_next_fun:                    0
% 39.30/5.52  bmc1_unsat_core_clauses_time:           0.
% 39.30/5.52  
% 39.30/5.52  ------ Instantiation
% 39.30/5.52  
% 39.30/5.52  inst_num_of_clauses:                    8303
% 39.30/5.52  inst_num_in_passive:                    2960
% 39.30/5.52  inst_num_in_active:                     4913
% 39.30/5.52  inst_num_in_unprocessed:                2634
% 39.30/5.52  inst_num_of_loops:                      5943
% 39.30/5.52  inst_num_of_learning_restarts:          1
% 39.30/5.52  inst_num_moves_active_passive:          1021
% 39.30/5.52  inst_lit_activity:                      0
% 39.30/5.52  inst_lit_activity_moves:                0
% 39.30/5.52  inst_num_tautologies:                   0
% 39.30/5.52  inst_num_prop_implied:                  0
% 39.30/5.52  inst_num_existing_simplified:           0
% 39.30/5.52  inst_num_eq_res_simplified:             0
% 39.30/5.52  inst_num_child_elim:                    0
% 39.30/5.52  inst_num_of_dismatching_blockings:      6459
% 39.30/5.52  inst_num_of_non_proper_insts:           11902
% 39.30/5.52  inst_num_of_duplicates:                 0
% 39.30/5.52  inst_inst_num_from_inst_to_res:         0
% 39.30/5.52  inst_dismatching_checking_time:         0.
% 39.30/5.52  
% 39.30/5.52  ------ Resolution
% 39.30/5.52  
% 39.30/5.52  res_num_of_clauses:                     40
% 39.30/5.52  res_num_in_passive:                     40
% 39.30/5.52  res_num_in_active:                      0
% 39.30/5.52  res_num_of_loops:                       146
% 39.30/5.52  res_forward_subset_subsumed:            307
% 39.30/5.52  res_backward_subset_subsumed:           6
% 39.30/5.52  res_forward_subsumed:                   0
% 39.30/5.52  res_backward_subsumed:                  0
% 39.30/5.52  res_forward_subsumption_resolution:     0
% 39.30/5.52  res_backward_subsumption_resolution:    0
% 39.30/5.52  res_clause_to_clause_subsumption:       39759
% 39.30/5.52  res_orphan_elimination:                 0
% 39.30/5.52  res_tautology_del:                      967
% 39.30/5.52  res_num_eq_res_simplified:              1
% 39.30/5.52  res_num_sel_changes:                    0
% 39.30/5.52  res_moves_from_active_to_pass:          0
% 39.30/5.52  
% 39.30/5.52  ------ Superposition
% 39.30/5.52  
% 39.30/5.52  sup_time_total:                         0.
% 39.30/5.52  sup_time_generating:                    0.
% 39.30/5.52  sup_time_sim_full:                      0.
% 39.30/5.52  sup_time_sim_immed:                     0.
% 39.30/5.52  
% 39.30/5.52  sup_num_of_clauses:                     7891
% 39.30/5.52  sup_num_in_active:                      996
% 39.30/5.52  sup_num_in_passive:                     6895
% 39.30/5.52  sup_num_of_loops:                       1188
% 39.30/5.52  sup_fw_superposition:                   7092
% 39.30/5.52  sup_bw_superposition:                   5812
% 39.30/5.52  sup_immediate_simplified:               3459
% 39.30/5.52  sup_given_eliminated:                   15
% 39.30/5.52  comparisons_done:                       0
% 39.30/5.52  comparisons_avoided:                    672
% 39.30/5.52  
% 39.30/5.52  ------ Simplifications
% 39.30/5.52  
% 39.30/5.52  
% 39.30/5.52  sim_fw_subset_subsumed:                 759
% 39.30/5.52  sim_bw_subset_subsumed:                 111
% 39.30/5.52  sim_fw_subsumed:                        1440
% 39.30/5.52  sim_bw_subsumed:                        215
% 39.30/5.52  sim_fw_subsumption_res:                 130
% 39.30/5.52  sim_bw_subsumption_res:                 0
% 39.30/5.52  sim_tautology_del:                      147
% 39.30/5.52  sim_eq_tautology_del:                   279
% 39.30/5.52  sim_eq_res_simp:                        0
% 39.30/5.52  sim_fw_demodulated:                     566
% 39.30/5.52  sim_bw_demodulated:                     205
% 39.30/5.52  sim_light_normalised:                   883
% 39.30/5.52  sim_joinable_taut:                      0
% 39.30/5.52  sim_joinable_simp:                      0
% 39.30/5.52  sim_ac_normalised:                      0
% 39.30/5.52  sim_smt_subsumption:                    0
% 39.30/5.52  
%------------------------------------------------------------------------------
