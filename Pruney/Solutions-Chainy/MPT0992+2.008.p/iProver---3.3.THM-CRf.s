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
% DateTime   : Thu Dec  3 12:03:47 EST 2020

% Result     : Theorem 31.80s
% Output     : CNFRefutation 31.80s
% Verified   : 
% Statistics : Number of formulae       :  356 (46562 expanded)
%              Number of clauses        :  281 (19176 expanded)
%              Number of leaves         :   27 (8971 expanded)
%              Depth                    :   58
%              Number of atoms          : 1018 (236786 expanded)
%              Number of equality atoms :  676 (73471 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

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

fof(f39,plain,(
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
    inference(flattening,[],[f39])).

fof(f46,plain,
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

fof(f47,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f40,f46])).

fof(f77,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f47])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f75,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f78,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f47])).

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

fof(f33,plain,(
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
    inference(flattening,[],[f33])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f76,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f41])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f82,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f50])).

fof(f79,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f47])).

fof(f80,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f47])).

fof(f1,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f48,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_8,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1003,plain,
    ( v5_relat_1(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_17,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_994,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_982,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_985,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_7993,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_982,c_985])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1350,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_1503,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_1350])).

cnf(c_8214,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7993,c_32,c_30,c_1503])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_987,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_8251,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_8214,c_987])).

cnf(c_33,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_35,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_1345,plain,
    ( m1_subset_1(k2_partfun1(X0,X1,sK3,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_1568,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1345])).

cnf(c_1569,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1568])).

cnf(c_341,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1919,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_341])).

cnf(c_342,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1903,plain,
    ( X0 != X1
    | X0 = k2_partfun1(sK0,sK1,sK3,X2)
    | k2_partfun1(sK0,sK1,sK3,X2) != X1 ),
    inference(instantiation,[status(thm)],[c_342])).

cnf(c_3352,plain,
    ( X0 = k2_partfun1(sK0,sK1,sK3,X1)
    | X0 != k7_relat_1(sK3,X1)
    | k2_partfun1(sK0,sK1,sK3,X1) != k7_relat_1(sK3,X1) ),
    inference(instantiation,[status(thm)],[c_1903])).

cnf(c_3818,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) != k7_relat_1(sK3,X0)
    | k7_relat_1(sK3,X0) = k2_partfun1(sK0,sK1,sK3,X0)
    | k7_relat_1(sK3,X0) != k7_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_3352])).

cnf(c_3819,plain,
    ( k7_relat_1(sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_341])).

cnf(c_346,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1623,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,X2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | X0 != k2_partfun1(sK0,sK1,sK3,X2)
    | X1 != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_346])).

cnf(c_1918,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | X0 != k2_partfun1(sK0,sK1,sK3,X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_1623])).

cnf(c_5140,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k7_relat_1(sK3,X0) != k2_partfun1(sK0,sK1,sK3,X0)
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_1918])).

cnf(c_5146,plain,
    ( k7_relat_1(sK3,X0) != k2_partfun1(sK0,sK1,sK3,X0)
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5140])).

cnf(c_8451,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8251,c_32,c_33,c_30,c_35,c_1503,c_1569,c_1919,c_3818,c_3819,c_5146])).

cnf(c_14,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_997,plain,
    ( v5_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_8466,plain,
    ( v5_relat_1(k7_relat_1(sK3,X0),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_8451,c_997])).

cnf(c_15,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_996,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2420,plain,
    ( v4_relat_1(sK3,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_982,c_996])).

cnf(c_9,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1002,plain,
    ( k7_relat_1(X0,X1) = X0
    | v4_relat_1(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4015,plain,
    ( k7_relat_1(sK3,sK0) = sK3
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2420,c_1002])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1279,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1302,plain,
    ( v4_relat_1(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1397,plain,
    ( ~ v4_relat_1(sK3,X0)
    | ~ v1_relat_1(sK3)
    | k7_relat_1(sK3,X0) = sK3 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1682,plain,
    ( ~ v4_relat_1(sK3,sK0)
    | ~ v1_relat_1(sK3)
    | k7_relat_1(sK3,sK0) = sK3 ),
    inference(instantiation,[status(thm)],[c_1397])).

cnf(c_4152,plain,
    ( k7_relat_1(sK3,sK0) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4015,c_30,c_1279,c_1302,c_1682])).

cnf(c_29,negated_conjecture,
    ( r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_983,plain,
    ( r1_tarski(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_988,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3869,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | sK1 = k1_xboole_0
    | v1_funct_2(sK3,sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_982,c_988])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_995,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3234,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_982,c_995])).

cnf(c_3883,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0
    | v1_funct_2(sK3,sK0,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3869,c_3234])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_34,plain,
    ( v1_funct_2(sK3,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_4341,plain,
    ( sK1 = k1_xboole_0
    | k1_relat_1(sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3883,c_34])).

cnf(c_4342,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_4341])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_999,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_5205,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4342,c_999])).

cnf(c_1280,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1279])).

cnf(c_5374,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | sK1 = k1_xboole_0
    | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5205,c_35,c_1280])).

cnf(c_5375,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5374])).

cnf(c_5384,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_983,c_5375])).

cnf(c_998,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_8464,plain,
    ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8451,c_998])).

cnf(c_10,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1001,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_5201,plain,
    ( k1_relat_1(k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))) = k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1001,c_999])).

cnf(c_47397,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),k1_relat_1(k7_relat_1(X1,k1_relat_1(k7_relat_1(sK3,X0)))))) = k1_relat_1(k7_relat_1(X1,k1_relat_1(k7_relat_1(sK3,X0))))
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_8464,c_5201])).

cnf(c_54813,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),k1_relat_1(k7_relat_1(k7_relat_1(sK3,X1),k1_relat_1(k7_relat_1(sK3,X0)))))) = k1_relat_1(k7_relat_1(k7_relat_1(sK3,X1),k1_relat_1(k7_relat_1(sK3,X0)))) ),
    inference(superposition,[status(thm)],[c_8464,c_47397])).

cnf(c_65801,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),k1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),sK2)))) = k1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),k1_relat_1(k7_relat_1(sK3,sK2))))
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5384,c_54813])).

cnf(c_11,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1000,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_4,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_208,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_4])).

cnf(c_209,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_208])).

cnf(c_269,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_209])).

cnf(c_979,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_269])).

cnf(c_1515,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1000,c_979])).

cnf(c_5745,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK2) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5384,c_999])).

cnf(c_5958,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1515,c_5745])).

cnf(c_5963,plain,
    ( r1_tarski(X0,sK2) != iProver_top
    | sK1 = k1_xboole_0
    | k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5958,c_35,c_1280])).

cnf(c_5964,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_5963])).

cnf(c_5973,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),k1_relat_1(k7_relat_1(X0,sK2)))) = k1_relat_1(k7_relat_1(X0,sK2))
    | sK1 = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1001,c_5964])).

cnf(c_8847,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),k1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),sK2)))) = k1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),sK2))
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8464,c_5973])).

cnf(c_66265,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),k1_relat_1(k7_relat_1(sK3,sK2)))) = k1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),sK2))
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_65801,c_8847])).

cnf(c_66964,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),sK2)),k1_relat_1(k7_relat_1(sK3,sK2))) = iProver_top
    | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_66265,c_1001])).

cnf(c_1399,plain,
    ( r1_tarski(k7_relat_1(sK3,X0),sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1405,plain,
    ( r1_tarski(k7_relat_1(sK3,X0),sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1399])).

cnf(c_1417,plain,
    ( ~ r1_tarski(X0,sK3)
    | v1_relat_1(X0)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_269])).

cnf(c_1714,plain,
    ( ~ r1_tarski(k7_relat_1(sK3,X0),sK3)
    | v1_relat_1(k7_relat_1(sK3,X0))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1417])).

cnf(c_1715,plain,
    ( r1_tarski(k7_relat_1(sK3,X0),sK3) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1714])).

cnf(c_67617,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),sK2)),k1_relat_1(k7_relat_1(sK3,sK2))) = iProver_top
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_66964,c_35,c_1280,c_1405,c_1715])).

cnf(c_67618,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),sK2)),k1_relat_1(k7_relat_1(sK3,sK2))) = iProver_top ),
    inference(renaming,[status(thm)],[c_67617])).

cnf(c_67631,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),sK2)),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_5384,c_67618])).

cnf(c_6460,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | r1_tarski(k1_relat_1(X2),X0) != iProver_top
    | r1_tarski(k2_relat_1(X2),X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_994,c_995])).

cnf(c_84158,plain,
    ( k1_relset_1(sK2,X0,k7_relat_1(k7_relat_1(sK3,X1),sK2)) = k1_relat_1(k7_relat_1(k7_relat_1(sK3,X1),sK2))
    | sK1 = k1_xboole_0
    | r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK3,X1),sK2)),X0) != iProver_top
    | v1_relat_1(k7_relat_1(k7_relat_1(sK3,X1),sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_67631,c_6460])).

cnf(c_3,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_105,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_106,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1305,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_342])).

cnf(c_1306,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1305])).

cnf(c_28,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_27,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_343,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1335,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(sK2,sK0)
    | X0 != sK2
    | X1 != sK0 ),
    inference(instantiation,[status(thm)],[c_343])).

cnf(c_1477,plain,
    ( r1_tarski(sK2,X0)
    | ~ r1_tarski(sK2,sK0)
    | X0 != sK0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1335])).

cnf(c_1480,plain,
    ( ~ r1_tarski(sK2,sK0)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != sK2
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1477])).

cnf(c_1478,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_341])).

cnf(c_1492,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_341])).

cnf(c_349,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_1380,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | X0 != sK3
    | X2 != sK1
    | X1 != sK0 ),
    inference(instantiation,[status(thm)],[c_349])).

cnf(c_1665,plain,
    ( v1_funct_2(sK3,X0,X1)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | X1 != sK1
    | X0 != sK0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1380])).

cnf(c_2185,plain,
    ( v1_funct_2(sK3,X0,sK1)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | X0 != sK0
    | sK3 != sK3
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1665])).

cnf(c_2188,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | v1_funct_2(sK3,k1_xboole_0,sK1)
    | sK3 != sK3
    | sK1 != sK1
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_2185])).

cnf(c_2186,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_341])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2527,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1894,plain,
    ( X0 != X1
    | sK2 != X1
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_342])).

cnf(c_3056,plain,
    ( X0 != sK2
    | sK2 = X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1894])).

cnf(c_3057,plain,
    ( sK2 != sK2
    | sK2 = k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_3056])).

cnf(c_4266,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(sK0,sK1,sK3,sK0) = k7_relat_1(sK3,sK0) ),
    inference(instantiation,[status(thm)],[c_1503])).

cnf(c_1774,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_342])).

cnf(c_2928,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1774])).

cnf(c_4331,plain,
    ( k7_relat_1(sK3,sK0) != sK3
    | sK3 = k7_relat_1(sK3,sK0)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2928])).

cnf(c_6740,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_341])).

cnf(c_7599,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK0) != k7_relat_1(sK3,sK0)
    | sK3 = k2_partfun1(sK0,sK1,sK3,sK0)
    | sK3 != k7_relat_1(sK3,sK0) ),
    inference(instantiation,[status(thm)],[c_3352])).

cnf(c_344,plain,
    ( X0 != X1
    | X2 != X3
    | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
    theory(equality)).

cnf(c_2628,plain,
    ( k2_zfmisc_1(sK2,sK1) = k2_zfmisc_1(X0,X1)
    | sK2 != X0
    | sK1 != X1 ),
    inference(instantiation,[status(thm)],[c_344])).

cnf(c_6635,plain,
    ( k2_zfmisc_1(sK2,sK1) = k2_zfmisc_1(X0,sK1)
    | sK2 != X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_2628])).

cnf(c_12067,plain,
    ( k2_zfmisc_1(sK2,sK1) = k2_zfmisc_1(sK0,sK1)
    | sK2 != sK0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_6635])).

cnf(c_21936,plain,
    ( sK2 != X0
    | sK2 = sK0
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_1894])).

cnf(c_21938,plain,
    ( sK2 = sK0
    | sK2 != k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_21936])).

cnf(c_2924,plain,
    ( X0 != X1
    | sK0 != X1
    | sK0 = X0 ),
    inference(instantiation,[status(thm)],[c_342])).

cnf(c_31531,plain,
    ( X0 != sK0
    | sK0 = X0
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_2924])).

cnf(c_31533,plain,
    ( sK0 != sK0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_31531])).

cnf(c_345,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_1791,plain,
    ( X0 != k2_zfmisc_1(sK0,sK1)
    | k1_zfmisc_1(X0) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_345])).

cnf(c_2687,plain,
    ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_1791])).

cnf(c_12120,plain,
    ( k2_zfmisc_1(X0,sK1) != k2_zfmisc_1(sK0,sK1)
    | k1_zfmisc_1(k2_zfmisc_1(X0,sK1)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_2687])).

cnf(c_34369,plain,
    ( k2_zfmisc_1(sK2,sK1) != k2_zfmisc_1(sK0,sK1)
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_12120])).

cnf(c_350,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | X6 != X7
    | k2_partfun1(X0,X2,X4,X6) = k2_partfun1(X1,X3,X5,X7) ),
    theory(equality)).

cnf(c_1906,plain,
    ( X0 != X1
    | X2 != sK3
    | X3 != sK1
    | X4 != sK0
    | k2_partfun1(X4,X3,X2,X0) = k2_partfun1(sK0,sK1,sK3,X1) ),
    inference(instantiation,[status(thm)],[c_350])).

cnf(c_3446,plain,
    ( X0 != X1
    | X2 != sK3
    | X3 != sK0
    | k2_partfun1(X3,sK1,X2,X0) = k2_partfun1(sK0,sK1,sK3,X1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1906])).

cnf(c_14866,plain,
    ( X0 != X1
    | X2 != sK0
    | k2_partfun1(X2,sK1,sK3,X0) = k2_partfun1(sK0,sK1,sK3,X1)
    | sK3 != sK3
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_3446])).

cnf(c_20073,plain,
    ( X0 != X1
    | k2_partfun1(sK0,sK1,sK3,X0) = k2_partfun1(sK0,sK1,sK3,X1)
    | sK3 != sK3
    | sK1 != sK1
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_14866])).

cnf(c_56632,plain,
    ( X0 != sK0
    | k2_partfun1(sK0,sK1,sK3,X0) = k2_partfun1(sK0,sK1,sK3,sK0)
    | sK3 != sK3
    | sK1 != sK1
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_20073])).

cnf(c_56635,plain,
    ( k2_partfun1(sK0,sK1,sK3,k1_xboole_0) = k2_partfun1(sK0,sK1,sK3,sK0)
    | sK3 != sK3
    | sK1 != sK1
    | sK0 != sK0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_56632])).

cnf(c_17504,plain,
    ( X0 != k2_partfun1(sK0,sK1,sK3,sK0)
    | sK3 = X0
    | sK3 != k2_partfun1(sK0,sK1,sK3,sK0) ),
    inference(instantiation,[status(thm)],[c_1774])).

cnf(c_56633,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) != k2_partfun1(sK0,sK1,sK3,sK0)
    | sK3 = k2_partfun1(sK0,sK1,sK3,X0)
    | sK3 != k2_partfun1(sK0,sK1,sK3,sK0) ),
    inference(instantiation,[status(thm)],[c_17504])).

cnf(c_56636,plain,
    ( k2_partfun1(sK0,sK1,sK3,k1_xboole_0) != k2_partfun1(sK0,sK1,sK3,sK0)
    | sK3 != k2_partfun1(sK0,sK1,sK3,sK0)
    | sK3 = k2_partfun1(sK0,sK1,sK3,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_56633])).

cnf(c_56637,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) = k2_partfun1(sK0,sK1,sK3,X0)
    | sK2 != X0
    | sK3 != sK3
    | sK1 != sK1
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_20073])).

cnf(c_56641,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) = k2_partfun1(sK0,sK1,sK3,k1_xboole_0)
    | sK2 != k1_xboole_0
    | sK3 != sK3
    | sK1 != sK1
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_56637])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1330,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(k2_partfun1(X0,X1,sK3,X2))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_1498,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1330])).

cnf(c_64102,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1498])).

cnf(c_2055,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | X0 != X2
    | X1 != k1_zfmisc_1(X3) ),
    inference(instantiation,[status(thm)],[c_346])).

cnf(c_3623,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(X2,k1_zfmisc_1(X3))
    | X2 != X0
    | k1_zfmisc_1(X3) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_2055])).

cnf(c_14388,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_3623])).

cnf(c_34370,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_14388])).

cnf(c_65454,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k2_partfun1(sK0,sK1,sK3,sK2) != sK3
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_34370])).

cnf(c_2829,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(sK3,X3,sK1)
    | X1 != X3
    | X0 != sK3
    | X2 != sK1 ),
    inference(instantiation,[status(thm)],[c_349])).

cnf(c_65553,plain,
    ( v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_2(sK3,X0,sK1)
    | k2_partfun1(sK0,sK1,sK3,sK2) != sK3
    | sK2 != X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_2829])).

cnf(c_65558,plain,
    ( v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_2(sK3,k1_xboole_0,sK1)
    | k2_partfun1(sK0,sK1,sK3,sK2) != sK3
    | sK2 != k1_xboole_0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_65553])).

cnf(c_1470,plain,
    ( X0 != X1
    | X0 = sK3
    | sK3 != X1 ),
    inference(instantiation,[status(thm)],[c_342])).

cnf(c_65452,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k2_partfun1(sK0,sK1,sK3,sK2) = sK3
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_1470])).

cnf(c_77186,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k2_partfun1(sK0,sK1,sK3,X0)
    | k2_partfun1(sK0,sK1,sK3,sK2) = sK3
    | sK3 != k2_partfun1(sK0,sK1,sK3,X0) ),
    inference(instantiation,[status(thm)],[c_65452])).

cnf(c_77187,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k2_partfun1(sK0,sK1,sK3,k1_xboole_0)
    | k2_partfun1(sK0,sK1,sK3,sK2) = sK3
    | sK3 != k2_partfun1(sK0,sK1,sK3,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_77186])).

cnf(c_90475,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_28,c_32,c_31,c_30,c_29,c_27,c_1279,c_1302,c_1480,c_1478,c_1492,c_1682,c_2188,c_2186,c_2527,c_3057,c_4266,c_4331,c_6740,c_7599,c_12067,c_21938,c_31533,c_34369,c_56635,c_56636,c_56641,c_64102,c_65454,c_65558,c_77187])).

cnf(c_96204,plain,
    ( k1_relset_1(sK2,X0,k7_relat_1(k7_relat_1(sK3,X1),sK2)) = k1_relat_1(k7_relat_1(k7_relat_1(sK3,X1),sK2))
    | r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK3,X1),sK2)),X0) != iProver_top
    | v1_relat_1(k7_relat_1(k7_relat_1(sK3,X1),sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_84158,c_32,c_31,c_30,c_29,c_28,c_27,c_105,c_106,c_1279,c_1302,c_1306,c_1480,c_1478,c_1492,c_1682,c_2188,c_2186,c_2527,c_3057,c_4266,c_4331,c_6740,c_7599,c_12067,c_21938,c_31533,c_34369,c_56635,c_56636,c_56641,c_64102,c_65454,c_65558,c_77187])).

cnf(c_8460,plain,
    ( k2_partfun1(sK0,sK1,k7_relat_1(sK3,X0),X1) = k7_relat_1(k7_relat_1(sK3,X0),X1)
    | v1_funct_1(k7_relat_1(sK3,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8451,c_985])).

cnf(c_1499,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1498])).

cnf(c_351,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1576,plain,
    ( v1_funct_1(X0)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,X1))
    | X0 != k2_partfun1(sK0,sK1,sK3,X1) ),
    inference(instantiation,[status(thm)],[c_351])).

cnf(c_5141,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
    | v1_funct_1(k7_relat_1(sK3,X0))
    | k7_relat_1(sK3,X0) != k2_partfun1(sK0,sK1,sK3,X0) ),
    inference(instantiation,[status(thm)],[c_1576])).

cnf(c_5142,plain,
    ( k7_relat_1(sK3,X0) != k2_partfun1(sK0,sK1,sK3,X0)
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5141])).

cnf(c_10026,plain,
    ( k2_partfun1(sK0,sK1,k7_relat_1(sK3,X0),X1) = k7_relat_1(k7_relat_1(sK3,X0),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8460,c_32,c_33,c_30,c_35,c_1499,c_1503,c_3818,c_3819,c_5142])).

cnf(c_10036,plain,
    ( m1_subset_1(k7_relat_1(k7_relat_1(sK3,X0),X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10026,c_987])).

cnf(c_11160,plain,
    ( m1_subset_1(k7_relat_1(k7_relat_1(sK3,X0),X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10036,c_32,c_33,c_30,c_35,c_1499,c_1503,c_1569,c_1919,c_3818,c_3819,c_5142,c_5146])).

cnf(c_11174,plain,
    ( v1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_11160,c_998])).

cnf(c_96213,plain,
    ( k1_relset_1(sK2,X0,k7_relat_1(k7_relat_1(sK3,X1),sK2)) = k1_relat_1(k7_relat_1(k7_relat_1(sK3,X1),sK2))
    | r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK3,X1),sK2)),X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_96204,c_11174])).

cnf(c_96220,plain,
    ( k1_relset_1(sK2,X0,k7_relat_1(k7_relat_1(sK3,sK0),sK2)) = k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK0),sK2))
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4152,c_96213])).

cnf(c_5744,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(sK2,sK2) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5384,c_1001])).

cnf(c_5765,plain,
    ( r1_tarski(sK2,sK2) = iProver_top
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5744,c_35,c_1280])).

cnf(c_5766,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(sK2,sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_5765])).

cnf(c_6461,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_994,c_996])).

cnf(c_28403,plain,
    ( sK1 = k1_xboole_0
    | v4_relat_1(k7_relat_1(sK3,sK2),X0) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5384,c_6461])).

cnf(c_29339,plain,
    ( sK1 = k1_xboole_0
    | v4_relat_1(k7_relat_1(sK3,sK2),X0) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_28403,c_8464])).

cnf(c_29343,plain,
    ( sK1 = k1_xboole_0
    | v4_relat_1(k7_relat_1(sK3,sK2),X0) = iProver_top
    | v5_relat_1(k7_relat_1(sK3,sK2),X1) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1003,c_29339])).

cnf(c_31393,plain,
    ( sK1 = k1_xboole_0
    | v4_relat_1(k7_relat_1(sK3,sK2),X0) = iProver_top
    | v5_relat_1(k7_relat_1(sK3,sK2),X1) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_29343,c_8464])).

cnf(c_31397,plain,
    ( sK1 = k1_xboole_0
    | v4_relat_1(k7_relat_1(sK3,sK2),X0) = iProver_top
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8466,c_31393])).

cnf(c_31405,plain,
    ( k7_relat_1(k7_relat_1(sK3,sK2),X0) = k7_relat_1(sK3,sK2)
    | sK1 = k1_xboole_0
    | r1_tarski(sK2,X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_31397,c_1002])).

cnf(c_72820,plain,
    ( k7_relat_1(k7_relat_1(sK3,sK2),X0) = k7_relat_1(sK3,sK2)
    | sK1 = k1_xboole_0
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_31405,c_8464])).

cnf(c_72826,plain,
    ( k7_relat_1(k7_relat_1(sK3,sK2),sK2) = k7_relat_1(sK3,sK2)
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5766,c_72820])).

cnf(c_4155,plain,
    ( r1_tarski(k1_relat_1(sK3),sK0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4152,c_1001])).

cnf(c_4586,plain,
    ( r1_tarski(k1_relat_1(sK3),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4155,c_35,c_1280])).

cnf(c_5386,plain,
    ( k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3))) = k1_relat_1(sK3)
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4586,c_5375])).

cnf(c_7099,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)),X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,k1_relat_1(sK3)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5386,c_999])).

cnf(c_31788,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)),X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,k1_relat_1(sK3)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7099,c_8464])).

cnf(c_31797,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)),X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4342,c_31788])).

cnf(c_32862,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)),sK2)) = sK2
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_983,c_31797])).

cnf(c_66257,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),k1_relat_1(k7_relat_1(sK3,sK2)))),k1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),sK2))) = iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_65801,c_1001])).

cnf(c_69691,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),k1_relat_1(k7_relat_1(sK3,sK2)))),k1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),sK2))) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_66257,c_8464])).

cnf(c_69709,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)),k1_relat_1(k7_relat_1(sK3,sK2)))),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_32862,c_69691])).

cnf(c_69837,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK0),k1_relat_1(k7_relat_1(sK3,sK2)))),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4342,c_69709])).

cnf(c_69899,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,sK2)))),sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_69837,c_4152])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1005,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1748,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_982,c_1005])).

cnf(c_1834,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1748,c_979])).

cnf(c_1837,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1834,c_35,c_1280])).

cnf(c_7475,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),k1_relat_1(k7_relat_1(sK3,sK2)))) = k1_relat_1(k7_relat_1(sK3,sK2))
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1837,c_5973])).

cnf(c_7618,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),k1_relat_1(k7_relat_1(sK3,sK2))) = iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7475,c_1001])).

cnf(c_12033,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),k1_relat_1(k7_relat_1(sK3,sK2))) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7618,c_8464])).

cnf(c_7617,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5384,c_7475])).

cnf(c_8742,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2),X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,k1_relat_1(k7_relat_1(sK3,sK2))) != iProver_top
    | v1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7617,c_999])).

cnf(c_12040,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2),k1_relat_1(k7_relat_1(sK3,sK2)))) = k1_relat_1(k7_relat_1(sK3,sK2))
    | sK1 = k1_xboole_0
    | v1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12033,c_8742])).

cnf(c_13922,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2),k1_relat_1(k7_relat_1(sK3,sK2)))) = k1_relat_1(k7_relat_1(sK3,sK2))
    | sK1 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_12040,c_11174])).

cnf(c_13923,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2),sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5384,c_13922])).

cnf(c_14716,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2),sK2),X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,k1_relat_1(k7_relat_1(sK3,sK2))) != iProver_top
    | v1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2),sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13923,c_999])).

cnf(c_14747,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2),sK2),X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,k1_relat_1(k7_relat_1(sK3,sK2))) != iProver_top
    | v1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1515,c_14716])).

cnf(c_19131,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2),sK2),X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,k1_relat_1(k7_relat_1(sK3,sK2))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_14747,c_11174])).

cnf(c_19142,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2),sK2),X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5384,c_19131])).

cnf(c_71070,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2),sK2),k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,sK2)))))) = k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,sK2))))
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_69899,c_19142])).

cnf(c_75908,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2),sK2),k1_relat_1(k7_relat_1(sK3,sK2)))) = k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,sK2))))
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5384,c_71070])).

cnf(c_76035,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2),k1_relat_1(k7_relat_1(sK3,sK2)))) = k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,sK2))))
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_72826,c_75908])).

cnf(c_92032,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2),k1_relat_1(k7_relat_1(sK3,sK2)))) = k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,sK2)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_76035,c_32,c_31,c_30,c_29,c_28,c_27,c_105,c_106,c_1279,c_1302,c_1306,c_1480,c_1478,c_1492,c_1682,c_2188,c_2186,c_2527,c_3057,c_4266,c_4331,c_6740,c_7599,c_12067,c_21938,c_31533,c_34369,c_56635,c_56636,c_56641,c_64102,c_65454,c_65558,c_77187])).

cnf(c_33078,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)),sK2)) = k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2))
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_32862,c_8847])).

cnf(c_19202,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2),sK2),k1_relat_1(k7_relat_1(X0,sK2)))) = k1_relat_1(k7_relat_1(X0,sK2))
    | sK1 = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1001,c_19142])).

cnf(c_19550,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2),sK2),k1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),sK2)))) = k1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),sK2))
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8464,c_19202])).

cnf(c_33150,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2),sK2),k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2)))) = k1_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)),sK2))
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_33078,c_19550])).

cnf(c_35756,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2),sK2),k1_relat_1(k7_relat_1(sK3,sK2)))) = k1_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)),sK2))
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7617,c_33150])).

cnf(c_76047,plain,
    ( k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,sK2)))) = k1_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)),sK2))
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_75908,c_35756])).

cnf(c_77415,plain,
    ( k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,sK2)))) = k1_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)),sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_76047,c_32,c_31,c_30,c_29,c_28,c_27,c_105,c_106,c_1279,c_1302,c_1306,c_1480,c_1478,c_1492,c_1682,c_2188,c_2186,c_2527,c_3057,c_4266,c_4331,c_6740,c_7599,c_12067,c_21938,c_31533,c_34369,c_56635,c_56636,c_56641,c_64102,c_65454,c_65558,c_77187])).

cnf(c_77501,plain,
    ( k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,sK2)))) = sK2
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_77415,c_32862])).

cnf(c_77623,plain,
    ( k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,sK2)))) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_77501,c_32,c_31,c_30,c_29,c_28,c_27,c_105,c_106,c_1279,c_1302,c_1306,c_1480,c_1478,c_1492,c_1682,c_2188,c_2186,c_2527,c_3057,c_4266,c_4331,c_6740,c_7599,c_12067,c_21938,c_31533,c_34369,c_56635,c_56636,c_56641,c_64102,c_65454,c_65558,c_77187])).

cnf(c_54811,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,X0)))))) = k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,X0)))) ),
    inference(superposition,[status(thm)],[c_1837,c_47397])).

cnf(c_77669,plain,
    ( k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,sK2)))) = k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2)) ),
    inference(superposition,[status(thm)],[c_77623,c_54811])).

cnf(c_77671,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_77669,c_77623])).

cnf(c_78255,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2),X0)) = X0
    | r1_tarski(X0,sK2) != iProver_top
    | v1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_77671,c_999])).

cnf(c_5976,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2)) = sK2
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5766,c_5964])).

cnf(c_6147,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2),X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK2) != iProver_top
    | v1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5976,c_999])).

cnf(c_14956,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2),X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6147,c_11174])).

cnf(c_79738,plain,
    ( r1_tarski(X0,sK2) != iProver_top
    | k1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2),X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_78255,c_32,c_31,c_30,c_29,c_28,c_27,c_105,c_106,c_1279,c_1302,c_1306,c_1480,c_1478,c_1492,c_1682,c_2188,c_2186,c_2527,c_3057,c_4266,c_4331,c_6740,c_7599,c_12067,c_14956,c_21938,c_31533,c_34369,c_56635,c_56636,c_56641,c_64102,c_65454,c_65558,c_77187])).

cnf(c_79739,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2),X0)) = X0
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_79738])).

cnf(c_79747,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2),k1_relat_1(k7_relat_1(X0,sK2)))) = k1_relat_1(k7_relat_1(X0,sK2))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1001,c_79739])).

cnf(c_81440,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2),k1_relat_1(k7_relat_1(sK3,sK2)))) = k1_relat_1(k7_relat_1(sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_1837,c_79747])).

cnf(c_92034,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_92032,c_77623,c_81440])).

cnf(c_96223,plain,
    ( k1_relset_1(sK2,X0,k7_relat_1(sK3,sK2)) = sK2
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_96220,c_4152,c_92034])).

cnf(c_96469,plain,
    ( k1_relset_1(sK2,X0,k7_relat_1(sK3,sK2)) = sK2
    | v5_relat_1(k7_relat_1(sK3,sK2),X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1003,c_96223])).

cnf(c_96802,plain,
    ( k1_relset_1(sK2,X0,k7_relat_1(sK3,sK2)) = sK2
    | v5_relat_1(k7_relat_1(sK3,sK2),X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_96469,c_8464])).

cnf(c_96806,plain,
    ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_8466,c_96802])).

cnf(c_21,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_990,plain,
    ( k1_relset_1(X0,X1,X2) != X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_103282,plain,
    ( sK1 = k1_xboole_0
    | v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) = iProver_top
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_96806,c_990])).

cnf(c_984,plain,
    ( v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_8220,plain,
    ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8214,c_984])).

cnf(c_986,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2068,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_982,c_986])).

cnf(c_2574,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2068,c_33,c_35,c_1499])).

cnf(c_8221,plain,
    ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8214,c_2574])).

cnf(c_8227,plain,
    ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8220,c_8221])).

cnf(c_105198,plain,
    ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_103282,c_32,c_31,c_30,c_29,c_28,c_27,c_105,c_106,c_1279,c_1302,c_1306,c_1480,c_1478,c_1492,c_1682,c_2188,c_2186,c_2527,c_3057,c_4266,c_4331,c_6740,c_7599,c_8227,c_12067,c_21938,c_31533,c_34369,c_56635,c_56636,c_56641,c_64102,c_65454,c_65558,c_77187])).

cnf(c_105204,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) != iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_994,c_105198])).

cnf(c_105208,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
    | r1_tarski(sK2,sK2) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_105204,c_92034])).

cnf(c_55132,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,X0)))),k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,X0))))) = iProver_top
    | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_54811,c_1001])).

cnf(c_55496,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,X0)))),k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,X0))))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_55132,c_35,c_1280,c_1405,c_1715])).

cnf(c_77667,plain,
    ( r1_tarski(sK2,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_77623,c_55496])).

cnf(c_116254,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_105208,c_32,c_31,c_30,c_35,c_29,c_28,c_27,c_105,c_106,c_1279,c_1280,c_1302,c_1306,c_1480,c_1478,c_1492,c_1682,c_2188,c_2186,c_2527,c_3057,c_4266,c_4331,c_5744,c_6740,c_7599,c_12067,c_21938,c_31533,c_34369,c_56635,c_56636,c_56641,c_64102,c_65454,c_65558,c_77187])).

cnf(c_116260,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_116254,c_8464])).

cnf(c_116262,plain,
    ( v5_relat_1(k7_relat_1(sK3,sK2),sK1) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1003,c_116260])).

cnf(c_116590,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_116262,c_8464,c_8466])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:55:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 31.80/4.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 31.80/4.50  
% 31.80/4.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 31.80/4.50  
% 31.80/4.50  ------  iProver source info
% 31.80/4.50  
% 31.80/4.50  git: date: 2020-06-30 10:37:57 +0100
% 31.80/4.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 31.80/4.50  git: non_committed_changes: false
% 31.80/4.50  git: last_make_outside_of_git: false
% 31.80/4.50  
% 31.80/4.50  ------ 
% 31.80/4.50  ------ Parsing...
% 31.80/4.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 31.80/4.50  
% 31.80/4.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 31.80/4.50  
% 31.80/4.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 31.80/4.50  
% 31.80/4.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.80/4.50  ------ Proving...
% 31.80/4.50  ------ Problem Properties 
% 31.80/4.50  
% 31.80/4.50  
% 31.80/4.50  clauses                                 33
% 31.80/4.50  conjectures                             6
% 31.80/4.50  EPR                                     6
% 31.80/4.50  Horn                                    28
% 31.80/4.50  unary                                   6
% 31.80/4.50  binary                                  10
% 31.80/4.50  lits                                    81
% 31.80/4.50  lits eq                                 21
% 31.80/4.50  fd_pure                                 0
% 31.80/4.50  fd_pseudo                               0
% 31.80/4.50  fd_cond                                 5
% 31.80/4.50  fd_pseudo_cond                          0
% 31.80/4.50  AC symbols                              0
% 31.80/4.50  
% 31.80/4.50  ------ Input Options Time Limit: Unbounded
% 31.80/4.50  
% 31.80/4.50  
% 31.80/4.50  ------ 
% 31.80/4.50  Current options:
% 31.80/4.50  ------ 
% 31.80/4.50  
% 31.80/4.50  
% 31.80/4.50  
% 31.80/4.50  
% 31.80/4.50  ------ Proving...
% 31.80/4.50  
% 31.80/4.50  
% 31.80/4.50  % SZS status Theorem for theBenchmark.p
% 31.80/4.50  
% 31.80/4.50   Resolution empty clause
% 31.80/4.50  
% 31.80/4.50  % SZS output start CNFRefutation for theBenchmark.p
% 31.80/4.50  
% 31.80/4.50  fof(f5,axiom,(
% 31.80/4.50    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 31.80/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.80/4.50  
% 31.80/4.50  fof(f21,plain,(
% 31.80/4.50    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 31.80/4.50    inference(ennf_transformation,[],[f5])).
% 31.80/4.50  
% 31.80/4.50  fof(f44,plain,(
% 31.80/4.50    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 31.80/4.50    inference(nnf_transformation,[],[f21])).
% 31.80/4.50  
% 31.80/4.50  fof(f55,plain,(
% 31.80/4.50    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 31.80/4.50    inference(cnf_transformation,[],[f44])).
% 31.80/4.50  
% 31.80/4.50  fof(f13,axiom,(
% 31.80/4.50    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 31.80/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.80/4.50  
% 31.80/4.50  fof(f31,plain,(
% 31.80/4.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 31.80/4.50    inference(ennf_transformation,[],[f13])).
% 31.80/4.50  
% 31.80/4.50  fof(f32,plain,(
% 31.80/4.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 31.80/4.50    inference(flattening,[],[f31])).
% 31.80/4.50  
% 31.80/4.50  fof(f65,plain,(
% 31.80/4.50    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 31.80/4.50    inference(cnf_transformation,[],[f32])).
% 31.80/4.50  
% 31.80/4.50  fof(f17,conjecture,(
% 31.80/4.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 31.80/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.80/4.50  
% 31.80/4.50  fof(f18,negated_conjecture,(
% 31.80/4.50    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 31.80/4.50    inference(negated_conjecture,[],[f17])).
% 31.80/4.50  
% 31.80/4.50  fof(f39,plain,(
% 31.80/4.50    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 31.80/4.50    inference(ennf_transformation,[],[f18])).
% 31.80/4.50  
% 31.80/4.50  fof(f40,plain,(
% 31.80/4.50    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 31.80/4.50    inference(flattening,[],[f39])).
% 31.80/4.50  
% 31.80/4.50  fof(f46,plain,(
% 31.80/4.50    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 31.80/4.50    introduced(choice_axiom,[])).
% 31.80/4.50  
% 31.80/4.50  fof(f47,plain,(
% 31.80/4.50    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 31.80/4.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f40,f46])).
% 31.80/4.50  
% 31.80/4.50  fof(f77,plain,(
% 31.80/4.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 31.80/4.50    inference(cnf_transformation,[],[f47])).
% 31.80/4.50  
% 31.80/4.50  fof(f16,axiom,(
% 31.80/4.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 31.80/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.80/4.50  
% 31.80/4.50  fof(f37,plain,(
% 31.80/4.50    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 31.80/4.50    inference(ennf_transformation,[],[f16])).
% 31.80/4.50  
% 31.80/4.50  fof(f38,plain,(
% 31.80/4.50    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 31.80/4.50    inference(flattening,[],[f37])).
% 31.80/4.50  
% 31.80/4.50  fof(f74,plain,(
% 31.80/4.50    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 31.80/4.50    inference(cnf_transformation,[],[f38])).
% 31.80/4.50  
% 31.80/4.50  fof(f75,plain,(
% 31.80/4.50    v1_funct_1(sK3)),
% 31.80/4.50    inference(cnf_transformation,[],[f47])).
% 31.80/4.50  
% 31.80/4.50  fof(f15,axiom,(
% 31.80/4.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 31.80/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.80/4.50  
% 31.80/4.50  fof(f35,plain,(
% 31.80/4.50    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 31.80/4.50    inference(ennf_transformation,[],[f15])).
% 31.80/4.50  
% 31.80/4.50  fof(f36,plain,(
% 31.80/4.50    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 31.80/4.50    inference(flattening,[],[f35])).
% 31.80/4.50  
% 31.80/4.50  fof(f73,plain,(
% 31.80/4.50    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 31.80/4.50    inference(cnf_transformation,[],[f36])).
% 31.80/4.50  
% 31.80/4.50  fof(f11,axiom,(
% 31.80/4.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 31.80/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.80/4.50  
% 31.80/4.50  fof(f29,plain,(
% 31.80/4.50    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.80/4.50    inference(ennf_transformation,[],[f11])).
% 31.80/4.50  
% 31.80/4.50  fof(f63,plain,(
% 31.80/4.50    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 31.80/4.50    inference(cnf_transformation,[],[f29])).
% 31.80/4.50  
% 31.80/4.50  fof(f62,plain,(
% 31.80/4.50    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 31.80/4.50    inference(cnf_transformation,[],[f29])).
% 31.80/4.50  
% 31.80/4.50  fof(f6,axiom,(
% 31.80/4.50    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 31.80/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.80/4.50  
% 31.80/4.50  fof(f22,plain,(
% 31.80/4.50    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 31.80/4.50    inference(ennf_transformation,[],[f6])).
% 31.80/4.50  
% 31.80/4.50  fof(f23,plain,(
% 31.80/4.50    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 31.80/4.50    inference(flattening,[],[f22])).
% 31.80/4.50  
% 31.80/4.50  fof(f57,plain,(
% 31.80/4.50    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 31.80/4.50    inference(cnf_transformation,[],[f23])).
% 31.80/4.50  
% 31.80/4.50  fof(f10,axiom,(
% 31.80/4.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 31.80/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.80/4.50  
% 31.80/4.50  fof(f28,plain,(
% 31.80/4.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.80/4.50    inference(ennf_transformation,[],[f10])).
% 31.80/4.50  
% 31.80/4.50  fof(f61,plain,(
% 31.80/4.50    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 31.80/4.50    inference(cnf_transformation,[],[f28])).
% 31.80/4.50  
% 31.80/4.50  fof(f78,plain,(
% 31.80/4.50    r1_tarski(sK2,sK0)),
% 31.80/4.50    inference(cnf_transformation,[],[f47])).
% 31.80/4.50  
% 31.80/4.50  fof(f14,axiom,(
% 31.80/4.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 31.80/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.80/4.50  
% 31.80/4.50  fof(f33,plain,(
% 31.80/4.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.80/4.50    inference(ennf_transformation,[],[f14])).
% 31.80/4.50  
% 31.80/4.50  fof(f34,plain,(
% 31.80/4.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.80/4.50    inference(flattening,[],[f33])).
% 31.80/4.50  
% 31.80/4.50  fof(f45,plain,(
% 31.80/4.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.80/4.50    inference(nnf_transformation,[],[f34])).
% 31.80/4.50  
% 31.80/4.50  fof(f66,plain,(
% 31.80/4.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 31.80/4.50    inference(cnf_transformation,[],[f45])).
% 31.80/4.50  
% 31.80/4.50  fof(f12,axiom,(
% 31.80/4.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 31.80/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.80/4.50  
% 31.80/4.50  fof(f30,plain,(
% 31.80/4.50    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.80/4.50    inference(ennf_transformation,[],[f12])).
% 31.80/4.50  
% 31.80/4.50  fof(f64,plain,(
% 31.80/4.50    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 31.80/4.50    inference(cnf_transformation,[],[f30])).
% 31.80/4.50  
% 31.80/4.50  fof(f76,plain,(
% 31.80/4.50    v1_funct_2(sK3,sK0,sK1)),
% 31.80/4.50    inference(cnf_transformation,[],[f47])).
% 31.80/4.50  
% 31.80/4.50  fof(f9,axiom,(
% 31.80/4.50    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 31.80/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.80/4.50  
% 31.80/4.50  fof(f26,plain,(
% 31.80/4.50    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 31.80/4.50    inference(ennf_transformation,[],[f9])).
% 31.80/4.50  
% 31.80/4.50  fof(f27,plain,(
% 31.80/4.50    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 31.80/4.50    inference(flattening,[],[f26])).
% 31.80/4.50  
% 31.80/4.50  fof(f60,plain,(
% 31.80/4.50    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 31.80/4.50    inference(cnf_transformation,[],[f27])).
% 31.80/4.50  
% 31.80/4.50  fof(f7,axiom,(
% 31.80/4.50    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 31.80/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.80/4.50  
% 31.80/4.50  fof(f24,plain,(
% 31.80/4.50    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 31.80/4.50    inference(ennf_transformation,[],[f7])).
% 31.80/4.50  
% 31.80/4.50  fof(f58,plain,(
% 31.80/4.50    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 31.80/4.50    inference(cnf_transformation,[],[f24])).
% 31.80/4.50  
% 31.80/4.50  fof(f8,axiom,(
% 31.80/4.50    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 31.80/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.80/4.50  
% 31.80/4.50  fof(f25,plain,(
% 31.80/4.50    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 31.80/4.50    inference(ennf_transformation,[],[f8])).
% 31.80/4.50  
% 31.80/4.50  fof(f59,plain,(
% 31.80/4.50    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 31.80/4.50    inference(cnf_transformation,[],[f25])).
% 31.80/4.50  
% 31.80/4.50  fof(f4,axiom,(
% 31.80/4.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 31.80/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.80/4.50  
% 31.80/4.50  fof(f20,plain,(
% 31.80/4.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 31.80/4.50    inference(ennf_transformation,[],[f4])).
% 31.80/4.50  
% 31.80/4.50  fof(f54,plain,(
% 31.80/4.50    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 31.80/4.50    inference(cnf_transformation,[],[f20])).
% 31.80/4.50  
% 31.80/4.50  fof(f3,axiom,(
% 31.80/4.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 31.80/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.80/4.50  
% 31.80/4.50  fof(f43,plain,(
% 31.80/4.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 31.80/4.50    inference(nnf_transformation,[],[f3])).
% 31.80/4.50  
% 31.80/4.50  fof(f53,plain,(
% 31.80/4.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 31.80/4.50    inference(cnf_transformation,[],[f43])).
% 31.80/4.50  
% 31.80/4.50  fof(f2,axiom,(
% 31.80/4.50    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 31.80/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.80/4.50  
% 31.80/4.50  fof(f41,plain,(
% 31.80/4.50    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 31.80/4.50    inference(nnf_transformation,[],[f2])).
% 31.80/4.50  
% 31.80/4.50  fof(f42,plain,(
% 31.80/4.50    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 31.80/4.50    inference(flattening,[],[f41])).
% 31.80/4.50  
% 31.80/4.50  fof(f49,plain,(
% 31.80/4.50    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 31.80/4.50    inference(cnf_transformation,[],[f42])).
% 31.80/4.50  
% 31.80/4.50  fof(f50,plain,(
% 31.80/4.50    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 31.80/4.50    inference(cnf_transformation,[],[f42])).
% 31.80/4.50  
% 31.80/4.50  fof(f82,plain,(
% 31.80/4.50    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 31.80/4.50    inference(equality_resolution,[],[f50])).
% 31.80/4.50  
% 31.80/4.50  fof(f79,plain,(
% 31.80/4.50    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 31.80/4.50    inference(cnf_transformation,[],[f47])).
% 31.80/4.50  
% 31.80/4.50  fof(f80,plain,(
% 31.80/4.50    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 31.80/4.50    inference(cnf_transformation,[],[f47])).
% 31.80/4.50  
% 31.80/4.50  fof(f1,axiom,(
% 31.80/4.50    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 31.80/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.80/4.50  
% 31.80/4.50  fof(f19,plain,(
% 31.80/4.50    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 31.80/4.50    inference(ennf_transformation,[],[f1])).
% 31.80/4.50  
% 31.80/4.50  fof(f48,plain,(
% 31.80/4.50    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 31.80/4.50    inference(cnf_transformation,[],[f19])).
% 31.80/4.50  
% 31.80/4.50  fof(f72,plain,(
% 31.80/4.50    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 31.80/4.50    inference(cnf_transformation,[],[f36])).
% 31.80/4.50  
% 31.80/4.50  fof(f52,plain,(
% 31.80/4.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 31.80/4.50    inference(cnf_transformation,[],[f43])).
% 31.80/4.50  
% 31.80/4.50  fof(f68,plain,(
% 31.80/4.50    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 31.80/4.50    inference(cnf_transformation,[],[f45])).
% 31.80/4.50  
% 31.80/4.50  cnf(c_8,plain,
% 31.80/4.50      ( ~ v5_relat_1(X0,X1) | r1_tarski(k2_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 31.80/4.50      inference(cnf_transformation,[],[f55]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_1003,plain,
% 31.80/4.50      ( v5_relat_1(X0,X1) != iProver_top
% 31.80/4.50      | r1_tarski(k2_relat_1(X0),X1) = iProver_top
% 31.80/4.50      | v1_relat_1(X0) != iProver_top ),
% 31.80/4.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_17,plain,
% 31.80/4.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.80/4.50      | ~ r1_tarski(k1_relat_1(X0),X1)
% 31.80/4.50      | ~ r1_tarski(k2_relat_1(X0),X2)
% 31.80/4.50      | ~ v1_relat_1(X0) ),
% 31.80/4.50      inference(cnf_transformation,[],[f65]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_994,plain,
% 31.80/4.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 31.80/4.50      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 31.80/4.50      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 31.80/4.50      | v1_relat_1(X0) != iProver_top ),
% 31.80/4.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_30,negated_conjecture,
% 31.80/4.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 31.80/4.50      inference(cnf_transformation,[],[f77]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_982,plain,
% 31.80/4.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 31.80/4.50      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_26,plain,
% 31.80/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.80/4.50      | ~ v1_funct_1(X0)
% 31.80/4.50      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 31.80/4.50      inference(cnf_transformation,[],[f74]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_985,plain,
% 31.80/4.50      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 31.80/4.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 31.80/4.50      | v1_funct_1(X2) != iProver_top ),
% 31.80/4.50      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_7993,plain,
% 31.80/4.50      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
% 31.80/4.50      | v1_funct_1(sK3) != iProver_top ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_982,c_985]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_32,negated_conjecture,
% 31.80/4.50      ( v1_funct_1(sK3) ),
% 31.80/4.50      inference(cnf_transformation,[],[f75]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_1350,plain,
% 31.80/4.50      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 31.80/4.50      | ~ v1_funct_1(sK3)
% 31.80/4.50      | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_26]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_1503,plain,
% 31.80/4.50      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 31.80/4.50      | ~ v1_funct_1(sK3)
% 31.80/4.50      | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_1350]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_8214,plain,
% 31.80/4.50      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 31.80/4.50      inference(global_propositional_subsumption,
% 31.80/4.50                [status(thm)],
% 31.80/4.50                [c_7993,c_32,c_30,c_1503]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_24,plain,
% 31.80/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.80/4.50      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.80/4.50      | ~ v1_funct_1(X0) ),
% 31.80/4.50      inference(cnf_transformation,[],[f73]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_987,plain,
% 31.80/4.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 31.80/4.50      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 31.80/4.50      | v1_funct_1(X0) != iProver_top ),
% 31.80/4.50      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_8251,plain,
% 31.80/4.50      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 31.80/4.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 31.80/4.50      | v1_funct_1(sK3) != iProver_top ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_8214,c_987]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_33,plain,
% 31.80/4.50      ( v1_funct_1(sK3) = iProver_top ),
% 31.80/4.50      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_35,plain,
% 31.80/4.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 31.80/4.50      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_1345,plain,
% 31.80/4.50      ( m1_subset_1(k2_partfun1(X0,X1,sK3,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 31.80/4.50      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 31.80/4.50      | ~ v1_funct_1(sK3) ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_24]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_1568,plain,
% 31.80/4.50      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 31.80/4.50      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 31.80/4.50      | ~ v1_funct_1(sK3) ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_1345]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_1569,plain,
% 31.80/4.50      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 31.80/4.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 31.80/4.50      | v1_funct_1(sK3) != iProver_top ),
% 31.80/4.50      inference(predicate_to_equality,[status(thm)],[c_1568]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_341,plain,( X0 = X0 ),theory(equality) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_1919,plain,
% 31.80/4.50      ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_341]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_342,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_1903,plain,
% 31.80/4.50      ( X0 != X1
% 31.80/4.50      | X0 = k2_partfun1(sK0,sK1,sK3,X2)
% 31.80/4.50      | k2_partfun1(sK0,sK1,sK3,X2) != X1 ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_342]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_3352,plain,
% 31.80/4.50      ( X0 = k2_partfun1(sK0,sK1,sK3,X1)
% 31.80/4.50      | X0 != k7_relat_1(sK3,X1)
% 31.80/4.50      | k2_partfun1(sK0,sK1,sK3,X1) != k7_relat_1(sK3,X1) ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_1903]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_3818,plain,
% 31.80/4.50      ( k2_partfun1(sK0,sK1,sK3,X0) != k7_relat_1(sK3,X0)
% 31.80/4.50      | k7_relat_1(sK3,X0) = k2_partfun1(sK0,sK1,sK3,X0)
% 31.80/4.50      | k7_relat_1(sK3,X0) != k7_relat_1(sK3,X0) ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_3352]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_3819,plain,
% 31.80/4.50      ( k7_relat_1(sK3,X0) = k7_relat_1(sK3,X0) ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_341]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_346,plain,
% 31.80/4.50      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 31.80/4.50      theory(equality) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_1623,plain,
% 31.80/4.50      ( m1_subset_1(X0,X1)
% 31.80/4.50      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,X2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 31.80/4.50      | X0 != k2_partfun1(sK0,sK1,sK3,X2)
% 31.80/4.50      | X1 != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_346]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_1918,plain,
% 31.80/4.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 31.80/4.50      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 31.80/4.50      | X0 != k2_partfun1(sK0,sK1,sK3,X1)
% 31.80/4.50      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_1623]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_5140,plain,
% 31.80/4.50      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 31.80/4.50      | m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 31.80/4.50      | k7_relat_1(sK3,X0) != k2_partfun1(sK0,sK1,sK3,X0)
% 31.80/4.50      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_1918]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_5146,plain,
% 31.80/4.50      ( k7_relat_1(sK3,X0) != k2_partfun1(sK0,sK1,sK3,X0)
% 31.80/4.50      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 31.80/4.50      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 31.80/4.50      | m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 31.80/4.50      inference(predicate_to_equality,[status(thm)],[c_5140]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_8451,plain,
% 31.80/4.50      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 31.80/4.50      inference(global_propositional_subsumption,
% 31.80/4.50                [status(thm)],
% 31.80/4.50                [c_8251,c_32,c_33,c_30,c_35,c_1503,c_1569,c_1919,c_3818,
% 31.80/4.50                 c_3819,c_5146]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_14,plain,
% 31.80/4.50      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 31.80/4.50      inference(cnf_transformation,[],[f63]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_997,plain,
% 31.80/4.50      ( v5_relat_1(X0,X1) = iProver_top
% 31.80/4.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
% 31.80/4.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_8466,plain,
% 31.80/4.50      ( v5_relat_1(k7_relat_1(sK3,X0),sK1) = iProver_top ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_8451,c_997]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_15,plain,
% 31.80/4.50      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 31.80/4.50      inference(cnf_transformation,[],[f62]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_996,plain,
% 31.80/4.50      ( v4_relat_1(X0,X1) = iProver_top
% 31.80/4.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 31.80/4.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_2420,plain,
% 31.80/4.50      ( v4_relat_1(sK3,sK0) = iProver_top ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_982,c_996]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_9,plain,
% 31.80/4.50      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 31.80/4.50      inference(cnf_transformation,[],[f57]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_1002,plain,
% 31.80/4.50      ( k7_relat_1(X0,X1) = X0
% 31.80/4.50      | v4_relat_1(X0,X1) != iProver_top
% 31.80/4.50      | v1_relat_1(X0) != iProver_top ),
% 31.80/4.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_4015,plain,
% 31.80/4.50      ( k7_relat_1(sK3,sK0) = sK3 | v1_relat_1(sK3) != iProver_top ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_2420,c_1002]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_13,plain,
% 31.80/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 31.80/4.50      inference(cnf_transformation,[],[f61]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_1279,plain,
% 31.80/4.50      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 31.80/4.50      | v1_relat_1(sK3) ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_13]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_1302,plain,
% 31.80/4.50      ( v4_relat_1(sK3,sK0)
% 31.80/4.50      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_15]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_1397,plain,
% 31.80/4.50      ( ~ v4_relat_1(sK3,X0) | ~ v1_relat_1(sK3) | k7_relat_1(sK3,X0) = sK3 ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_9]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_1682,plain,
% 31.80/4.50      ( ~ v4_relat_1(sK3,sK0) | ~ v1_relat_1(sK3) | k7_relat_1(sK3,sK0) = sK3 ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_1397]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_4152,plain,
% 31.80/4.50      ( k7_relat_1(sK3,sK0) = sK3 ),
% 31.80/4.50      inference(global_propositional_subsumption,
% 31.80/4.50                [status(thm)],
% 31.80/4.50                [c_4015,c_30,c_1279,c_1302,c_1682]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_29,negated_conjecture,
% 31.80/4.50      ( r1_tarski(sK2,sK0) ),
% 31.80/4.50      inference(cnf_transformation,[],[f78]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_983,plain,
% 31.80/4.50      ( r1_tarski(sK2,sK0) = iProver_top ),
% 31.80/4.50      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_23,plain,
% 31.80/4.50      ( ~ v1_funct_2(X0,X1,X2)
% 31.80/4.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.80/4.50      | k1_relset_1(X1,X2,X0) = X1
% 31.80/4.50      | k1_xboole_0 = X2 ),
% 31.80/4.50      inference(cnf_transformation,[],[f66]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_988,plain,
% 31.80/4.50      ( k1_relset_1(X0,X1,X2) = X0
% 31.80/4.50      | k1_xboole_0 = X1
% 31.80/4.50      | v1_funct_2(X2,X0,X1) != iProver_top
% 31.80/4.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 31.80/4.50      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_3869,plain,
% 31.80/4.50      ( k1_relset_1(sK0,sK1,sK3) = sK0
% 31.80/4.50      | sK1 = k1_xboole_0
% 31.80/4.50      | v1_funct_2(sK3,sK0,sK1) != iProver_top ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_982,c_988]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_16,plain,
% 31.80/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.80/4.50      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 31.80/4.50      inference(cnf_transformation,[],[f64]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_995,plain,
% 31.80/4.50      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 31.80/4.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 31.80/4.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_3234,plain,
% 31.80/4.50      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_982,c_995]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_3883,plain,
% 31.80/4.50      ( k1_relat_1(sK3) = sK0
% 31.80/4.50      | sK1 = k1_xboole_0
% 31.80/4.50      | v1_funct_2(sK3,sK0,sK1) != iProver_top ),
% 31.80/4.50      inference(demodulation,[status(thm)],[c_3869,c_3234]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_31,negated_conjecture,
% 31.80/4.50      ( v1_funct_2(sK3,sK0,sK1) ),
% 31.80/4.50      inference(cnf_transformation,[],[f76]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_34,plain,
% 31.80/4.50      ( v1_funct_2(sK3,sK0,sK1) = iProver_top ),
% 31.80/4.50      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_4341,plain,
% 31.80/4.50      ( sK1 = k1_xboole_0 | k1_relat_1(sK3) = sK0 ),
% 31.80/4.50      inference(global_propositional_subsumption,[status(thm)],[c_3883,c_34]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_4342,plain,
% 31.80/4.50      ( k1_relat_1(sK3) = sK0 | sK1 = k1_xboole_0 ),
% 31.80/4.50      inference(renaming,[status(thm)],[c_4341]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_12,plain,
% 31.80/4.50      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 31.80/4.50      | ~ v1_relat_1(X1)
% 31.80/4.50      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 31.80/4.50      inference(cnf_transformation,[],[f60]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_999,plain,
% 31.80/4.50      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 31.80/4.50      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 31.80/4.50      | v1_relat_1(X0) != iProver_top ),
% 31.80/4.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_5205,plain,
% 31.80/4.50      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 31.80/4.50      | sK1 = k1_xboole_0
% 31.80/4.50      | r1_tarski(X0,sK0) != iProver_top
% 31.80/4.50      | v1_relat_1(sK3) != iProver_top ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_4342,c_999]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_1280,plain,
% 31.80/4.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 31.80/4.50      | v1_relat_1(sK3) = iProver_top ),
% 31.80/4.50      inference(predicate_to_equality,[status(thm)],[c_1279]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_5374,plain,
% 31.80/4.50      ( r1_tarski(X0,sK0) != iProver_top
% 31.80/4.50      | sK1 = k1_xboole_0
% 31.80/4.50      | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
% 31.80/4.50      inference(global_propositional_subsumption,
% 31.80/4.50                [status(thm)],
% 31.80/4.50                [c_5205,c_35,c_1280]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_5375,plain,
% 31.80/4.50      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 31.80/4.50      | sK1 = k1_xboole_0
% 31.80/4.50      | r1_tarski(X0,sK0) != iProver_top ),
% 31.80/4.50      inference(renaming,[status(thm)],[c_5374]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_5384,plain,
% 31.80/4.50      ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2 | sK1 = k1_xboole_0 ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_983,c_5375]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_998,plain,
% 31.80/4.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 31.80/4.50      | v1_relat_1(X0) = iProver_top ),
% 31.80/4.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_8464,plain,
% 31.80/4.50      ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_8451,c_998]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_10,plain,
% 31.80/4.50      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 31.80/4.50      inference(cnf_transformation,[],[f58]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_1001,plain,
% 31.80/4.50      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
% 31.80/4.50      | v1_relat_1(X0) != iProver_top ),
% 31.80/4.50      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_5201,plain,
% 31.80/4.50      ( k1_relat_1(k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))) = k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))
% 31.80/4.50      | v1_relat_1(X1) != iProver_top
% 31.80/4.50      | v1_relat_1(X0) != iProver_top ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_1001,c_999]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_47397,plain,
% 31.80/4.50      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),k1_relat_1(k7_relat_1(X1,k1_relat_1(k7_relat_1(sK3,X0)))))) = k1_relat_1(k7_relat_1(X1,k1_relat_1(k7_relat_1(sK3,X0))))
% 31.80/4.50      | v1_relat_1(X1) != iProver_top ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_8464,c_5201]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_54813,plain,
% 31.80/4.50      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),k1_relat_1(k7_relat_1(k7_relat_1(sK3,X1),k1_relat_1(k7_relat_1(sK3,X0)))))) = k1_relat_1(k7_relat_1(k7_relat_1(sK3,X1),k1_relat_1(k7_relat_1(sK3,X0)))) ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_8464,c_47397]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_65801,plain,
% 31.80/4.50      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),k1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),sK2)))) = k1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),k1_relat_1(k7_relat_1(sK3,sK2))))
% 31.80/4.50      | sK1 = k1_xboole_0 ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_5384,c_54813]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_11,plain,
% 31.80/4.50      ( r1_tarski(k7_relat_1(X0,X1),X0) | ~ v1_relat_1(X0) ),
% 31.80/4.50      inference(cnf_transformation,[],[f59]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_1000,plain,
% 31.80/4.50      ( r1_tarski(k7_relat_1(X0,X1),X0) = iProver_top
% 31.80/4.50      | v1_relat_1(X0) != iProver_top ),
% 31.80/4.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_6,plain,
% 31.80/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 31.80/4.50      inference(cnf_transformation,[],[f54]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_4,plain,
% 31.80/4.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 31.80/4.50      inference(cnf_transformation,[],[f53]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_208,plain,
% 31.80/4.50      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 31.80/4.50      inference(prop_impl,[status(thm)],[c_4]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_209,plain,
% 31.80/4.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 31.80/4.50      inference(renaming,[status(thm)],[c_208]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_269,plain,
% 31.80/4.50      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 31.80/4.50      inference(bin_hyper_res,[status(thm)],[c_6,c_209]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_979,plain,
% 31.80/4.50      ( r1_tarski(X0,X1) != iProver_top
% 31.80/4.50      | v1_relat_1(X1) != iProver_top
% 31.80/4.50      | v1_relat_1(X0) = iProver_top ),
% 31.80/4.50      inference(predicate_to_equality,[status(thm)],[c_269]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_1515,plain,
% 31.80/4.50      ( v1_relat_1(X0) != iProver_top
% 31.80/4.50      | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_1000,c_979]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_5745,plain,
% 31.80/4.50      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),X0)) = X0
% 31.80/4.50      | sK1 = k1_xboole_0
% 31.80/4.50      | r1_tarski(X0,sK2) != iProver_top
% 31.80/4.50      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_5384,c_999]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_5958,plain,
% 31.80/4.50      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),X0)) = X0
% 31.80/4.50      | sK1 = k1_xboole_0
% 31.80/4.50      | r1_tarski(X0,sK2) != iProver_top
% 31.80/4.50      | v1_relat_1(sK3) != iProver_top ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_1515,c_5745]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_5963,plain,
% 31.80/4.50      ( r1_tarski(X0,sK2) != iProver_top
% 31.80/4.50      | sK1 = k1_xboole_0
% 31.80/4.50      | k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),X0)) = X0 ),
% 31.80/4.50      inference(global_propositional_subsumption,
% 31.80/4.50                [status(thm)],
% 31.80/4.50                [c_5958,c_35,c_1280]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_5964,plain,
% 31.80/4.50      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),X0)) = X0
% 31.80/4.50      | sK1 = k1_xboole_0
% 31.80/4.50      | r1_tarski(X0,sK2) != iProver_top ),
% 31.80/4.50      inference(renaming,[status(thm)],[c_5963]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_5973,plain,
% 31.80/4.50      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),k1_relat_1(k7_relat_1(X0,sK2)))) = k1_relat_1(k7_relat_1(X0,sK2))
% 31.80/4.50      | sK1 = k1_xboole_0
% 31.80/4.50      | v1_relat_1(X0) != iProver_top ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_1001,c_5964]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_8847,plain,
% 31.80/4.50      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),k1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),sK2)))) = k1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),sK2))
% 31.80/4.50      | sK1 = k1_xboole_0 ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_8464,c_5973]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_66265,plain,
% 31.80/4.50      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),k1_relat_1(k7_relat_1(sK3,sK2)))) = k1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),sK2))
% 31.80/4.50      | sK1 = k1_xboole_0 ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_65801,c_8847]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_66964,plain,
% 31.80/4.50      ( sK1 = k1_xboole_0
% 31.80/4.50      | r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),sK2)),k1_relat_1(k7_relat_1(sK3,sK2))) = iProver_top
% 31.80/4.50      | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_66265,c_1001]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_1399,plain,
% 31.80/4.50      ( r1_tarski(k7_relat_1(sK3,X0),sK3) | ~ v1_relat_1(sK3) ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_11]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_1405,plain,
% 31.80/4.50      ( r1_tarski(k7_relat_1(sK3,X0),sK3) = iProver_top
% 31.80/4.50      | v1_relat_1(sK3) != iProver_top ),
% 31.80/4.50      inference(predicate_to_equality,[status(thm)],[c_1399]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_1417,plain,
% 31.80/4.50      ( ~ r1_tarski(X0,sK3) | v1_relat_1(X0) | ~ v1_relat_1(sK3) ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_269]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_1714,plain,
% 31.80/4.50      ( ~ r1_tarski(k7_relat_1(sK3,X0),sK3)
% 31.80/4.50      | v1_relat_1(k7_relat_1(sK3,X0))
% 31.80/4.50      | ~ v1_relat_1(sK3) ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_1417]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_1715,plain,
% 31.80/4.50      ( r1_tarski(k7_relat_1(sK3,X0),sK3) != iProver_top
% 31.80/4.50      | v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top
% 31.80/4.50      | v1_relat_1(sK3) != iProver_top ),
% 31.80/4.50      inference(predicate_to_equality,[status(thm)],[c_1714]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_67617,plain,
% 31.80/4.50      ( r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),sK2)),k1_relat_1(k7_relat_1(sK3,sK2))) = iProver_top
% 31.80/4.50      | sK1 = k1_xboole_0 ),
% 31.80/4.50      inference(global_propositional_subsumption,
% 31.80/4.50                [status(thm)],
% 31.80/4.50                [c_66964,c_35,c_1280,c_1405,c_1715]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_67618,plain,
% 31.80/4.50      ( sK1 = k1_xboole_0
% 31.80/4.50      | r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),sK2)),k1_relat_1(k7_relat_1(sK3,sK2))) = iProver_top ),
% 31.80/4.50      inference(renaming,[status(thm)],[c_67617]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_67631,plain,
% 31.80/4.50      ( sK1 = k1_xboole_0
% 31.80/4.50      | r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),sK2)),sK2) = iProver_top ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_5384,c_67618]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_6460,plain,
% 31.80/4.50      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 31.80/4.50      | r1_tarski(k1_relat_1(X2),X0) != iProver_top
% 31.80/4.50      | r1_tarski(k2_relat_1(X2),X1) != iProver_top
% 31.80/4.50      | v1_relat_1(X2) != iProver_top ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_994,c_995]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_84158,plain,
% 31.80/4.50      ( k1_relset_1(sK2,X0,k7_relat_1(k7_relat_1(sK3,X1),sK2)) = k1_relat_1(k7_relat_1(k7_relat_1(sK3,X1),sK2))
% 31.80/4.50      | sK1 = k1_xboole_0
% 31.80/4.50      | r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK3,X1),sK2)),X0) != iProver_top
% 31.80/4.50      | v1_relat_1(k7_relat_1(k7_relat_1(sK3,X1),sK2)) != iProver_top ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_67631,c_6460]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_3,plain,
% 31.80/4.50      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 31.80/4.50      | k1_xboole_0 = X0
% 31.80/4.50      | k1_xboole_0 = X1 ),
% 31.80/4.50      inference(cnf_transformation,[],[f49]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_105,plain,
% 31.80/4.50      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 31.80/4.50      | k1_xboole_0 = k1_xboole_0 ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_3]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_2,plain,
% 31.80/4.50      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 31.80/4.50      inference(cnf_transformation,[],[f82]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_106,plain,
% 31.80/4.50      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_2]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_1305,plain,
% 31.80/4.50      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_342]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_1306,plain,
% 31.80/4.50      ( sK1 != k1_xboole_0 | k1_xboole_0 = sK1 | k1_xboole_0 != k1_xboole_0 ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_1305]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_28,negated_conjecture,
% 31.80/4.50      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 31.80/4.50      inference(cnf_transformation,[],[f79]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_27,negated_conjecture,
% 31.80/4.50      ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
% 31.80/4.50      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 31.80/4.50      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
% 31.80/4.50      inference(cnf_transformation,[],[f80]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_343,plain,
% 31.80/4.50      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 31.80/4.50      theory(equality) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_1335,plain,
% 31.80/4.50      ( r1_tarski(X0,X1) | ~ r1_tarski(sK2,sK0) | X0 != sK2 | X1 != sK0 ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_343]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_1477,plain,
% 31.80/4.50      ( r1_tarski(sK2,X0) | ~ r1_tarski(sK2,sK0) | X0 != sK0 | sK2 != sK2 ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_1335]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_1480,plain,
% 31.80/4.50      ( ~ r1_tarski(sK2,sK0)
% 31.80/4.50      | r1_tarski(sK2,k1_xboole_0)
% 31.80/4.50      | sK2 != sK2
% 31.80/4.50      | k1_xboole_0 != sK0 ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_1477]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_1478,plain,
% 31.80/4.50      ( sK2 = sK2 ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_341]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_1492,plain,
% 31.80/4.50      ( sK3 = sK3 ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_341]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_349,plain,
% 31.80/4.50      ( ~ v1_funct_2(X0,X1,X2)
% 31.80/4.50      | v1_funct_2(X3,X4,X5)
% 31.80/4.50      | X3 != X0
% 31.80/4.50      | X4 != X1
% 31.80/4.50      | X5 != X2 ),
% 31.80/4.50      theory(equality) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_1380,plain,
% 31.80/4.50      ( v1_funct_2(X0,X1,X2)
% 31.80/4.50      | ~ v1_funct_2(sK3,sK0,sK1)
% 31.80/4.50      | X0 != sK3
% 31.80/4.50      | X2 != sK1
% 31.80/4.50      | X1 != sK0 ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_349]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_1665,plain,
% 31.80/4.50      ( v1_funct_2(sK3,X0,X1)
% 31.80/4.50      | ~ v1_funct_2(sK3,sK0,sK1)
% 31.80/4.50      | X1 != sK1
% 31.80/4.50      | X0 != sK0
% 31.80/4.50      | sK3 != sK3 ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_1380]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_2185,plain,
% 31.80/4.50      ( v1_funct_2(sK3,X0,sK1)
% 31.80/4.50      | ~ v1_funct_2(sK3,sK0,sK1)
% 31.80/4.50      | X0 != sK0
% 31.80/4.50      | sK3 != sK3
% 31.80/4.50      | sK1 != sK1 ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_1665]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_2188,plain,
% 31.80/4.50      ( ~ v1_funct_2(sK3,sK0,sK1)
% 31.80/4.50      | v1_funct_2(sK3,k1_xboole_0,sK1)
% 31.80/4.50      | sK3 != sK3
% 31.80/4.50      | sK1 != sK1
% 31.80/4.50      | k1_xboole_0 != sK0 ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_2185]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_2186,plain,
% 31.80/4.50      ( sK1 = sK1 ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_341]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_0,plain,
% 31.80/4.50      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 31.80/4.50      inference(cnf_transformation,[],[f48]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_2527,plain,
% 31.80/4.50      ( ~ r1_tarski(sK2,k1_xboole_0) | k1_xboole_0 = sK2 ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_0]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_1894,plain,
% 31.80/4.50      ( X0 != X1 | sK2 != X1 | sK2 = X0 ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_342]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_3056,plain,
% 31.80/4.50      ( X0 != sK2 | sK2 = X0 | sK2 != sK2 ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_1894]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_3057,plain,
% 31.80/4.50      ( sK2 != sK2 | sK2 = k1_xboole_0 | k1_xboole_0 != sK2 ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_3056]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_4266,plain,
% 31.80/4.50      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 31.80/4.50      | ~ v1_funct_1(sK3)
% 31.80/4.50      | k2_partfun1(sK0,sK1,sK3,sK0) = k7_relat_1(sK3,sK0) ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_1503]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_1774,plain,
% 31.80/4.50      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_342]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_2928,plain,
% 31.80/4.50      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_1774]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_4331,plain,
% 31.80/4.50      ( k7_relat_1(sK3,sK0) != sK3 | sK3 = k7_relat_1(sK3,sK0) | sK3 != sK3 ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_2928]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_6740,plain,
% 31.80/4.50      ( sK0 = sK0 ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_341]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_7599,plain,
% 31.80/4.50      ( k2_partfun1(sK0,sK1,sK3,sK0) != k7_relat_1(sK3,sK0)
% 31.80/4.50      | sK3 = k2_partfun1(sK0,sK1,sK3,sK0)
% 31.80/4.50      | sK3 != k7_relat_1(sK3,sK0) ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_3352]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_344,plain,
% 31.80/4.50      ( X0 != X1 | X2 != X3 | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
% 31.80/4.50      theory(equality) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_2628,plain,
% 31.80/4.50      ( k2_zfmisc_1(sK2,sK1) = k2_zfmisc_1(X0,X1) | sK2 != X0 | sK1 != X1 ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_344]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_6635,plain,
% 31.80/4.50      ( k2_zfmisc_1(sK2,sK1) = k2_zfmisc_1(X0,sK1) | sK2 != X0 | sK1 != sK1 ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_2628]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_12067,plain,
% 31.80/4.50      ( k2_zfmisc_1(sK2,sK1) = k2_zfmisc_1(sK0,sK1) | sK2 != sK0 | sK1 != sK1 ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_6635]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_21936,plain,
% 31.80/4.50      ( sK2 != X0 | sK2 = sK0 | sK0 != X0 ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_1894]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_21938,plain,
% 31.80/4.50      ( sK2 = sK0 | sK2 != k1_xboole_0 | sK0 != k1_xboole_0 ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_21936]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_2924,plain,
% 31.80/4.50      ( X0 != X1 | sK0 != X1 | sK0 = X0 ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_342]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_31531,plain,
% 31.80/4.50      ( X0 != sK0 | sK0 = X0 | sK0 != sK0 ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_2924]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_31533,plain,
% 31.80/4.50      ( sK0 != sK0 | sK0 = k1_xboole_0 | k1_xboole_0 != sK0 ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_31531]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_345,plain,
% 31.80/4.50      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 31.80/4.50      theory(equality) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_1791,plain,
% 31.80/4.50      ( X0 != k2_zfmisc_1(sK0,sK1)
% 31.80/4.50      | k1_zfmisc_1(X0) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_345]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_2687,plain,
% 31.80/4.50      ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK1)
% 31.80/4.50      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_1791]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_12120,plain,
% 31.80/4.50      ( k2_zfmisc_1(X0,sK1) != k2_zfmisc_1(sK0,sK1)
% 31.80/4.50      | k1_zfmisc_1(k2_zfmisc_1(X0,sK1)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_2687]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_34369,plain,
% 31.80/4.50      ( k2_zfmisc_1(sK2,sK1) != k2_zfmisc_1(sK0,sK1)
% 31.80/4.50      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_12120]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_350,plain,
% 31.80/4.50      ( X0 != X1
% 31.80/4.50      | X2 != X3
% 31.80/4.50      | X4 != X5
% 31.80/4.50      | X6 != X7
% 31.80/4.50      | k2_partfun1(X0,X2,X4,X6) = k2_partfun1(X1,X3,X5,X7) ),
% 31.80/4.50      theory(equality) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_1906,plain,
% 31.80/4.50      ( X0 != X1
% 31.80/4.50      | X2 != sK3
% 31.80/4.50      | X3 != sK1
% 31.80/4.50      | X4 != sK0
% 31.80/4.50      | k2_partfun1(X4,X3,X2,X0) = k2_partfun1(sK0,sK1,sK3,X1) ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_350]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_3446,plain,
% 31.80/4.50      ( X0 != X1
% 31.80/4.50      | X2 != sK3
% 31.80/4.50      | X3 != sK0
% 31.80/4.50      | k2_partfun1(X3,sK1,X2,X0) = k2_partfun1(sK0,sK1,sK3,X1)
% 31.80/4.50      | sK1 != sK1 ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_1906]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_14866,plain,
% 31.80/4.50      ( X0 != X1
% 31.80/4.50      | X2 != sK0
% 31.80/4.50      | k2_partfun1(X2,sK1,sK3,X0) = k2_partfun1(sK0,sK1,sK3,X1)
% 31.80/4.50      | sK3 != sK3
% 31.80/4.50      | sK1 != sK1 ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_3446]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_20073,plain,
% 31.80/4.50      ( X0 != X1
% 31.80/4.50      | k2_partfun1(sK0,sK1,sK3,X0) = k2_partfun1(sK0,sK1,sK3,X1)
% 31.80/4.50      | sK3 != sK3
% 31.80/4.50      | sK1 != sK1
% 31.80/4.50      | sK0 != sK0 ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_14866]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_56632,plain,
% 31.80/4.50      ( X0 != sK0
% 31.80/4.50      | k2_partfun1(sK0,sK1,sK3,X0) = k2_partfun1(sK0,sK1,sK3,sK0)
% 31.80/4.50      | sK3 != sK3
% 31.80/4.50      | sK1 != sK1
% 31.80/4.50      | sK0 != sK0 ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_20073]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_56635,plain,
% 31.80/4.50      ( k2_partfun1(sK0,sK1,sK3,k1_xboole_0) = k2_partfun1(sK0,sK1,sK3,sK0)
% 31.80/4.50      | sK3 != sK3
% 31.80/4.50      | sK1 != sK1
% 31.80/4.50      | sK0 != sK0
% 31.80/4.50      | k1_xboole_0 != sK0 ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_56632]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_17504,plain,
% 31.80/4.50      ( X0 != k2_partfun1(sK0,sK1,sK3,sK0)
% 31.80/4.50      | sK3 = X0
% 31.80/4.50      | sK3 != k2_partfun1(sK0,sK1,sK3,sK0) ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_1774]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_56633,plain,
% 31.80/4.50      ( k2_partfun1(sK0,sK1,sK3,X0) != k2_partfun1(sK0,sK1,sK3,sK0)
% 31.80/4.50      | sK3 = k2_partfun1(sK0,sK1,sK3,X0)
% 31.80/4.50      | sK3 != k2_partfun1(sK0,sK1,sK3,sK0) ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_17504]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_56636,plain,
% 31.80/4.50      ( k2_partfun1(sK0,sK1,sK3,k1_xboole_0) != k2_partfun1(sK0,sK1,sK3,sK0)
% 31.80/4.50      | sK3 != k2_partfun1(sK0,sK1,sK3,sK0)
% 31.80/4.50      | sK3 = k2_partfun1(sK0,sK1,sK3,k1_xboole_0) ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_56633]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_56637,plain,
% 31.80/4.50      ( k2_partfun1(sK0,sK1,sK3,sK2) = k2_partfun1(sK0,sK1,sK3,X0)
% 31.80/4.50      | sK2 != X0
% 31.80/4.50      | sK3 != sK3
% 31.80/4.50      | sK1 != sK1
% 31.80/4.50      | sK0 != sK0 ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_20073]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_56641,plain,
% 31.80/4.50      ( k2_partfun1(sK0,sK1,sK3,sK2) = k2_partfun1(sK0,sK1,sK3,k1_xboole_0)
% 31.80/4.50      | sK2 != k1_xboole_0
% 31.80/4.50      | sK3 != sK3
% 31.80/4.50      | sK1 != sK1
% 31.80/4.50      | sK0 != sK0 ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_56637]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_25,plain,
% 31.80/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.80/4.50      | ~ v1_funct_1(X0)
% 31.80/4.50      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
% 31.80/4.50      inference(cnf_transformation,[],[f72]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_1330,plain,
% 31.80/4.50      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 31.80/4.50      | v1_funct_1(k2_partfun1(X0,X1,sK3,X2))
% 31.80/4.50      | ~ v1_funct_1(sK3) ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_25]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_1498,plain,
% 31.80/4.50      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 31.80/4.50      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
% 31.80/4.50      | ~ v1_funct_1(sK3) ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_1330]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_64102,plain,
% 31.80/4.50      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 31.80/4.50      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 31.80/4.50      | ~ v1_funct_1(sK3) ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_1498]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_2055,plain,
% 31.80/4.50      ( m1_subset_1(X0,X1)
% 31.80/4.50      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
% 31.80/4.50      | X0 != X2
% 31.80/4.50      | X1 != k1_zfmisc_1(X3) ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_346]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_3623,plain,
% 31.80/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 31.80/4.50      | m1_subset_1(X2,k1_zfmisc_1(X3))
% 31.80/4.50      | X2 != X0
% 31.80/4.50      | k1_zfmisc_1(X3) != k1_zfmisc_1(X1) ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_2055]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_14388,plain,
% 31.80/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 31.80/4.50      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 31.80/4.50      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 31.80/4.50      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) != k1_zfmisc_1(X1) ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_3623]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_34370,plain,
% 31.80/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 31.80/4.50      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 31.80/4.50      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 31.80/4.50      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_14388]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_65454,plain,
% 31.80/4.50      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 31.80/4.50      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 31.80/4.50      | k2_partfun1(sK0,sK1,sK3,sK2) != sK3
% 31.80/4.50      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_34370]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_2829,plain,
% 31.80/4.50      ( v1_funct_2(X0,X1,X2)
% 31.80/4.50      | ~ v1_funct_2(sK3,X3,sK1)
% 31.80/4.50      | X1 != X3
% 31.80/4.50      | X0 != sK3
% 31.80/4.50      | X2 != sK1 ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_349]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_65553,plain,
% 31.80/4.50      ( v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
% 31.80/4.50      | ~ v1_funct_2(sK3,X0,sK1)
% 31.80/4.50      | k2_partfun1(sK0,sK1,sK3,sK2) != sK3
% 31.80/4.50      | sK2 != X0
% 31.80/4.50      | sK1 != sK1 ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_2829]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_65558,plain,
% 31.80/4.50      ( v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
% 31.80/4.50      | ~ v1_funct_2(sK3,k1_xboole_0,sK1)
% 31.80/4.50      | k2_partfun1(sK0,sK1,sK3,sK2) != sK3
% 31.80/4.50      | sK2 != k1_xboole_0
% 31.80/4.50      | sK1 != sK1 ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_65553]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_1470,plain,
% 31.80/4.50      ( X0 != X1 | X0 = sK3 | sK3 != X1 ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_342]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_65452,plain,
% 31.80/4.50      ( k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 31.80/4.50      | k2_partfun1(sK0,sK1,sK3,sK2) = sK3
% 31.80/4.50      | sK3 != X0 ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_1470]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_77186,plain,
% 31.80/4.50      ( k2_partfun1(sK0,sK1,sK3,sK2) != k2_partfun1(sK0,sK1,sK3,X0)
% 31.80/4.50      | k2_partfun1(sK0,sK1,sK3,sK2) = sK3
% 31.80/4.50      | sK3 != k2_partfun1(sK0,sK1,sK3,X0) ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_65452]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_77187,plain,
% 31.80/4.50      ( k2_partfun1(sK0,sK1,sK3,sK2) != k2_partfun1(sK0,sK1,sK3,k1_xboole_0)
% 31.80/4.50      | k2_partfun1(sK0,sK1,sK3,sK2) = sK3
% 31.80/4.50      | sK3 != k2_partfun1(sK0,sK1,sK3,k1_xboole_0) ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_77186]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_90475,negated_conjecture,
% 31.80/4.50      ( k1_xboole_0 != sK1 ),
% 31.80/4.50      inference(global_propositional_subsumption,
% 31.80/4.50                [status(thm)],
% 31.80/4.50                [c_28,c_32,c_31,c_30,c_29,c_27,c_1279,c_1302,c_1480,c_1478,
% 31.80/4.50                 c_1492,c_1682,c_2188,c_2186,c_2527,c_3057,c_4266,c_4331,
% 31.80/4.50                 c_6740,c_7599,c_12067,c_21938,c_31533,c_34369,c_56635,
% 31.80/4.50                 c_56636,c_56641,c_64102,c_65454,c_65558,c_77187]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_96204,plain,
% 31.80/4.50      ( k1_relset_1(sK2,X0,k7_relat_1(k7_relat_1(sK3,X1),sK2)) = k1_relat_1(k7_relat_1(k7_relat_1(sK3,X1),sK2))
% 31.80/4.50      | r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK3,X1),sK2)),X0) != iProver_top
% 31.80/4.50      | v1_relat_1(k7_relat_1(k7_relat_1(sK3,X1),sK2)) != iProver_top ),
% 31.80/4.50      inference(global_propositional_subsumption,
% 31.80/4.50                [status(thm)],
% 31.80/4.50                [c_84158,c_32,c_31,c_30,c_29,c_28,c_27,c_105,c_106,c_1279,
% 31.80/4.50                 c_1302,c_1306,c_1480,c_1478,c_1492,c_1682,c_2188,c_2186,
% 31.80/4.50                 c_2527,c_3057,c_4266,c_4331,c_6740,c_7599,c_12067,c_21938,
% 31.80/4.50                 c_31533,c_34369,c_56635,c_56636,c_56641,c_64102,c_65454,
% 31.80/4.50                 c_65558,c_77187]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_8460,plain,
% 31.80/4.50      ( k2_partfun1(sK0,sK1,k7_relat_1(sK3,X0),X1) = k7_relat_1(k7_relat_1(sK3,X0),X1)
% 31.80/4.50      | v1_funct_1(k7_relat_1(sK3,X0)) != iProver_top ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_8451,c_985]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_1499,plain,
% 31.80/4.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 31.80/4.50      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
% 31.80/4.50      | v1_funct_1(sK3) != iProver_top ),
% 31.80/4.50      inference(predicate_to_equality,[status(thm)],[c_1498]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_351,plain,
% 31.80/4.50      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 31.80/4.50      theory(equality) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_1576,plain,
% 31.80/4.50      ( v1_funct_1(X0)
% 31.80/4.50      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,X1))
% 31.80/4.50      | X0 != k2_partfun1(sK0,sK1,sK3,X1) ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_351]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_5141,plain,
% 31.80/4.50      ( ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
% 31.80/4.50      | v1_funct_1(k7_relat_1(sK3,X0))
% 31.80/4.50      | k7_relat_1(sK3,X0) != k2_partfun1(sK0,sK1,sK3,X0) ),
% 31.80/4.50      inference(instantiation,[status(thm)],[c_1576]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_5142,plain,
% 31.80/4.50      ( k7_relat_1(sK3,X0) != k2_partfun1(sK0,sK1,sK3,X0)
% 31.80/4.50      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) != iProver_top
% 31.80/4.50      | v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 31.80/4.50      inference(predicate_to_equality,[status(thm)],[c_5141]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_10026,plain,
% 31.80/4.50      ( k2_partfun1(sK0,sK1,k7_relat_1(sK3,X0),X1) = k7_relat_1(k7_relat_1(sK3,X0),X1) ),
% 31.80/4.50      inference(global_propositional_subsumption,
% 31.80/4.50                [status(thm)],
% 31.80/4.50                [c_8460,c_32,c_33,c_30,c_35,c_1499,c_1503,c_3818,c_3819,c_5142]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_10036,plain,
% 31.80/4.50      ( m1_subset_1(k7_relat_1(k7_relat_1(sK3,X0),X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 31.80/4.50      | m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 31.80/4.50      | v1_funct_1(k7_relat_1(sK3,X0)) != iProver_top ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_10026,c_987]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_11160,plain,
% 31.80/4.50      ( m1_subset_1(k7_relat_1(k7_relat_1(sK3,X0),X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 31.80/4.50      inference(global_propositional_subsumption,
% 31.80/4.50                [status(thm)],
% 31.80/4.50                [c_10036,c_32,c_33,c_30,c_35,c_1499,c_1503,c_1569,c_1919,
% 31.80/4.50                 c_3818,c_3819,c_5142,c_5146]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_11174,plain,
% 31.80/4.50      ( v1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),X1)) = iProver_top ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_11160,c_998]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_96213,plain,
% 31.80/4.50      ( k1_relset_1(sK2,X0,k7_relat_1(k7_relat_1(sK3,X1),sK2)) = k1_relat_1(k7_relat_1(k7_relat_1(sK3,X1),sK2))
% 31.80/4.50      | r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(sK3,X1),sK2)),X0) != iProver_top ),
% 31.80/4.50      inference(forward_subsumption_resolution,[status(thm)],[c_96204,c_11174]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_96220,plain,
% 31.80/4.50      ( k1_relset_1(sK2,X0,k7_relat_1(k7_relat_1(sK3,sK0),sK2)) = k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK0),sK2))
% 31.80/4.50      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_4152,c_96213]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_5744,plain,
% 31.80/4.50      ( sK1 = k1_xboole_0
% 31.80/4.50      | r1_tarski(sK2,sK2) = iProver_top
% 31.80/4.50      | v1_relat_1(sK3) != iProver_top ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_5384,c_1001]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_5765,plain,
% 31.80/4.50      ( r1_tarski(sK2,sK2) = iProver_top | sK1 = k1_xboole_0 ),
% 31.80/4.50      inference(global_propositional_subsumption,
% 31.80/4.50                [status(thm)],
% 31.80/4.50                [c_5744,c_35,c_1280]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_5766,plain,
% 31.80/4.50      ( sK1 = k1_xboole_0 | r1_tarski(sK2,sK2) = iProver_top ),
% 31.80/4.50      inference(renaming,[status(thm)],[c_5765]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_6461,plain,
% 31.80/4.50      ( v4_relat_1(X0,X1) = iProver_top
% 31.80/4.50      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 31.80/4.50      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 31.80/4.50      | v1_relat_1(X0) != iProver_top ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_994,c_996]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_28403,plain,
% 31.80/4.50      ( sK1 = k1_xboole_0
% 31.80/4.50      | v4_relat_1(k7_relat_1(sK3,sK2),X0) = iProver_top
% 31.80/4.50      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1) != iProver_top
% 31.80/4.50      | r1_tarski(sK2,X0) != iProver_top
% 31.80/4.50      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_5384,c_6461]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_29339,plain,
% 31.80/4.50      ( sK1 = k1_xboole_0
% 31.80/4.50      | v4_relat_1(k7_relat_1(sK3,sK2),X0) = iProver_top
% 31.80/4.50      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1) != iProver_top
% 31.80/4.50      | r1_tarski(sK2,X0) != iProver_top ),
% 31.80/4.50      inference(forward_subsumption_resolution,[status(thm)],[c_28403,c_8464]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_29343,plain,
% 31.80/4.50      ( sK1 = k1_xboole_0
% 31.80/4.50      | v4_relat_1(k7_relat_1(sK3,sK2),X0) = iProver_top
% 31.80/4.50      | v5_relat_1(k7_relat_1(sK3,sK2),X1) != iProver_top
% 31.80/4.50      | r1_tarski(sK2,X0) != iProver_top
% 31.80/4.50      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_1003,c_29339]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_31393,plain,
% 31.80/4.50      ( sK1 = k1_xboole_0
% 31.80/4.50      | v4_relat_1(k7_relat_1(sK3,sK2),X0) = iProver_top
% 31.80/4.50      | v5_relat_1(k7_relat_1(sK3,sK2),X1) != iProver_top
% 31.80/4.50      | r1_tarski(sK2,X0) != iProver_top ),
% 31.80/4.50      inference(forward_subsumption_resolution,[status(thm)],[c_29343,c_8464]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_31397,plain,
% 31.80/4.50      ( sK1 = k1_xboole_0
% 31.80/4.50      | v4_relat_1(k7_relat_1(sK3,sK2),X0) = iProver_top
% 31.80/4.50      | r1_tarski(sK2,X0) != iProver_top ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_8466,c_31393]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_31405,plain,
% 31.80/4.50      ( k7_relat_1(k7_relat_1(sK3,sK2),X0) = k7_relat_1(sK3,sK2)
% 31.80/4.50      | sK1 = k1_xboole_0
% 31.80/4.50      | r1_tarski(sK2,X0) != iProver_top
% 31.80/4.50      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_31397,c_1002]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_72820,plain,
% 31.80/4.50      ( k7_relat_1(k7_relat_1(sK3,sK2),X0) = k7_relat_1(sK3,sK2)
% 31.80/4.50      | sK1 = k1_xboole_0
% 31.80/4.50      | r1_tarski(sK2,X0) != iProver_top ),
% 31.80/4.50      inference(forward_subsumption_resolution,[status(thm)],[c_31405,c_8464]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_72826,plain,
% 31.80/4.50      ( k7_relat_1(k7_relat_1(sK3,sK2),sK2) = k7_relat_1(sK3,sK2)
% 31.80/4.50      | sK1 = k1_xboole_0 ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_5766,c_72820]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_4155,plain,
% 31.80/4.50      ( r1_tarski(k1_relat_1(sK3),sK0) = iProver_top
% 31.80/4.50      | v1_relat_1(sK3) != iProver_top ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_4152,c_1001]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_4586,plain,
% 31.80/4.50      ( r1_tarski(k1_relat_1(sK3),sK0) = iProver_top ),
% 31.80/4.50      inference(global_propositional_subsumption,
% 31.80/4.50                [status(thm)],
% 31.80/4.50                [c_4155,c_35,c_1280]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_5386,plain,
% 31.80/4.50      ( k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3))) = k1_relat_1(sK3)
% 31.80/4.50      | sK1 = k1_xboole_0 ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_4586,c_5375]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_7099,plain,
% 31.80/4.50      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)),X0)) = X0
% 31.80/4.50      | sK1 = k1_xboole_0
% 31.80/4.50      | r1_tarski(X0,k1_relat_1(sK3)) != iProver_top
% 31.80/4.50      | v1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3))) != iProver_top ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_5386,c_999]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_31788,plain,
% 31.80/4.50      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)),X0)) = X0
% 31.80/4.50      | sK1 = k1_xboole_0
% 31.80/4.50      | r1_tarski(X0,k1_relat_1(sK3)) != iProver_top ),
% 31.80/4.50      inference(forward_subsumption_resolution,[status(thm)],[c_7099,c_8464]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_31797,plain,
% 31.80/4.50      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)),X0)) = X0
% 31.80/4.50      | sK1 = k1_xboole_0
% 31.80/4.50      | r1_tarski(X0,sK0) != iProver_top ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_4342,c_31788]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_32862,plain,
% 31.80/4.50      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)),sK2)) = sK2
% 31.80/4.50      | sK1 = k1_xboole_0 ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_983,c_31797]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_66257,plain,
% 31.80/4.50      ( sK1 = k1_xboole_0
% 31.80/4.50      | r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),k1_relat_1(k7_relat_1(sK3,sK2)))),k1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),sK2))) = iProver_top
% 31.80/4.50      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_65801,c_1001]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_69691,plain,
% 31.80/4.50      ( sK1 = k1_xboole_0
% 31.80/4.50      | r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),k1_relat_1(k7_relat_1(sK3,sK2)))),k1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),sK2))) = iProver_top ),
% 31.80/4.50      inference(forward_subsumption_resolution,[status(thm)],[c_66257,c_8464]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_69709,plain,
% 31.80/4.50      ( sK1 = k1_xboole_0
% 31.80/4.50      | r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)),k1_relat_1(k7_relat_1(sK3,sK2)))),sK2) = iProver_top ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_32862,c_69691]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_69837,plain,
% 31.80/4.50      ( sK1 = k1_xboole_0
% 31.80/4.50      | r1_tarski(k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK0),k1_relat_1(k7_relat_1(sK3,sK2)))),sK2) = iProver_top ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_4342,c_69709]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_69899,plain,
% 31.80/4.50      ( sK1 = k1_xboole_0
% 31.80/4.50      | r1_tarski(k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,sK2)))),sK2) = iProver_top ),
% 31.80/4.50      inference(light_normalisation,[status(thm)],[c_69837,c_4152]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_5,plain,
% 31.80/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 31.80/4.50      inference(cnf_transformation,[],[f52]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_1005,plain,
% 31.80/4.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 31.80/4.50      | r1_tarski(X0,X1) = iProver_top ),
% 31.80/4.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_1748,plain,
% 31.80/4.50      ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_982,c_1005]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_1834,plain,
% 31.80/4.50      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 31.80/4.50      | v1_relat_1(sK3) = iProver_top ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_1748,c_979]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_1837,plain,
% 31.80/4.50      ( v1_relat_1(sK3) = iProver_top ),
% 31.80/4.50      inference(global_propositional_subsumption,
% 31.80/4.50                [status(thm)],
% 31.80/4.50                [c_1834,c_35,c_1280]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_7475,plain,
% 31.80/4.50      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),k1_relat_1(k7_relat_1(sK3,sK2)))) = k1_relat_1(k7_relat_1(sK3,sK2))
% 31.80/4.50      | sK1 = k1_xboole_0 ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_1837,c_5973]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_7618,plain,
% 31.80/4.50      ( sK1 = k1_xboole_0
% 31.80/4.50      | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),k1_relat_1(k7_relat_1(sK3,sK2))) = iProver_top
% 31.80/4.50      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_7475,c_1001]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_12033,plain,
% 31.80/4.50      ( sK1 = k1_xboole_0
% 31.80/4.50      | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),k1_relat_1(k7_relat_1(sK3,sK2))) = iProver_top ),
% 31.80/4.50      inference(forward_subsumption_resolution,[status(thm)],[c_7618,c_8464]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_7617,plain,
% 31.80/4.50      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
% 31.80/4.50      | sK1 = k1_xboole_0 ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_5384,c_7475]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_8742,plain,
% 31.80/4.50      ( k1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2),X0)) = X0
% 31.80/4.50      | sK1 = k1_xboole_0
% 31.80/4.50      | r1_tarski(X0,k1_relat_1(k7_relat_1(sK3,sK2))) != iProver_top
% 31.80/4.50      | v1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2)) != iProver_top ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_7617,c_999]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_12040,plain,
% 31.80/4.50      ( k1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2),k1_relat_1(k7_relat_1(sK3,sK2)))) = k1_relat_1(k7_relat_1(sK3,sK2))
% 31.80/4.50      | sK1 = k1_xboole_0
% 31.80/4.50      | v1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2)) != iProver_top ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_12033,c_8742]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_13922,plain,
% 31.80/4.50      ( k1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2),k1_relat_1(k7_relat_1(sK3,sK2)))) = k1_relat_1(k7_relat_1(sK3,sK2))
% 31.80/4.50      | sK1 = k1_xboole_0 ),
% 31.80/4.50      inference(forward_subsumption_resolution,[status(thm)],[c_12040,c_11174]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_13923,plain,
% 31.80/4.50      ( k1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2),sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
% 31.80/4.50      | sK1 = k1_xboole_0 ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_5384,c_13922]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_14716,plain,
% 31.80/4.50      ( k1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2),sK2),X0)) = X0
% 31.80/4.50      | sK1 = k1_xboole_0
% 31.80/4.50      | r1_tarski(X0,k1_relat_1(k7_relat_1(sK3,sK2))) != iProver_top
% 31.80/4.50      | v1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2),sK2)) != iProver_top ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_13923,c_999]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_14747,plain,
% 31.80/4.50      ( k1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2),sK2),X0)) = X0
% 31.80/4.50      | sK1 = k1_xboole_0
% 31.80/4.50      | r1_tarski(X0,k1_relat_1(k7_relat_1(sK3,sK2))) != iProver_top
% 31.80/4.50      | v1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2)) != iProver_top ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_1515,c_14716]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_19131,plain,
% 31.80/4.50      ( k1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2),sK2),X0)) = X0
% 31.80/4.50      | sK1 = k1_xboole_0
% 31.80/4.50      | r1_tarski(X0,k1_relat_1(k7_relat_1(sK3,sK2))) != iProver_top ),
% 31.80/4.50      inference(forward_subsumption_resolution,[status(thm)],[c_14747,c_11174]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_19142,plain,
% 31.80/4.50      ( k1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2),sK2),X0)) = X0
% 31.80/4.50      | sK1 = k1_xboole_0
% 31.80/4.50      | r1_tarski(X0,sK2) != iProver_top ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_5384,c_19131]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_71070,plain,
% 31.80/4.50      ( k1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2),sK2),k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,sK2)))))) = k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,sK2))))
% 31.80/4.50      | sK1 = k1_xboole_0 ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_69899,c_19142]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_75908,plain,
% 31.80/4.50      ( k1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2),sK2),k1_relat_1(k7_relat_1(sK3,sK2)))) = k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,sK2))))
% 31.80/4.50      | sK1 = k1_xboole_0 ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_5384,c_71070]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_76035,plain,
% 31.80/4.50      ( k1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2),k1_relat_1(k7_relat_1(sK3,sK2)))) = k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,sK2))))
% 31.80/4.50      | sK1 = k1_xboole_0 ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_72826,c_75908]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_92032,plain,
% 31.80/4.50      ( k1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2),k1_relat_1(k7_relat_1(sK3,sK2)))) = k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,sK2)))) ),
% 31.80/4.50      inference(global_propositional_subsumption,
% 31.80/4.50                [status(thm)],
% 31.80/4.50                [c_76035,c_32,c_31,c_30,c_29,c_28,c_27,c_105,c_106,c_1279,
% 31.80/4.50                 c_1302,c_1306,c_1480,c_1478,c_1492,c_1682,c_2188,c_2186,
% 31.80/4.50                 c_2527,c_3057,c_4266,c_4331,c_6740,c_7599,c_12067,c_21938,
% 31.80/4.50                 c_31533,c_34369,c_56635,c_56636,c_56641,c_64102,c_65454,
% 31.80/4.50                 c_65558,c_77187]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_33078,plain,
% 31.80/4.50      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)),sK2)) = k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2))
% 31.80/4.50      | sK1 = k1_xboole_0 ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_32862,c_8847]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_19202,plain,
% 31.80/4.50      ( k1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2),sK2),k1_relat_1(k7_relat_1(X0,sK2)))) = k1_relat_1(k7_relat_1(X0,sK2))
% 31.80/4.50      | sK1 = k1_xboole_0
% 31.80/4.50      | v1_relat_1(X0) != iProver_top ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_1001,c_19142]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_19550,plain,
% 31.80/4.50      ( k1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2),sK2),k1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),sK2)))) = k1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),sK2))
% 31.80/4.50      | sK1 = k1_xboole_0 ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_8464,c_19202]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_33150,plain,
% 31.80/4.50      ( k1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2),sK2),k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2)))) = k1_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)),sK2))
% 31.80/4.50      | sK1 = k1_xboole_0 ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_33078,c_19550]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_35756,plain,
% 31.80/4.50      ( k1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2),sK2),k1_relat_1(k7_relat_1(sK3,sK2)))) = k1_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)),sK2))
% 31.80/4.50      | sK1 = k1_xboole_0 ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_7617,c_33150]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_76047,plain,
% 31.80/4.50      ( k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,sK2)))) = k1_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)),sK2))
% 31.80/4.50      | sK1 = k1_xboole_0 ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_75908,c_35756]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_77415,plain,
% 31.80/4.50      ( k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,sK2)))) = k1_relat_1(k7_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)),sK2)) ),
% 31.80/4.50      inference(global_propositional_subsumption,
% 31.80/4.50                [status(thm)],
% 31.80/4.50                [c_76047,c_32,c_31,c_30,c_29,c_28,c_27,c_105,c_106,c_1279,
% 31.80/4.50                 c_1302,c_1306,c_1480,c_1478,c_1492,c_1682,c_2188,c_2186,
% 31.80/4.50                 c_2527,c_3057,c_4266,c_4331,c_6740,c_7599,c_12067,c_21938,
% 31.80/4.50                 c_31533,c_34369,c_56635,c_56636,c_56641,c_64102,c_65454,
% 31.80/4.50                 c_65558,c_77187]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_77501,plain,
% 31.80/4.50      ( k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,sK2)))) = sK2
% 31.80/4.50      | sK1 = k1_xboole_0 ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_77415,c_32862]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_77623,plain,
% 31.80/4.50      ( k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,sK2)))) = sK2 ),
% 31.80/4.50      inference(global_propositional_subsumption,
% 31.80/4.50                [status(thm)],
% 31.80/4.50                [c_77501,c_32,c_31,c_30,c_29,c_28,c_27,c_105,c_106,c_1279,
% 31.80/4.50                 c_1302,c_1306,c_1480,c_1478,c_1492,c_1682,c_2188,c_2186,
% 31.80/4.50                 c_2527,c_3057,c_4266,c_4331,c_6740,c_7599,c_12067,c_21938,
% 31.80/4.50                 c_31533,c_34369,c_56635,c_56636,c_56641,c_64102,c_65454,
% 31.80/4.50                 c_65558,c_77187]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_54811,plain,
% 31.80/4.50      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,X0),k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,X0)))))) = k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,X0)))) ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_1837,c_47397]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_77669,plain,
% 31.80/4.50      ( k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,sK2)))) = k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2)) ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_77623,c_54811]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_77671,plain,
% 31.80/4.50      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2)) = sK2 ),
% 31.80/4.50      inference(light_normalisation,[status(thm)],[c_77669,c_77623]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_78255,plain,
% 31.80/4.50      ( k1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2),X0)) = X0
% 31.80/4.50      | r1_tarski(X0,sK2) != iProver_top
% 31.80/4.50      | v1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2)) != iProver_top ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_77671,c_999]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_5976,plain,
% 31.80/4.50      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2)) = sK2
% 31.80/4.50      | sK1 = k1_xboole_0 ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_5766,c_5964]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_6147,plain,
% 31.80/4.50      ( k1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2),X0)) = X0
% 31.80/4.50      | sK1 = k1_xboole_0
% 31.80/4.50      | r1_tarski(X0,sK2) != iProver_top
% 31.80/4.50      | v1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2)) != iProver_top ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_5976,c_999]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_14956,plain,
% 31.80/4.50      ( k1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2),X0)) = X0
% 31.80/4.50      | sK1 = k1_xboole_0
% 31.80/4.50      | r1_tarski(X0,sK2) != iProver_top ),
% 31.80/4.50      inference(forward_subsumption_resolution,[status(thm)],[c_6147,c_11174]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_79738,plain,
% 31.80/4.50      ( r1_tarski(X0,sK2) != iProver_top
% 31.80/4.50      | k1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2),X0)) = X0 ),
% 31.80/4.50      inference(global_propositional_subsumption,
% 31.80/4.50                [status(thm)],
% 31.80/4.50                [c_78255,c_32,c_31,c_30,c_29,c_28,c_27,c_105,c_106,c_1279,
% 31.80/4.50                 c_1302,c_1306,c_1480,c_1478,c_1492,c_1682,c_2188,c_2186,
% 31.80/4.50                 c_2527,c_3057,c_4266,c_4331,c_6740,c_7599,c_12067,c_14956,
% 31.80/4.50                 c_21938,c_31533,c_34369,c_56635,c_56636,c_56641,c_64102,
% 31.80/4.50                 c_65454,c_65558,c_77187]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_79739,plain,
% 31.80/4.50      ( k1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2),X0)) = X0
% 31.80/4.50      | r1_tarski(X0,sK2) != iProver_top ),
% 31.80/4.50      inference(renaming,[status(thm)],[c_79738]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_79747,plain,
% 31.80/4.50      ( k1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2),k1_relat_1(k7_relat_1(X0,sK2)))) = k1_relat_1(k7_relat_1(X0,sK2))
% 31.80/4.50      | v1_relat_1(X0) != iProver_top ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_1001,c_79739]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_81440,plain,
% 31.80/4.50      ( k1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2),k1_relat_1(k7_relat_1(sK3,sK2)))) = k1_relat_1(k7_relat_1(sK3,sK2)) ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_1837,c_79747]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_92034,plain,
% 31.80/4.50      ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2 ),
% 31.80/4.50      inference(light_normalisation,[status(thm)],[c_92032,c_77623,c_81440]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_96223,plain,
% 31.80/4.50      ( k1_relset_1(sK2,X0,k7_relat_1(sK3,sK2)) = sK2
% 31.80/4.50      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top ),
% 31.80/4.50      inference(light_normalisation,[status(thm)],[c_96220,c_4152,c_92034]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_96469,plain,
% 31.80/4.50      ( k1_relset_1(sK2,X0,k7_relat_1(sK3,sK2)) = sK2
% 31.80/4.50      | v5_relat_1(k7_relat_1(sK3,sK2),X0) != iProver_top
% 31.80/4.50      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_1003,c_96223]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_96802,plain,
% 31.80/4.50      ( k1_relset_1(sK2,X0,k7_relat_1(sK3,sK2)) = sK2
% 31.80/4.50      | v5_relat_1(k7_relat_1(sK3,sK2),X0) != iProver_top ),
% 31.80/4.50      inference(forward_subsumption_resolution,[status(thm)],[c_96469,c_8464]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_96806,plain,
% 31.80/4.50      ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) = sK2 ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_8466,c_96802]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_21,plain,
% 31.80/4.50      ( v1_funct_2(X0,X1,X2)
% 31.80/4.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.80/4.50      | k1_relset_1(X1,X2,X0) != X1
% 31.80/4.50      | k1_xboole_0 = X2 ),
% 31.80/4.50      inference(cnf_transformation,[],[f68]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_990,plain,
% 31.80/4.50      ( k1_relset_1(X0,X1,X2) != X0
% 31.80/4.50      | k1_xboole_0 = X1
% 31.80/4.50      | v1_funct_2(X2,X0,X1) = iProver_top
% 31.80/4.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 31.80/4.50      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_103282,plain,
% 31.80/4.50      ( sK1 = k1_xboole_0
% 31.80/4.50      | v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) = iProver_top
% 31.80/4.50      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_96806,c_990]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_984,plain,
% 31.80/4.50      ( v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) != iProver_top
% 31.80/4.50      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 31.80/4.50      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 31.80/4.50      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_8220,plain,
% 31.80/4.50      ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) != iProver_top
% 31.80/4.50      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 31.80/4.50      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 31.80/4.50      inference(demodulation,[status(thm)],[c_8214,c_984]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_986,plain,
% 31.80/4.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 31.80/4.50      | v1_funct_1(X0) != iProver_top
% 31.80/4.50      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
% 31.80/4.50      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_2068,plain,
% 31.80/4.50      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
% 31.80/4.50      | v1_funct_1(sK3) != iProver_top ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_982,c_986]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_2574,plain,
% 31.80/4.50      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
% 31.80/4.50      inference(global_propositional_subsumption,
% 31.80/4.50                [status(thm)],
% 31.80/4.50                [c_2068,c_33,c_35,c_1499]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_8221,plain,
% 31.80/4.50      ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 31.80/4.50      inference(demodulation,[status(thm)],[c_8214,c_2574]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_8227,plain,
% 31.80/4.50      ( v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) != iProver_top
% 31.80/4.50      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 31.80/4.50      inference(forward_subsumption_resolution,[status(thm)],[c_8220,c_8221]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_105198,plain,
% 31.80/4.50      ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 31.80/4.50      inference(global_propositional_subsumption,
% 31.80/4.50                [status(thm)],
% 31.80/4.50                [c_103282,c_32,c_31,c_30,c_29,c_28,c_27,c_105,c_106,c_1279,
% 31.80/4.50                 c_1302,c_1306,c_1480,c_1478,c_1492,c_1682,c_2188,c_2186,
% 31.80/4.50                 c_2527,c_3057,c_4266,c_4331,c_6740,c_7599,c_8227,c_12067,
% 31.80/4.50                 c_21938,c_31533,c_34369,c_56635,c_56636,c_56641,c_64102,
% 31.80/4.50                 c_65454,c_65558,c_77187]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_105204,plain,
% 31.80/4.50      ( r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) != iProver_top
% 31.80/4.50      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
% 31.80/4.50      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_994,c_105198]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_105208,plain,
% 31.80/4.50      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
% 31.80/4.50      | r1_tarski(sK2,sK2) != iProver_top
% 31.80/4.50      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 31.80/4.50      inference(light_normalisation,[status(thm)],[c_105204,c_92034]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_55132,plain,
% 31.80/4.50      ( r1_tarski(k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,X0)))),k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,X0))))) = iProver_top
% 31.80/4.50      | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_54811,c_1001]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_55496,plain,
% 31.80/4.50      ( r1_tarski(k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,X0)))),k1_relat_1(k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,X0))))) = iProver_top ),
% 31.80/4.50      inference(global_propositional_subsumption,
% 31.80/4.50                [status(thm)],
% 31.80/4.50                [c_55132,c_35,c_1280,c_1405,c_1715]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_77667,plain,
% 31.80/4.50      ( r1_tarski(sK2,sK2) = iProver_top ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_77623,c_55496]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_116254,plain,
% 31.80/4.50      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
% 31.80/4.50      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 31.80/4.50      inference(global_propositional_subsumption,
% 31.80/4.50                [status(thm)],
% 31.80/4.50                [c_105208,c_32,c_31,c_30,c_35,c_29,c_28,c_27,c_105,c_106,
% 31.80/4.50                 c_1279,c_1280,c_1302,c_1306,c_1480,c_1478,c_1492,c_1682,
% 31.80/4.50                 c_2188,c_2186,c_2527,c_3057,c_4266,c_4331,c_5744,c_6740,
% 31.80/4.50                 c_7599,c_12067,c_21938,c_31533,c_34369,c_56635,c_56636,
% 31.80/4.50                 c_56641,c_64102,c_65454,c_65558,c_77187]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_116260,plain,
% 31.80/4.50      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top ),
% 31.80/4.50      inference(forward_subsumption_resolution,[status(thm)],[c_116254,c_8464]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_116262,plain,
% 31.80/4.50      ( v5_relat_1(k7_relat_1(sK3,sK2),sK1) != iProver_top
% 31.80/4.50      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 31.80/4.50      inference(superposition,[status(thm)],[c_1003,c_116260]) ).
% 31.80/4.50  
% 31.80/4.50  cnf(c_116590,plain,
% 31.80/4.50      ( $false ),
% 31.80/4.50      inference(forward_subsumption_resolution,
% 31.80/4.50                [status(thm)],
% 31.80/4.50                [c_116262,c_8464,c_8466]) ).
% 31.80/4.50  
% 31.80/4.50  
% 31.80/4.50  % SZS output end CNFRefutation for theBenchmark.p
% 31.80/4.50  
% 31.80/4.50  ------                               Statistics
% 31.80/4.50  
% 31.80/4.50  ------ Selected
% 31.80/4.50  
% 31.80/4.50  total_time:                             3.902
% 31.80/4.50  
%------------------------------------------------------------------------------
