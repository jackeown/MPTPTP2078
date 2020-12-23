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
% DateTime   : Thu Dec  3 12:03:56 EST 2020

% Result     : Theorem 35.39s
% Output     : CNFRefutation 35.39s
% Verified   : 
% Statistics : Number of formulae       :  256 (2720 expanded)
%              Number of clauses        :  177 (1016 expanded)
%              Number of leaves         :   19 ( 482 expanded)
%              Depth                    :   32
%              Number of atoms          :  802 (13834 expanded)
%              Number of equality atoms :  482 (4214 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
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

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f43,plain,
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

fof(f44,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f38,f43])).

fof(f73,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f44])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f71,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f74,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f12,axiom,(
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
    inference(ennf_transformation,[],[f12])).

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

fof(f42,plain,(
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
    inference(cnf_transformation,[],[f42])).

fof(f72,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f39])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f78,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(X2,X1)
        & v1_relat_1(X2) )
     => ( v4_relat_1(k7_relat_1(X2,X0),X1)
        & v4_relat_1(k7_relat_1(X2,X0),X0)
        & v1_relat_1(k7_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(k7_relat_1(X2,X0),X1)
        & v4_relat_1(k7_relat_1(X2,X0),X0)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(k7_relat_1(X2,X0),X1)
        & v4_relat_1(k7_relat_1(X2,X0),X0)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(k7_relat_1(X2,X0))
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f76,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f44])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f67])).

fof(f80,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f79])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f77,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f48])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f1,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f45,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f81,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f66])).

fof(f75,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f44])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f82,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f65])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(k7_relat_1(X2,X0),X0)
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1100,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1102,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3061,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1100,c_1102])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_32,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_3109,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3061,c_32])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1103,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1610,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1100,c_1103])).

cnf(c_1779,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1610,c_32])).

cnf(c_3116,plain,
    ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3109,c_1779])).

cnf(c_28,negated_conjecture,
    ( r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1101,plain,
    ( r1_tarski(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_446,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X0
    | sK1 != X2
    | sK0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_30])).

cnf(c_447,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_446])).

cnf(c_449,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_447,c_29])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1106,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1841,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1100,c_1106])).

cnf(c_2017,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_449,c_1841])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1109,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2239,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2017,c_1109])).

cnf(c_34,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1266,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1310,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1266])).

cnf(c_1311,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1310])).

cnf(c_2423,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | sK1 = k1_xboole_0
    | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2239,c_34,c_1311])).

cnf(c_2424,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2423])).

cnf(c_2428,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1101,c_2424])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1104,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3125,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3109,c_1104])).

cnf(c_3228,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3125,c_32,c_34])).

cnf(c_5,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v5_relat_1(X0,X2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_323,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X3),X4)
    | ~ v1_relat_1(X3)
    | X0 != X3
    | X2 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_13])).

cnf(c_324,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_323])).

cnf(c_328,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_324,c_12])).

cnf(c_329,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_328])).

cnf(c_1098,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_329])).

cnf(c_3240,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3228,c_1098])).

cnf(c_2,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_16,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1105,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2252,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_1105])).

cnf(c_3636,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),k1_xboole_0) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3240,c_2252])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v4_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1107,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v4_relat_1(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1732,plain,
    ( v4_relat_1(sK3,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1100,c_1107])).

cnf(c_8,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X2)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1112,plain,
    ( v4_relat_1(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k7_relat_1(X0,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2013,plain,
    ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1732,c_1112])).

cnf(c_7726,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),k1_xboole_0) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3636,c_34,c_1311,c_2013])).

cnf(c_7727,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_7726])).

cnf(c_7732,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2428,c_7727])).

cnf(c_1889,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(k2_partfun1(X1,X2,X0,X3)),X2) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1104,c_1098])).

cnf(c_2122,plain,
    ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2013,c_34,c_1311])).

cnf(c_2479,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK2) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2428,c_1109])).

cnf(c_2677,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2122,c_2479])).

cnf(c_4497,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),k2_relat_1(k2_partfun1(X0,sK2,X1,X2)))) = k2_relat_1(k2_partfun1(X0,sK2,X1,X2))
    | sK1 = k1_xboole_0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1889,c_2677])).

cnf(c_33178,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),k2_relat_1(k2_partfun1(k1_xboole_0,sK2,X0,X1)))) = k2_relat_1(k2_partfun1(k1_xboole_0,sK2,X0,X1))
    | sK1 = k1_xboole_0
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_4497])).

cnf(c_33192,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),k2_relat_1(k2_partfun1(k1_xboole_0,sK2,k7_relat_1(sK3,sK2),X0)))) = k2_relat_1(k2_partfun1(k1_xboole_0,sK2,k7_relat_1(sK3,sK2),X0))
    | sK1 = k1_xboole_0
    | r1_tarski(sK2,k1_xboole_0) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7732,c_33178])).

cnf(c_10,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1110,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2478,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(sK2,sK2) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2428,c_1110])).

cnf(c_2485,plain,
    ( r1_tarski(sK2,sK2) = iProver_top
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2478,c_34,c_1311])).

cnf(c_2486,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(sK2,sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_2485])).

cnf(c_2253,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | r1_tarski(k1_relat_1(X2),X0) != iProver_top
    | r1_tarski(k2_relat_1(X2),X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1105,c_1106])).

cnf(c_11254,plain,
    ( k1_relset_1(X0,X1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
    | sK1 = k1_xboole_0
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2428,c_2253])).

cnf(c_11714,plain,
    ( k1_relset_1(X0,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
    | sK1 = k1_xboole_0
    | r1_tarski(sK2,X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3240,c_11254])).

cnf(c_25292,plain,
    ( k1_relset_1(X0,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
    | sK1 = k1_xboole_0
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2122,c_11714])).

cnf(c_25298,plain,
    ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2486,c_25292])).

cnf(c_20,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_26,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_430,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_relset_1(X1,X2,X0) != X1
    | sK2 != X1
    | sK1 != X2
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_26])).

cnf(c_431,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_430])).

cnf(c_1093,plain,
    ( k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | k1_xboole_0 = sK1
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_431])).

cnf(c_3115,plain,
    ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) != sK2
    | sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3109,c_1093])).

cnf(c_25335,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_25298,c_3115])).

cnf(c_25338,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_25335,c_2428])).

cnf(c_25342,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) != iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1105,c_25338])).

cnf(c_23866,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_23867,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23866])).

cnf(c_44267,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_25342,c_34,c_1311,c_23867])).

cnf(c_44271,plain,
    ( sK1 = k1_xboole_0
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3240,c_44267])).

cnf(c_37278,plain,
    ( ~ v4_relat_1(sK3,X0)
    | v1_relat_1(k7_relat_1(sK3,X1))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_43251,plain,
    ( ~ v4_relat_1(sK3,X0)
    | v1_relat_1(k7_relat_1(sK3,sK2))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_37278])).

cnf(c_50930,plain,
    ( ~ v4_relat_1(sK3,sK0)
    | v1_relat_1(k7_relat_1(sK3,sK2))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_43251])).

cnf(c_50934,plain,
    ( v4_relat_1(sK3,sK0) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50930])).

cnf(c_58014,plain,
    ( sK1 = k1_xboole_0
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_33192,c_34,c_1311,c_1732,c_44271,c_50934])).

cnf(c_58018,plain,
    ( sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3116,c_58014])).

cnf(c_17,plain,
    ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_352,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK2 != X0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_26])).

cnf(c_353,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_352])).

cnf(c_1097,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_353])).

cnf(c_1,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1118,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1097,c_1])).

cnf(c_3113,plain,
    ( k7_relat_1(sK3,sK2) != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3109,c_1118])).

cnf(c_3,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_101,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_102,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_676,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1154,plain,
    ( sK2 != X0
    | sK2 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_676])).

cnf(c_1161,plain,
    ( sK2 != sK2
    | sK2 = k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_1154])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1170,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_675,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1192,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_675])).

cnf(c_677,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1194,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_677])).

cnf(c_1249,plain,
    ( ~ r1_tarski(sK2,X0)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != sK2
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1194])).

cnf(c_1368,plain,
    ( ~ r1_tarski(sK2,sK0)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != sK2
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1249])).

cnf(c_1384,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_676])).

cnf(c_1385,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1384])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_378,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK3 != X0
    | sK1 != k1_xboole_0
    | sK0 != X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_30])).

cnf(c_379,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0 ),
    inference(unflattening,[status(thm)],[c_378])).

cnf(c_1096,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_379])).

cnf(c_1117,plain,
    ( sK3 = k1_xboole_0
    | sK1 != k1_xboole_0
    | sK0 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1096,c_1])).

cnf(c_27,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1155,plain,
    ( sK0 != X0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_676])).

cnf(c_1163,plain,
    ( sK0 != sK0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1155])).

cnf(c_1176,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_675])).

cnf(c_1394,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_676])).

cnf(c_1395,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1394])).

cnf(c_1463,plain,
    ( sK0 = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1117,c_27,c_101,c_102,c_1163,c_1176,c_1395])).

cnf(c_1464,plain,
    ( sK1 != k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_1463])).

cnf(c_3337,plain,
    ( sK1 != k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3113,c_28,c_101,c_102,c_1161,c_1170,c_1192,c_1368,c_1385,c_1464])).

cnf(c_3338,plain,
    ( sK2 = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_3337])).

cnf(c_58357,plain,
    ( sK2 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_58018,c_3338])).

cnf(c_58384,plain,
    ( sK2 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_58357])).

cnf(c_19,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_398,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | sK2 != k1_xboole_0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_26])).

cnf(c_399,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_398])).

cnf(c_1095,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_399])).

cnf(c_1119,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1095,c_2])).

cnf(c_1397,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_1398,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1397])).

cnf(c_1458,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | sK2 != k1_xboole_0
    | k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1119,c_32,c_34,c_1398])).

cnf(c_1459,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_1458])).

cnf(c_3112,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k7_relat_1(sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3109,c_1459])).

cnf(c_58358,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_58018,c_3112])).

cnf(c_58383,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_58358,c_1])).

cnf(c_58385,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_58384,c_58383])).

cnf(c_58388,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_58385])).

cnf(c_1108,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1518,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1100,c_1108])).

cnf(c_1115,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1621,plain,
    ( k1_relat_1(k7_relat_1(X0,k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1110,c_1115])).

cnf(c_1786,plain,
    ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1518,c_1621])).

cnf(c_2251,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_1105])).

cnf(c_3419,plain,
    ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_xboole_0)),k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1786,c_2251])).

cnf(c_2015,plain,
    ( v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2013])).

cnf(c_7,plain,
    ( ~ v4_relat_1(X0,X1)
    | v4_relat_1(k7_relat_1(X0,X2),X2)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1113,plain,
    ( v4_relat_1(X0,X1) != iProver_top
    | v4_relat_1(k7_relat_1(X0,X2),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2298,plain,
    ( v4_relat_1(k7_relat_1(sK3,X0),X0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1732,c_1113])).

cnf(c_2403,plain,
    ( v4_relat_1(k7_relat_1(sK3,X0),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2298,c_34,c_1311])).

cnf(c_9,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1111,plain,
    ( k7_relat_1(X0,X1) = X0
    | v4_relat_1(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2412,plain,
    ( k7_relat_1(k7_relat_1(sK3,X0),X0) = k7_relat_1(sK3,X0)
    | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2403,c_1111])).

cnf(c_2796,plain,
    ( k7_relat_1(k7_relat_1(sK3,X0),X0) = k7_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2412,c_34,c_1311,c_2013])).

cnf(c_2800,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X0) = iProver_top
    | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2796,c_1110])).

cnf(c_2805,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,k1_xboole_0)),k1_xboole_0) = iProver_top
    | v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2800])).

cnf(c_3638,plain,
    ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,k1_xboole_0)),k1_xboole_0) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3636])).

cnf(c_3996,plain,
    ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3419,c_34,c_1311,c_2015,c_2805,c_3638])).

cnf(c_1843,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_1106])).

cnf(c_4005,plain,
    ( k1_relset_1(k1_xboole_0,X0,k7_relat_1(sK3,k1_xboole_0)) = k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_3996,c_1843])).

cnf(c_4008,plain,
    ( k1_relset_1(k1_xboole_0,X0,k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4005,c_1786])).

cnf(c_58389,plain,
    ( k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_58388,c_4008])).

cnf(c_58390,plain,
    ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_58389])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_58390,c_3638,c_2805,c_2015,c_1311,c_34])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:08:09 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 35.39/4.95  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 35.39/4.95  
% 35.39/4.95  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 35.39/4.95  
% 35.39/4.95  ------  iProver source info
% 35.39/4.95  
% 35.39/4.95  git: date: 2020-06-30 10:37:57 +0100
% 35.39/4.95  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 35.39/4.95  git: non_committed_changes: false
% 35.39/4.95  git: last_make_outside_of_git: false
% 35.39/4.95  
% 35.39/4.95  ------ 
% 35.39/4.95  
% 35.39/4.95  ------ Input Options
% 35.39/4.95  
% 35.39/4.95  --out_options                           all
% 35.39/4.95  --tptp_safe_out                         true
% 35.39/4.95  --problem_path                          ""
% 35.39/4.95  --include_path                          ""
% 35.39/4.95  --clausifier                            res/vclausify_rel
% 35.39/4.95  --clausifier_options                    ""
% 35.39/4.95  --stdin                                 false
% 35.39/4.95  --stats_out                             all
% 35.39/4.95  
% 35.39/4.95  ------ General Options
% 35.39/4.95  
% 35.39/4.95  --fof                                   false
% 35.39/4.95  --time_out_real                         305.
% 35.39/4.95  --time_out_virtual                      -1.
% 35.39/4.95  --symbol_type_check                     false
% 35.39/4.95  --clausify_out                          false
% 35.39/4.95  --sig_cnt_out                           false
% 35.39/4.95  --trig_cnt_out                          false
% 35.39/4.95  --trig_cnt_out_tolerance                1.
% 35.39/4.95  --trig_cnt_out_sk_spl                   false
% 35.39/4.95  --abstr_cl_out                          false
% 35.39/4.95  
% 35.39/4.95  ------ Global Options
% 35.39/4.95  
% 35.39/4.95  --schedule                              default
% 35.39/4.95  --add_important_lit                     false
% 35.39/4.95  --prop_solver_per_cl                    1000
% 35.39/4.95  --min_unsat_core                        false
% 35.39/4.95  --soft_assumptions                      false
% 35.39/4.95  --soft_lemma_size                       3
% 35.39/4.95  --prop_impl_unit_size                   0
% 35.39/4.95  --prop_impl_unit                        []
% 35.39/4.95  --share_sel_clauses                     true
% 35.39/4.95  --reset_solvers                         false
% 35.39/4.95  --bc_imp_inh                            [conj_cone]
% 35.39/4.95  --conj_cone_tolerance                   3.
% 35.39/4.95  --extra_neg_conj                        none
% 35.39/4.95  --large_theory_mode                     true
% 35.39/4.95  --prolific_symb_bound                   200
% 35.39/4.95  --lt_threshold                          2000
% 35.39/4.95  --clause_weak_htbl                      true
% 35.39/4.95  --gc_record_bc_elim                     false
% 35.39/4.95  
% 35.39/4.95  ------ Preprocessing Options
% 35.39/4.95  
% 35.39/4.95  --preprocessing_flag                    true
% 35.39/4.95  --time_out_prep_mult                    0.1
% 35.39/4.95  --splitting_mode                        input
% 35.39/4.95  --splitting_grd                         true
% 35.39/4.95  --splitting_cvd                         false
% 35.39/4.95  --splitting_cvd_svl                     false
% 35.39/4.95  --splitting_nvd                         32
% 35.39/4.95  --sub_typing                            true
% 35.39/4.95  --prep_gs_sim                           true
% 35.39/4.95  --prep_unflatten                        true
% 35.39/4.95  --prep_res_sim                          true
% 35.39/4.95  --prep_upred                            true
% 35.39/4.95  --prep_sem_filter                       exhaustive
% 35.39/4.95  --prep_sem_filter_out                   false
% 35.39/4.95  --pred_elim                             true
% 35.39/4.95  --res_sim_input                         true
% 35.39/4.95  --eq_ax_congr_red                       true
% 35.39/4.95  --pure_diseq_elim                       true
% 35.39/4.95  --brand_transform                       false
% 35.39/4.95  --non_eq_to_eq                          false
% 35.39/4.95  --prep_def_merge                        true
% 35.39/4.95  --prep_def_merge_prop_impl              false
% 35.39/4.95  --prep_def_merge_mbd                    true
% 35.39/4.95  --prep_def_merge_tr_red                 false
% 35.39/4.95  --prep_def_merge_tr_cl                  false
% 35.39/4.95  --smt_preprocessing                     true
% 35.39/4.95  --smt_ac_axioms                         fast
% 35.39/4.95  --preprocessed_out                      false
% 35.39/4.95  --preprocessed_stats                    false
% 35.39/4.95  
% 35.39/4.95  ------ Abstraction refinement Options
% 35.39/4.95  
% 35.39/4.95  --abstr_ref                             []
% 35.39/4.95  --abstr_ref_prep                        false
% 35.39/4.95  --abstr_ref_until_sat                   false
% 35.39/4.95  --abstr_ref_sig_restrict                funpre
% 35.39/4.95  --abstr_ref_af_restrict_to_split_sk     false
% 35.39/4.95  --abstr_ref_under                       []
% 35.39/4.95  
% 35.39/4.95  ------ SAT Options
% 35.39/4.95  
% 35.39/4.95  --sat_mode                              false
% 35.39/4.95  --sat_fm_restart_options                ""
% 35.39/4.95  --sat_gr_def                            false
% 35.39/4.95  --sat_epr_types                         true
% 35.39/4.95  --sat_non_cyclic_types                  false
% 35.39/4.95  --sat_finite_models                     false
% 35.39/4.95  --sat_fm_lemmas                         false
% 35.39/4.95  --sat_fm_prep                           false
% 35.39/4.95  --sat_fm_uc_incr                        true
% 35.39/4.95  --sat_out_model                         small
% 35.39/4.95  --sat_out_clauses                       false
% 35.39/4.95  
% 35.39/4.95  ------ QBF Options
% 35.39/4.95  
% 35.39/4.95  --qbf_mode                              false
% 35.39/4.95  --qbf_elim_univ                         false
% 35.39/4.95  --qbf_dom_inst                          none
% 35.39/4.95  --qbf_dom_pre_inst                      false
% 35.39/4.95  --qbf_sk_in                             false
% 35.39/4.95  --qbf_pred_elim                         true
% 35.39/4.95  --qbf_split                             512
% 35.39/4.95  
% 35.39/4.95  ------ BMC1 Options
% 35.39/4.95  
% 35.39/4.95  --bmc1_incremental                      false
% 35.39/4.95  --bmc1_axioms                           reachable_all
% 35.39/4.95  --bmc1_min_bound                        0
% 35.39/4.95  --bmc1_max_bound                        -1
% 35.39/4.95  --bmc1_max_bound_default                -1
% 35.39/4.95  --bmc1_symbol_reachability              true
% 35.39/4.95  --bmc1_property_lemmas                  false
% 35.39/4.95  --bmc1_k_induction                      false
% 35.39/4.95  --bmc1_non_equiv_states                 false
% 35.39/4.95  --bmc1_deadlock                         false
% 35.39/4.95  --bmc1_ucm                              false
% 35.39/4.95  --bmc1_add_unsat_core                   none
% 35.39/4.95  --bmc1_unsat_core_children              false
% 35.39/4.95  --bmc1_unsat_core_extrapolate_axioms    false
% 35.39/4.95  --bmc1_out_stat                         full
% 35.39/4.95  --bmc1_ground_init                      false
% 35.39/4.95  --bmc1_pre_inst_next_state              false
% 35.39/4.95  --bmc1_pre_inst_state                   false
% 35.39/4.95  --bmc1_pre_inst_reach_state             false
% 35.39/4.95  --bmc1_out_unsat_core                   false
% 35.39/4.95  --bmc1_aig_witness_out                  false
% 35.39/4.95  --bmc1_verbose                          false
% 35.39/4.95  --bmc1_dump_clauses_tptp                false
% 35.39/4.95  --bmc1_dump_unsat_core_tptp             false
% 35.39/4.95  --bmc1_dump_file                        -
% 35.39/4.95  --bmc1_ucm_expand_uc_limit              128
% 35.39/4.95  --bmc1_ucm_n_expand_iterations          6
% 35.39/4.95  --bmc1_ucm_extend_mode                  1
% 35.39/4.95  --bmc1_ucm_init_mode                    2
% 35.39/4.95  --bmc1_ucm_cone_mode                    none
% 35.39/4.95  --bmc1_ucm_reduced_relation_type        0
% 35.39/4.95  --bmc1_ucm_relax_model                  4
% 35.39/4.95  --bmc1_ucm_full_tr_after_sat            true
% 35.39/4.95  --bmc1_ucm_expand_neg_assumptions       false
% 35.39/4.95  --bmc1_ucm_layered_model                none
% 35.39/4.95  --bmc1_ucm_max_lemma_size               10
% 35.39/4.95  
% 35.39/4.95  ------ AIG Options
% 35.39/4.95  
% 35.39/4.95  --aig_mode                              false
% 35.39/4.95  
% 35.39/4.95  ------ Instantiation Options
% 35.39/4.95  
% 35.39/4.95  --instantiation_flag                    true
% 35.39/4.95  --inst_sos_flag                         true
% 35.39/4.95  --inst_sos_phase                        true
% 35.39/4.95  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 35.39/4.95  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 35.39/4.95  --inst_lit_sel_side                     num_symb
% 35.39/4.95  --inst_solver_per_active                1400
% 35.39/4.95  --inst_solver_calls_frac                1.
% 35.39/4.95  --inst_passive_queue_type               priority_queues
% 35.39/4.95  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 35.39/4.95  --inst_passive_queues_freq              [25;2]
% 35.39/4.95  --inst_dismatching                      true
% 35.39/4.95  --inst_eager_unprocessed_to_passive     true
% 35.39/4.95  --inst_prop_sim_given                   true
% 35.39/4.95  --inst_prop_sim_new                     false
% 35.39/4.95  --inst_subs_new                         false
% 35.39/4.95  --inst_eq_res_simp                      false
% 35.39/4.95  --inst_subs_given                       false
% 35.39/4.95  --inst_orphan_elimination               true
% 35.39/4.95  --inst_learning_loop_flag               true
% 35.39/4.95  --inst_learning_start                   3000
% 35.39/4.95  --inst_learning_factor                  2
% 35.39/4.95  --inst_start_prop_sim_after_learn       3
% 35.39/4.95  --inst_sel_renew                        solver
% 35.39/4.95  --inst_lit_activity_flag                true
% 35.39/4.95  --inst_restr_to_given                   false
% 35.39/4.95  --inst_activity_threshold               500
% 35.39/4.95  --inst_out_proof                        true
% 35.39/4.95  
% 35.39/4.95  ------ Resolution Options
% 35.39/4.95  
% 35.39/4.95  --resolution_flag                       true
% 35.39/4.95  --res_lit_sel                           adaptive
% 35.39/4.95  --res_lit_sel_side                      none
% 35.39/4.95  --res_ordering                          kbo
% 35.39/4.95  --res_to_prop_solver                    active
% 35.39/4.95  --res_prop_simpl_new                    false
% 35.39/4.95  --res_prop_simpl_given                  true
% 35.39/4.95  --res_passive_queue_type                priority_queues
% 35.39/4.95  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 35.39/4.95  --res_passive_queues_freq               [15;5]
% 35.39/4.95  --res_forward_subs                      full
% 35.39/4.95  --res_backward_subs                     full
% 35.39/4.95  --res_forward_subs_resolution           true
% 35.39/4.95  --res_backward_subs_resolution          true
% 35.39/4.95  --res_orphan_elimination                true
% 35.39/4.95  --res_time_limit                        2.
% 35.39/4.95  --res_out_proof                         true
% 35.39/4.95  
% 35.39/4.95  ------ Superposition Options
% 35.39/4.95  
% 35.39/4.95  --superposition_flag                    true
% 35.39/4.95  --sup_passive_queue_type                priority_queues
% 35.39/4.95  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 35.39/4.95  --sup_passive_queues_freq               [8;1;4]
% 35.39/4.95  --demod_completeness_check              fast
% 35.39/4.95  --demod_use_ground                      true
% 35.39/4.95  --sup_to_prop_solver                    passive
% 35.39/4.95  --sup_prop_simpl_new                    true
% 35.39/4.95  --sup_prop_simpl_given                  true
% 35.39/4.95  --sup_fun_splitting                     true
% 35.39/4.95  --sup_smt_interval                      50000
% 35.39/4.95  
% 35.39/4.95  ------ Superposition Simplification Setup
% 35.39/4.95  
% 35.39/4.95  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 35.39/4.95  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 35.39/4.95  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 35.39/4.95  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 35.39/4.95  --sup_full_triv                         [TrivRules;PropSubs]
% 35.39/4.95  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 35.39/4.95  --sup_full_bw                           [BwDemod;BwSubsumption]
% 35.39/4.95  --sup_immed_triv                        [TrivRules]
% 35.39/4.95  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 35.39/4.95  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.39/4.95  --sup_immed_bw_main                     []
% 35.39/4.95  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 35.39/4.95  --sup_input_triv                        [Unflattening;TrivRules]
% 35.39/4.95  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.39/4.95  --sup_input_bw                          []
% 35.39/4.95  
% 35.39/4.95  ------ Combination Options
% 35.39/4.95  
% 35.39/4.95  --comb_res_mult                         3
% 35.39/4.95  --comb_sup_mult                         2
% 35.39/4.95  --comb_inst_mult                        10
% 35.39/4.95  
% 35.39/4.95  ------ Debug Options
% 35.39/4.95  
% 35.39/4.95  --dbg_backtrace                         false
% 35.39/4.95  --dbg_dump_prop_clauses                 false
% 35.39/4.95  --dbg_dump_prop_clauses_file            -
% 35.39/4.95  --dbg_out_stat                          false
% 35.39/4.95  ------ Parsing...
% 35.39/4.95  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 35.39/4.95  
% 35.39/4.95  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 35.39/4.95  
% 35.39/4.95  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 35.39/4.95  
% 35.39/4.95  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.39/4.95  ------ Proving...
% 35.39/4.95  ------ Problem Properties 
% 35.39/4.95  
% 35.39/4.95  
% 35.39/4.95  clauses                                 29
% 35.39/4.95  conjectures                             4
% 35.39/4.95  EPR                                     4
% 35.39/4.95  Horn                                    26
% 35.39/4.95  unary                                   5
% 35.39/4.95  binary                                  8
% 35.39/4.95  lits                                    78
% 35.39/4.95  lits eq                                 28
% 35.39/4.95  fd_pure                                 0
% 35.39/4.95  fd_pseudo                               0
% 35.39/4.95  fd_cond                                 2
% 35.39/4.95  fd_pseudo_cond                          0
% 35.39/4.95  AC symbols                              0
% 35.39/4.95  
% 35.39/4.95  ------ Schedule dynamic 5 is on 
% 35.39/4.95  
% 35.39/4.95  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 35.39/4.95  
% 35.39/4.95  
% 35.39/4.95  ------ 
% 35.39/4.95  Current options:
% 35.39/4.95  ------ 
% 35.39/4.95  
% 35.39/4.95  ------ Input Options
% 35.39/4.95  
% 35.39/4.95  --out_options                           all
% 35.39/4.95  --tptp_safe_out                         true
% 35.39/4.95  --problem_path                          ""
% 35.39/4.95  --include_path                          ""
% 35.39/4.95  --clausifier                            res/vclausify_rel
% 35.39/4.95  --clausifier_options                    ""
% 35.39/4.95  --stdin                                 false
% 35.39/4.95  --stats_out                             all
% 35.39/4.95  
% 35.39/4.95  ------ General Options
% 35.39/4.95  
% 35.39/4.95  --fof                                   false
% 35.39/4.95  --time_out_real                         305.
% 35.39/4.95  --time_out_virtual                      -1.
% 35.39/4.95  --symbol_type_check                     false
% 35.39/4.95  --clausify_out                          false
% 35.39/4.95  --sig_cnt_out                           false
% 35.39/4.95  --trig_cnt_out                          false
% 35.39/4.95  --trig_cnt_out_tolerance                1.
% 35.39/4.95  --trig_cnt_out_sk_spl                   false
% 35.39/4.95  --abstr_cl_out                          false
% 35.39/4.95  
% 35.39/4.95  ------ Global Options
% 35.39/4.95  
% 35.39/4.95  --schedule                              default
% 35.39/4.95  --add_important_lit                     false
% 35.39/4.95  --prop_solver_per_cl                    1000
% 35.39/4.95  --min_unsat_core                        false
% 35.39/4.95  --soft_assumptions                      false
% 35.39/4.95  --soft_lemma_size                       3
% 35.39/4.95  --prop_impl_unit_size                   0
% 35.39/4.95  --prop_impl_unit                        []
% 35.39/4.95  --share_sel_clauses                     true
% 35.39/4.95  --reset_solvers                         false
% 35.39/4.95  --bc_imp_inh                            [conj_cone]
% 35.39/4.95  --conj_cone_tolerance                   3.
% 35.39/4.95  --extra_neg_conj                        none
% 35.39/4.95  --large_theory_mode                     true
% 35.39/4.95  --prolific_symb_bound                   200
% 35.39/4.95  --lt_threshold                          2000
% 35.39/4.95  --clause_weak_htbl                      true
% 35.39/4.95  --gc_record_bc_elim                     false
% 35.39/4.95  
% 35.39/4.95  ------ Preprocessing Options
% 35.39/4.95  
% 35.39/4.95  --preprocessing_flag                    true
% 35.39/4.95  --time_out_prep_mult                    0.1
% 35.39/4.95  --splitting_mode                        input
% 35.39/4.95  --splitting_grd                         true
% 35.39/4.95  --splitting_cvd                         false
% 35.39/4.95  --splitting_cvd_svl                     false
% 35.39/4.95  --splitting_nvd                         32
% 35.39/4.95  --sub_typing                            true
% 35.39/4.95  --prep_gs_sim                           true
% 35.39/4.95  --prep_unflatten                        true
% 35.39/4.95  --prep_res_sim                          true
% 35.39/4.95  --prep_upred                            true
% 35.39/4.95  --prep_sem_filter                       exhaustive
% 35.39/4.95  --prep_sem_filter_out                   false
% 35.39/4.95  --pred_elim                             true
% 35.39/4.95  --res_sim_input                         true
% 35.39/4.95  --eq_ax_congr_red                       true
% 35.39/4.95  --pure_diseq_elim                       true
% 35.39/4.95  --brand_transform                       false
% 35.39/4.95  --non_eq_to_eq                          false
% 35.39/4.95  --prep_def_merge                        true
% 35.39/4.95  --prep_def_merge_prop_impl              false
% 35.39/4.95  --prep_def_merge_mbd                    true
% 35.39/4.95  --prep_def_merge_tr_red                 false
% 35.39/4.95  --prep_def_merge_tr_cl                  false
% 35.39/4.95  --smt_preprocessing                     true
% 35.39/4.95  --smt_ac_axioms                         fast
% 35.39/4.95  --preprocessed_out                      false
% 35.39/4.95  --preprocessed_stats                    false
% 35.39/4.95  
% 35.39/4.95  ------ Abstraction refinement Options
% 35.39/4.95  
% 35.39/4.95  --abstr_ref                             []
% 35.39/4.95  --abstr_ref_prep                        false
% 35.39/4.95  --abstr_ref_until_sat                   false
% 35.39/4.95  --abstr_ref_sig_restrict                funpre
% 35.39/4.95  --abstr_ref_af_restrict_to_split_sk     false
% 35.39/4.95  --abstr_ref_under                       []
% 35.39/4.95  
% 35.39/4.95  ------ SAT Options
% 35.39/4.95  
% 35.39/4.95  --sat_mode                              false
% 35.39/4.95  --sat_fm_restart_options                ""
% 35.39/4.95  --sat_gr_def                            false
% 35.39/4.95  --sat_epr_types                         true
% 35.39/4.95  --sat_non_cyclic_types                  false
% 35.39/4.95  --sat_finite_models                     false
% 35.39/4.95  --sat_fm_lemmas                         false
% 35.39/4.95  --sat_fm_prep                           false
% 35.39/4.95  --sat_fm_uc_incr                        true
% 35.39/4.95  --sat_out_model                         small
% 35.39/4.95  --sat_out_clauses                       false
% 35.39/4.95  
% 35.39/4.95  ------ QBF Options
% 35.39/4.95  
% 35.39/4.95  --qbf_mode                              false
% 35.39/4.95  --qbf_elim_univ                         false
% 35.39/4.95  --qbf_dom_inst                          none
% 35.39/4.95  --qbf_dom_pre_inst                      false
% 35.39/4.95  --qbf_sk_in                             false
% 35.39/4.95  --qbf_pred_elim                         true
% 35.39/4.95  --qbf_split                             512
% 35.39/4.95  
% 35.39/4.95  ------ BMC1 Options
% 35.39/4.95  
% 35.39/4.95  --bmc1_incremental                      false
% 35.39/4.95  --bmc1_axioms                           reachable_all
% 35.39/4.95  --bmc1_min_bound                        0
% 35.39/4.95  --bmc1_max_bound                        -1
% 35.39/4.95  --bmc1_max_bound_default                -1
% 35.39/4.95  --bmc1_symbol_reachability              true
% 35.39/4.95  --bmc1_property_lemmas                  false
% 35.39/4.95  --bmc1_k_induction                      false
% 35.39/4.95  --bmc1_non_equiv_states                 false
% 35.39/4.95  --bmc1_deadlock                         false
% 35.39/4.95  --bmc1_ucm                              false
% 35.39/4.95  --bmc1_add_unsat_core                   none
% 35.39/4.95  --bmc1_unsat_core_children              false
% 35.39/4.95  --bmc1_unsat_core_extrapolate_axioms    false
% 35.39/4.95  --bmc1_out_stat                         full
% 35.39/4.95  --bmc1_ground_init                      false
% 35.39/4.95  --bmc1_pre_inst_next_state              false
% 35.39/4.95  --bmc1_pre_inst_state                   false
% 35.39/4.95  --bmc1_pre_inst_reach_state             false
% 35.39/4.95  --bmc1_out_unsat_core                   false
% 35.39/4.95  --bmc1_aig_witness_out                  false
% 35.39/4.95  --bmc1_verbose                          false
% 35.39/4.95  --bmc1_dump_clauses_tptp                false
% 35.39/4.95  --bmc1_dump_unsat_core_tptp             false
% 35.39/4.95  --bmc1_dump_file                        -
% 35.39/4.95  --bmc1_ucm_expand_uc_limit              128
% 35.39/4.95  --bmc1_ucm_n_expand_iterations          6
% 35.39/4.95  --bmc1_ucm_extend_mode                  1
% 35.39/4.95  --bmc1_ucm_init_mode                    2
% 35.39/4.95  --bmc1_ucm_cone_mode                    none
% 35.39/4.95  --bmc1_ucm_reduced_relation_type        0
% 35.39/4.95  --bmc1_ucm_relax_model                  4
% 35.39/4.95  --bmc1_ucm_full_tr_after_sat            true
% 35.39/4.95  --bmc1_ucm_expand_neg_assumptions       false
% 35.39/4.95  --bmc1_ucm_layered_model                none
% 35.39/4.95  --bmc1_ucm_max_lemma_size               10
% 35.39/4.95  
% 35.39/4.95  ------ AIG Options
% 35.39/4.95  
% 35.39/4.95  --aig_mode                              false
% 35.39/4.95  
% 35.39/4.95  ------ Instantiation Options
% 35.39/4.95  
% 35.39/4.95  --instantiation_flag                    true
% 35.39/4.95  --inst_sos_flag                         true
% 35.39/4.95  --inst_sos_phase                        true
% 35.39/4.95  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 35.39/4.95  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 35.39/4.95  --inst_lit_sel_side                     none
% 35.39/4.95  --inst_solver_per_active                1400
% 35.39/4.95  --inst_solver_calls_frac                1.
% 35.39/4.95  --inst_passive_queue_type               priority_queues
% 35.39/4.95  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 35.39/4.95  --inst_passive_queues_freq              [25;2]
% 35.39/4.95  --inst_dismatching                      true
% 35.39/4.95  --inst_eager_unprocessed_to_passive     true
% 35.39/4.95  --inst_prop_sim_given                   true
% 35.39/4.95  --inst_prop_sim_new                     false
% 35.39/4.95  --inst_subs_new                         false
% 35.39/4.95  --inst_eq_res_simp                      false
% 35.39/4.95  --inst_subs_given                       false
% 35.39/4.95  --inst_orphan_elimination               true
% 35.39/4.95  --inst_learning_loop_flag               true
% 35.39/4.95  --inst_learning_start                   3000
% 35.39/4.95  --inst_learning_factor                  2
% 35.39/4.95  --inst_start_prop_sim_after_learn       3
% 35.39/4.95  --inst_sel_renew                        solver
% 35.39/4.95  --inst_lit_activity_flag                true
% 35.39/4.95  --inst_restr_to_given                   false
% 35.39/4.95  --inst_activity_threshold               500
% 35.39/4.95  --inst_out_proof                        true
% 35.39/4.95  
% 35.39/4.95  ------ Resolution Options
% 35.39/4.95  
% 35.39/4.95  --resolution_flag                       false
% 35.39/4.95  --res_lit_sel                           adaptive
% 35.39/4.95  --res_lit_sel_side                      none
% 35.39/4.95  --res_ordering                          kbo
% 35.39/4.95  --res_to_prop_solver                    active
% 35.39/4.95  --res_prop_simpl_new                    false
% 35.39/4.95  --res_prop_simpl_given                  true
% 35.39/4.95  --res_passive_queue_type                priority_queues
% 35.39/4.95  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 35.39/4.95  --res_passive_queues_freq               [15;5]
% 35.39/4.95  --res_forward_subs                      full
% 35.39/4.95  --res_backward_subs                     full
% 35.39/4.95  --res_forward_subs_resolution           true
% 35.39/4.95  --res_backward_subs_resolution          true
% 35.39/4.95  --res_orphan_elimination                true
% 35.39/4.95  --res_time_limit                        2.
% 35.39/4.95  --res_out_proof                         true
% 35.39/4.95  
% 35.39/4.95  ------ Superposition Options
% 35.39/4.95  
% 35.39/4.95  --superposition_flag                    true
% 35.39/4.95  --sup_passive_queue_type                priority_queues
% 35.39/4.95  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 35.39/4.95  --sup_passive_queues_freq               [8;1;4]
% 35.39/4.95  --demod_completeness_check              fast
% 35.39/4.95  --demod_use_ground                      true
% 35.39/4.95  --sup_to_prop_solver                    passive
% 35.39/4.95  --sup_prop_simpl_new                    true
% 35.39/4.95  --sup_prop_simpl_given                  true
% 35.39/4.95  --sup_fun_splitting                     true
% 35.39/4.95  --sup_smt_interval                      50000
% 35.39/4.95  
% 35.39/4.95  ------ Superposition Simplification Setup
% 35.39/4.95  
% 35.39/4.95  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 35.39/4.95  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 35.39/4.95  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 35.39/4.95  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 35.39/4.95  --sup_full_triv                         [TrivRules;PropSubs]
% 35.39/4.95  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 35.39/4.95  --sup_full_bw                           [BwDemod;BwSubsumption]
% 35.39/4.95  --sup_immed_triv                        [TrivRules]
% 35.39/4.95  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 35.39/4.95  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.39/4.95  --sup_immed_bw_main                     []
% 35.39/4.95  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 35.39/4.95  --sup_input_triv                        [Unflattening;TrivRules]
% 35.39/4.95  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.39/4.95  --sup_input_bw                          []
% 35.39/4.95  
% 35.39/4.95  ------ Combination Options
% 35.39/4.95  
% 35.39/4.95  --comb_res_mult                         3
% 35.39/4.95  --comb_sup_mult                         2
% 35.39/4.95  --comb_inst_mult                        10
% 35.39/4.95  
% 35.39/4.95  ------ Debug Options
% 35.39/4.95  
% 35.39/4.95  --dbg_backtrace                         false
% 35.39/4.95  --dbg_dump_prop_clauses                 false
% 35.39/4.95  --dbg_dump_prop_clauses_file            -
% 35.39/4.95  --dbg_out_stat                          false
% 35.39/4.95  
% 35.39/4.95  
% 35.39/4.95  
% 35.39/4.95  
% 35.39/4.95  ------ Proving...
% 35.39/4.95  
% 35.39/4.95  
% 35.39/4.95  % SZS status Theorem for theBenchmark.p
% 35.39/4.95  
% 35.39/4.95  % SZS output start CNFRefutation for theBenchmark.p
% 35.39/4.95  
% 35.39/4.95  fof(f15,conjecture,(
% 35.39/4.95    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 35.39/4.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.39/4.95  
% 35.39/4.95  fof(f16,negated_conjecture,(
% 35.39/4.95    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 35.39/4.95    inference(negated_conjecture,[],[f15])).
% 35.39/4.95  
% 35.39/4.95  fof(f37,plain,(
% 35.39/4.95    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 35.39/4.95    inference(ennf_transformation,[],[f16])).
% 35.39/4.95  
% 35.39/4.95  fof(f38,plain,(
% 35.39/4.95    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 35.39/4.95    inference(flattening,[],[f37])).
% 35.39/4.95  
% 35.39/4.95  fof(f43,plain,(
% 35.39/4.95    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 35.39/4.95    introduced(choice_axiom,[])).
% 35.39/4.95  
% 35.39/4.95  fof(f44,plain,(
% 35.39/4.95    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 35.39/4.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f38,f43])).
% 35.39/4.95  
% 35.39/4.95  fof(f73,plain,(
% 35.39/4.95    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 35.39/4.95    inference(cnf_transformation,[],[f44])).
% 35.39/4.95  
% 35.39/4.95  fof(f14,axiom,(
% 35.39/4.95    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 35.39/4.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.39/4.95  
% 35.39/4.95  fof(f35,plain,(
% 35.39/4.95    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 35.39/4.95    inference(ennf_transformation,[],[f14])).
% 35.39/4.95  
% 35.39/4.95  fof(f36,plain,(
% 35.39/4.95    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 35.39/4.95    inference(flattening,[],[f35])).
% 35.39/4.95  
% 35.39/4.95  fof(f70,plain,(
% 35.39/4.95    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 35.39/4.95    inference(cnf_transformation,[],[f36])).
% 35.39/4.95  
% 35.39/4.95  fof(f71,plain,(
% 35.39/4.95    v1_funct_1(sK3)),
% 35.39/4.95    inference(cnf_transformation,[],[f44])).
% 35.39/4.95  
% 35.39/4.95  fof(f13,axiom,(
% 35.39/4.95    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 35.39/4.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.39/4.95  
% 35.39/4.95  fof(f33,plain,(
% 35.39/4.95    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 35.39/4.95    inference(ennf_transformation,[],[f13])).
% 35.39/4.95  
% 35.39/4.95  fof(f34,plain,(
% 35.39/4.95    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 35.39/4.95    inference(flattening,[],[f33])).
% 35.39/4.95  
% 35.39/4.95  fof(f68,plain,(
% 35.39/4.95    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 35.39/4.95    inference(cnf_transformation,[],[f34])).
% 35.39/4.95  
% 35.39/4.95  fof(f74,plain,(
% 35.39/4.95    r1_tarski(sK2,sK0)),
% 35.39/4.95    inference(cnf_transformation,[],[f44])).
% 35.39/4.95  
% 35.39/4.95  fof(f12,axiom,(
% 35.39/4.95    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 35.39/4.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.39/4.95  
% 35.39/4.95  fof(f31,plain,(
% 35.39/4.95    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 35.39/4.95    inference(ennf_transformation,[],[f12])).
% 35.39/4.95  
% 35.39/4.95  fof(f32,plain,(
% 35.39/4.95    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 35.39/4.95    inference(flattening,[],[f31])).
% 35.39/4.95  
% 35.39/4.95  fof(f42,plain,(
% 35.39/4.95    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 35.39/4.95    inference(nnf_transformation,[],[f32])).
% 35.39/4.95  
% 35.39/4.95  fof(f62,plain,(
% 35.39/4.95    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 35.39/4.95    inference(cnf_transformation,[],[f42])).
% 35.39/4.95  
% 35.39/4.95  fof(f72,plain,(
% 35.39/4.95    v1_funct_2(sK3,sK0,sK1)),
% 35.39/4.95    inference(cnf_transformation,[],[f44])).
% 35.39/4.95  
% 35.39/4.95  fof(f10,axiom,(
% 35.39/4.95    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 35.39/4.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.39/4.95  
% 35.39/4.95  fof(f28,plain,(
% 35.39/4.95    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 35.39/4.95    inference(ennf_transformation,[],[f10])).
% 35.39/4.95  
% 35.39/4.95  fof(f60,plain,(
% 35.39/4.95    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 35.39/4.95    inference(cnf_transformation,[],[f28])).
% 35.39/4.95  
% 35.39/4.95  fof(f7,axiom,(
% 35.39/4.95    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 35.39/4.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.39/4.95  
% 35.39/4.95  fof(f24,plain,(
% 35.39/4.95    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 35.39/4.95    inference(ennf_transformation,[],[f7])).
% 35.39/4.95  
% 35.39/4.95  fof(f25,plain,(
% 35.39/4.95    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 35.39/4.95    inference(flattening,[],[f24])).
% 35.39/4.95  
% 35.39/4.95  fof(f56,plain,(
% 35.39/4.95    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 35.39/4.95    inference(cnf_transformation,[],[f25])).
% 35.39/4.95  
% 35.39/4.95  fof(f8,axiom,(
% 35.39/4.95    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 35.39/4.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.39/4.95  
% 35.39/4.95  fof(f26,plain,(
% 35.39/4.95    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 35.39/4.95    inference(ennf_transformation,[],[f8])).
% 35.39/4.95  
% 35.39/4.95  fof(f57,plain,(
% 35.39/4.95    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 35.39/4.95    inference(cnf_transformation,[],[f26])).
% 35.39/4.95  
% 35.39/4.95  fof(f69,plain,(
% 35.39/4.95    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 35.39/4.95    inference(cnf_transformation,[],[f34])).
% 35.39/4.95  
% 35.39/4.95  fof(f3,axiom,(
% 35.39/4.95    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 35.39/4.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.39/4.95  
% 35.39/4.95  fof(f18,plain,(
% 35.39/4.95    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 35.39/4.95    inference(ennf_transformation,[],[f3])).
% 35.39/4.95  
% 35.39/4.95  fof(f41,plain,(
% 35.39/4.95    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 35.39/4.95    inference(nnf_transformation,[],[f18])).
% 35.39/4.95  
% 35.39/4.95  fof(f49,plain,(
% 35.39/4.95    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 35.39/4.95    inference(cnf_transformation,[],[f41])).
% 35.39/4.95  
% 35.39/4.95  fof(f9,axiom,(
% 35.39/4.95    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 35.39/4.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.39/4.95  
% 35.39/4.95  fof(f27,plain,(
% 35.39/4.95    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 35.39/4.95    inference(ennf_transformation,[],[f9])).
% 35.39/4.95  
% 35.39/4.95  fof(f59,plain,(
% 35.39/4.95    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 35.39/4.95    inference(cnf_transformation,[],[f27])).
% 35.39/4.95  
% 35.39/4.95  fof(f2,axiom,(
% 35.39/4.95    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 35.39/4.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.39/4.95  
% 35.39/4.95  fof(f39,plain,(
% 35.39/4.95    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 35.39/4.95    inference(nnf_transformation,[],[f2])).
% 35.39/4.95  
% 35.39/4.95  fof(f40,plain,(
% 35.39/4.95    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 35.39/4.95    inference(flattening,[],[f39])).
% 35.39/4.95  
% 35.39/4.95  fof(f47,plain,(
% 35.39/4.95    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 35.39/4.95    inference(cnf_transformation,[],[f40])).
% 35.39/4.95  
% 35.39/4.95  fof(f78,plain,(
% 35.39/4.95    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 35.39/4.95    inference(equality_resolution,[],[f47])).
% 35.39/4.95  
% 35.39/4.95  fof(f11,axiom,(
% 35.39/4.95    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 35.39/4.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.39/4.95  
% 35.39/4.95  fof(f29,plain,(
% 35.39/4.95    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 35.39/4.95    inference(ennf_transformation,[],[f11])).
% 35.39/4.95  
% 35.39/4.95  fof(f30,plain,(
% 35.39/4.95    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 35.39/4.95    inference(flattening,[],[f29])).
% 35.39/4.95  
% 35.39/4.95  fof(f61,plain,(
% 35.39/4.95    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 35.39/4.95    inference(cnf_transformation,[],[f30])).
% 35.39/4.95  
% 35.39/4.95  fof(f58,plain,(
% 35.39/4.95    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 35.39/4.95    inference(cnf_transformation,[],[f27])).
% 35.39/4.95  
% 35.39/4.95  fof(f4,axiom,(
% 35.39/4.95    ! [X0,X1,X2] : ((v4_relat_1(X2,X1) & v1_relat_1(X2)) => (v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))))),
% 35.39/4.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.39/4.95  
% 35.39/4.95  fof(f19,plain,(
% 35.39/4.95    ! [X0,X1,X2] : ((v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))) | (~v4_relat_1(X2,X1) | ~v1_relat_1(X2)))),
% 35.39/4.95    inference(ennf_transformation,[],[f4])).
% 35.39/4.95  
% 35.39/4.95  fof(f20,plain,(
% 35.39/4.95    ! [X0,X1,X2] : ((v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))) | ~v4_relat_1(X2,X1) | ~v1_relat_1(X2))),
% 35.39/4.95    inference(flattening,[],[f19])).
% 35.39/4.95  
% 35.39/4.95  fof(f51,plain,(
% 35.39/4.95    ( ! [X2,X0,X1] : (v1_relat_1(k7_relat_1(X2,X0)) | ~v4_relat_1(X2,X1) | ~v1_relat_1(X2)) )),
% 35.39/4.95    inference(cnf_transformation,[],[f20])).
% 35.39/4.95  
% 35.39/4.95  fof(f6,axiom,(
% 35.39/4.95    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 35.39/4.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.39/4.95  
% 35.39/4.95  fof(f23,plain,(
% 35.39/4.95    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 35.39/4.95    inference(ennf_transformation,[],[f6])).
% 35.39/4.95  
% 35.39/4.95  fof(f55,plain,(
% 35.39/4.95    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 35.39/4.95    inference(cnf_transformation,[],[f23])).
% 35.39/4.95  
% 35.39/4.95  fof(f64,plain,(
% 35.39/4.95    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 35.39/4.95    inference(cnf_transformation,[],[f42])).
% 35.39/4.95  
% 35.39/4.95  fof(f76,plain,(
% 35.39/4.95    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 35.39/4.95    inference(cnf_transformation,[],[f44])).
% 35.39/4.95  
% 35.39/4.95  fof(f67,plain,(
% 35.39/4.95    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 35.39/4.95    inference(cnf_transformation,[],[f42])).
% 35.39/4.95  
% 35.39/4.95  fof(f79,plain,(
% 35.39/4.95    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 35.39/4.95    inference(equality_resolution,[],[f67])).
% 35.39/4.95  
% 35.39/4.95  fof(f80,plain,(
% 35.39/4.95    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 35.39/4.95    inference(equality_resolution,[],[f79])).
% 35.39/4.95  
% 35.39/4.95  fof(f48,plain,(
% 35.39/4.95    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 35.39/4.95    inference(cnf_transformation,[],[f40])).
% 35.39/4.95  
% 35.39/4.95  fof(f77,plain,(
% 35.39/4.95    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 35.39/4.95    inference(equality_resolution,[],[f48])).
% 35.39/4.95  
% 35.39/4.95  fof(f46,plain,(
% 35.39/4.95    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 35.39/4.95    inference(cnf_transformation,[],[f40])).
% 35.39/4.95  
% 35.39/4.95  fof(f1,axiom,(
% 35.39/4.95    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 35.39/4.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.39/4.95  
% 35.39/4.95  fof(f17,plain,(
% 35.39/4.95    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 35.39/4.95    inference(ennf_transformation,[],[f1])).
% 35.39/4.95  
% 35.39/4.95  fof(f45,plain,(
% 35.39/4.95    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 35.39/4.95    inference(cnf_transformation,[],[f17])).
% 35.39/4.95  
% 35.39/4.95  fof(f66,plain,(
% 35.39/4.95    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 35.39/4.95    inference(cnf_transformation,[],[f42])).
% 35.39/4.95  
% 35.39/4.95  fof(f81,plain,(
% 35.39/4.95    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 35.39/4.95    inference(equality_resolution,[],[f66])).
% 35.39/4.95  
% 35.39/4.95  fof(f75,plain,(
% 35.39/4.95    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 35.39/4.95    inference(cnf_transformation,[],[f44])).
% 35.39/4.95  
% 35.39/4.95  fof(f65,plain,(
% 35.39/4.95    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 35.39/4.95    inference(cnf_transformation,[],[f42])).
% 35.39/4.95  
% 35.39/4.95  fof(f82,plain,(
% 35.39/4.95    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 35.39/4.95    inference(equality_resolution,[],[f65])).
% 35.39/4.95  
% 35.39/4.95  fof(f52,plain,(
% 35.39/4.95    ( ! [X2,X0,X1] : (v4_relat_1(k7_relat_1(X2,X0),X0) | ~v4_relat_1(X2,X1) | ~v1_relat_1(X2)) )),
% 35.39/4.95    inference(cnf_transformation,[],[f20])).
% 35.39/4.95  
% 35.39/4.95  fof(f5,axiom,(
% 35.39/4.95    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 35.39/4.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.39/4.95  
% 35.39/4.95  fof(f21,plain,(
% 35.39/4.95    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 35.39/4.95    inference(ennf_transformation,[],[f5])).
% 35.39/4.95  
% 35.39/4.95  fof(f22,plain,(
% 35.39/4.95    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 35.39/4.95    inference(flattening,[],[f21])).
% 35.39/4.95  
% 35.39/4.95  fof(f54,plain,(
% 35.39/4.95    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 35.39/4.95    inference(cnf_transformation,[],[f22])).
% 35.39/4.95  
% 35.39/4.95  cnf(c_29,negated_conjecture,
% 35.39/4.95      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 35.39/4.95      inference(cnf_transformation,[],[f73]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_1100,plain,
% 35.39/4.95      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 35.39/4.95      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_25,plain,
% 35.39/4.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.39/4.95      | ~ v1_funct_1(X0)
% 35.39/4.95      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 35.39/4.95      inference(cnf_transformation,[],[f70]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_1102,plain,
% 35.39/4.95      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 35.39/4.95      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 35.39/4.95      | v1_funct_1(X2) != iProver_top ),
% 35.39/4.95      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_3061,plain,
% 35.39/4.95      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
% 35.39/4.95      | v1_funct_1(sK3) != iProver_top ),
% 35.39/4.95      inference(superposition,[status(thm)],[c_1100,c_1102]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_31,negated_conjecture,
% 35.39/4.95      ( v1_funct_1(sK3) ),
% 35.39/4.95      inference(cnf_transformation,[],[f71]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_32,plain,
% 35.39/4.95      ( v1_funct_1(sK3) = iProver_top ),
% 35.39/4.95      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_3109,plain,
% 35.39/4.95      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 35.39/4.95      inference(global_propositional_subsumption,
% 35.39/4.95                [status(thm)],
% 35.39/4.95                [c_3061,c_32]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_24,plain,
% 35.39/4.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.39/4.95      | ~ v1_funct_1(X0)
% 35.39/4.95      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
% 35.39/4.95      inference(cnf_transformation,[],[f68]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_1103,plain,
% 35.39/4.95      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 35.39/4.95      | v1_funct_1(X0) != iProver_top
% 35.39/4.95      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
% 35.39/4.95      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_1610,plain,
% 35.39/4.95      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
% 35.39/4.95      | v1_funct_1(sK3) != iProver_top ),
% 35.39/4.95      inference(superposition,[status(thm)],[c_1100,c_1103]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_1779,plain,
% 35.39/4.95      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
% 35.39/4.95      inference(global_propositional_subsumption,
% 35.39/4.95                [status(thm)],
% 35.39/4.95                [c_1610,c_32]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_3116,plain,
% 35.39/4.95      ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 35.39/4.95      inference(demodulation,[status(thm)],[c_3109,c_1779]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_28,negated_conjecture,
% 35.39/4.95      ( r1_tarski(sK2,sK0) ),
% 35.39/4.95      inference(cnf_transformation,[],[f74]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_1101,plain,
% 35.39/4.95      ( r1_tarski(sK2,sK0) = iProver_top ),
% 35.39/4.95      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_22,plain,
% 35.39/4.95      ( ~ v1_funct_2(X0,X1,X2)
% 35.39/4.95      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.39/4.95      | k1_relset_1(X1,X2,X0) = X1
% 35.39/4.95      | k1_xboole_0 = X2 ),
% 35.39/4.95      inference(cnf_transformation,[],[f62]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_30,negated_conjecture,
% 35.39/4.95      ( v1_funct_2(sK3,sK0,sK1) ),
% 35.39/4.95      inference(cnf_transformation,[],[f72]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_446,plain,
% 35.39/4.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.39/4.95      | k1_relset_1(X1,X2,X0) = X1
% 35.39/4.95      | sK3 != X0
% 35.39/4.95      | sK1 != X2
% 35.39/4.95      | sK0 != X1
% 35.39/4.95      | k1_xboole_0 = X2 ),
% 35.39/4.95      inference(resolution_lifted,[status(thm)],[c_22,c_30]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_447,plain,
% 35.39/4.95      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 35.39/4.95      | k1_relset_1(sK0,sK1,sK3) = sK0
% 35.39/4.95      | k1_xboole_0 = sK1 ),
% 35.39/4.95      inference(unflattening,[status(thm)],[c_446]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_449,plain,
% 35.39/4.95      ( k1_relset_1(sK0,sK1,sK3) = sK0 | k1_xboole_0 = sK1 ),
% 35.39/4.95      inference(global_propositional_subsumption,
% 35.39/4.95                [status(thm)],
% 35.39/4.95                [c_447,c_29]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_15,plain,
% 35.39/4.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.39/4.95      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 35.39/4.95      inference(cnf_transformation,[],[f60]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_1106,plain,
% 35.39/4.95      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 35.39/4.95      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 35.39/4.95      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_1841,plain,
% 35.39/4.95      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 35.39/4.95      inference(superposition,[status(thm)],[c_1100,c_1106]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_2017,plain,
% 35.39/4.95      ( k1_relat_1(sK3) = sK0 | sK1 = k1_xboole_0 ),
% 35.39/4.95      inference(superposition,[status(thm)],[c_449,c_1841]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_11,plain,
% 35.39/4.95      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 35.39/4.95      | ~ v1_relat_1(X1)
% 35.39/4.95      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 35.39/4.95      inference(cnf_transformation,[],[f56]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_1109,plain,
% 35.39/4.95      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 35.39/4.95      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 35.39/4.95      | v1_relat_1(X0) != iProver_top ),
% 35.39/4.95      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_2239,plain,
% 35.39/4.95      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 35.39/4.95      | sK1 = k1_xboole_0
% 35.39/4.95      | r1_tarski(X0,sK0) != iProver_top
% 35.39/4.95      | v1_relat_1(sK3) != iProver_top ),
% 35.39/4.95      inference(superposition,[status(thm)],[c_2017,c_1109]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_34,plain,
% 35.39/4.95      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 35.39/4.95      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_12,plain,
% 35.39/4.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.39/4.95      | v1_relat_1(X0) ),
% 35.39/4.95      inference(cnf_transformation,[],[f57]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_1266,plain,
% 35.39/4.95      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 35.39/4.95      | v1_relat_1(sK3) ),
% 35.39/4.95      inference(instantiation,[status(thm)],[c_12]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_1310,plain,
% 35.39/4.95      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 35.39/4.95      | v1_relat_1(sK3) ),
% 35.39/4.95      inference(instantiation,[status(thm)],[c_1266]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_1311,plain,
% 35.39/4.95      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 35.39/4.95      | v1_relat_1(sK3) = iProver_top ),
% 35.39/4.95      inference(predicate_to_equality,[status(thm)],[c_1310]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_2423,plain,
% 35.39/4.95      ( r1_tarski(X0,sK0) != iProver_top
% 35.39/4.95      | sK1 = k1_xboole_0
% 35.39/4.95      | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
% 35.39/4.95      inference(global_propositional_subsumption,
% 35.39/4.95                [status(thm)],
% 35.39/4.95                [c_2239,c_34,c_1311]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_2424,plain,
% 35.39/4.95      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 35.39/4.95      | sK1 = k1_xboole_0
% 35.39/4.95      | r1_tarski(X0,sK0) != iProver_top ),
% 35.39/4.95      inference(renaming,[status(thm)],[c_2423]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_2428,plain,
% 35.39/4.95      ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2 | sK1 = k1_xboole_0 ),
% 35.39/4.95      inference(superposition,[status(thm)],[c_1101,c_2424]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_23,plain,
% 35.39/4.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.39/4.95      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.39/4.95      | ~ v1_funct_1(X0) ),
% 35.39/4.95      inference(cnf_transformation,[],[f69]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_1104,plain,
% 35.39/4.95      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 35.39/4.95      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 35.39/4.95      | v1_funct_1(X0) != iProver_top ),
% 35.39/4.95      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_3125,plain,
% 35.39/4.95      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 35.39/4.95      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 35.39/4.95      | v1_funct_1(sK3) != iProver_top ),
% 35.39/4.95      inference(superposition,[status(thm)],[c_3109,c_1104]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_3228,plain,
% 35.39/4.95      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 35.39/4.95      inference(global_propositional_subsumption,
% 35.39/4.95                [status(thm)],
% 35.39/4.95                [c_3125,c_32,c_34]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_5,plain,
% 35.39/4.95      ( ~ v5_relat_1(X0,X1)
% 35.39/4.95      | r1_tarski(k2_relat_1(X0),X1)
% 35.39/4.95      | ~ v1_relat_1(X0) ),
% 35.39/4.95      inference(cnf_transformation,[],[f49]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_13,plain,
% 35.39/4.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.39/4.95      | v5_relat_1(X0,X2) ),
% 35.39/4.95      inference(cnf_transformation,[],[f59]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_323,plain,
% 35.39/4.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.39/4.95      | r1_tarski(k2_relat_1(X3),X4)
% 35.39/4.95      | ~ v1_relat_1(X3)
% 35.39/4.95      | X0 != X3
% 35.39/4.95      | X2 != X4 ),
% 35.39/4.95      inference(resolution_lifted,[status(thm)],[c_5,c_13]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_324,plain,
% 35.39/4.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.39/4.95      | r1_tarski(k2_relat_1(X0),X2)
% 35.39/4.95      | ~ v1_relat_1(X0) ),
% 35.39/4.95      inference(unflattening,[status(thm)],[c_323]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_328,plain,
% 35.39/4.95      ( r1_tarski(k2_relat_1(X0),X2)
% 35.39/4.95      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 35.39/4.95      inference(global_propositional_subsumption,
% 35.39/4.95                [status(thm)],
% 35.39/4.95                [c_324,c_12]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_329,plain,
% 35.39/4.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.39/4.95      | r1_tarski(k2_relat_1(X0),X2) ),
% 35.39/4.95      inference(renaming,[status(thm)],[c_328]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_1098,plain,
% 35.39/4.95      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 35.39/4.95      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 35.39/4.95      inference(predicate_to_equality,[status(thm)],[c_329]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_3240,plain,
% 35.39/4.95      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) = iProver_top ),
% 35.39/4.95      inference(superposition,[status(thm)],[c_3228,c_1098]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_2,plain,
% 35.39/4.95      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 35.39/4.95      inference(cnf_transformation,[],[f78]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_16,plain,
% 35.39/4.95      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.39/4.95      | ~ r1_tarski(k1_relat_1(X0),X1)
% 35.39/4.95      | ~ r1_tarski(k2_relat_1(X0),X2)
% 35.39/4.95      | ~ v1_relat_1(X0) ),
% 35.39/4.95      inference(cnf_transformation,[],[f61]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_1105,plain,
% 35.39/4.95      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 35.39/4.95      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 35.39/4.95      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 35.39/4.95      | v1_relat_1(X0) != iProver_top ),
% 35.39/4.95      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_2252,plain,
% 35.39/4.95      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 35.39/4.95      | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
% 35.39/4.95      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 35.39/4.95      | v1_relat_1(X0) != iProver_top ),
% 35.39/4.95      inference(superposition,[status(thm)],[c_2,c_1105]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_3636,plain,
% 35.39/4.95      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 35.39/4.95      | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),k1_xboole_0) != iProver_top
% 35.39/4.95      | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
% 35.39/4.95      inference(superposition,[status(thm)],[c_3240,c_2252]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_14,plain,
% 35.39/4.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.39/4.95      | v4_relat_1(X0,X1) ),
% 35.39/4.95      inference(cnf_transformation,[],[f58]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_1107,plain,
% 35.39/4.95      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 35.39/4.95      | v4_relat_1(X0,X1) = iProver_top ),
% 35.39/4.95      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_1732,plain,
% 35.39/4.95      ( v4_relat_1(sK3,sK0) = iProver_top ),
% 35.39/4.95      inference(superposition,[status(thm)],[c_1100,c_1107]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_8,plain,
% 35.39/4.95      ( ~ v4_relat_1(X0,X1)
% 35.39/4.95      | ~ v1_relat_1(X0)
% 35.39/4.95      | v1_relat_1(k7_relat_1(X0,X2)) ),
% 35.39/4.95      inference(cnf_transformation,[],[f51]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_1112,plain,
% 35.39/4.95      ( v4_relat_1(X0,X1) != iProver_top
% 35.39/4.95      | v1_relat_1(X0) != iProver_top
% 35.39/4.95      | v1_relat_1(k7_relat_1(X0,X2)) = iProver_top ),
% 35.39/4.95      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_2013,plain,
% 35.39/4.95      ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top
% 35.39/4.95      | v1_relat_1(sK3) != iProver_top ),
% 35.39/4.95      inference(superposition,[status(thm)],[c_1732,c_1112]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_7726,plain,
% 35.39/4.95      ( r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),k1_xboole_0) != iProver_top
% 35.39/4.95      | m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 35.39/4.95      inference(global_propositional_subsumption,
% 35.39/4.95                [status(thm)],
% 35.39/4.95                [c_3636,c_34,c_1311,c_2013]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_7727,plain,
% 35.39/4.95      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 35.39/4.95      | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),k1_xboole_0) != iProver_top ),
% 35.39/4.95      inference(renaming,[status(thm)],[c_7726]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_7732,plain,
% 35.39/4.95      ( sK1 = k1_xboole_0
% 35.39/4.95      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 35.39/4.95      | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
% 35.39/4.95      inference(superposition,[status(thm)],[c_2428,c_7727]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_1889,plain,
% 35.39/4.95      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 35.39/4.95      | r1_tarski(k2_relat_1(k2_partfun1(X1,X2,X0,X3)),X2) = iProver_top
% 35.39/4.95      | v1_funct_1(X0) != iProver_top ),
% 35.39/4.95      inference(superposition,[status(thm)],[c_1104,c_1098]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_2122,plain,
% 35.39/4.95      ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 35.39/4.95      inference(global_propositional_subsumption,
% 35.39/4.95                [status(thm)],
% 35.39/4.95                [c_2013,c_34,c_1311]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_2479,plain,
% 35.39/4.95      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),X0)) = X0
% 35.39/4.95      | sK1 = k1_xboole_0
% 35.39/4.95      | r1_tarski(X0,sK2) != iProver_top
% 35.39/4.95      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 35.39/4.95      inference(superposition,[status(thm)],[c_2428,c_1109]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_2677,plain,
% 35.39/4.95      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),X0)) = X0
% 35.39/4.95      | sK1 = k1_xboole_0
% 35.39/4.95      | r1_tarski(X0,sK2) != iProver_top ),
% 35.39/4.95      inference(superposition,[status(thm)],[c_2122,c_2479]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_4497,plain,
% 35.39/4.95      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),k2_relat_1(k2_partfun1(X0,sK2,X1,X2)))) = k2_relat_1(k2_partfun1(X0,sK2,X1,X2))
% 35.39/4.95      | sK1 = k1_xboole_0
% 35.39/4.95      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) != iProver_top
% 35.39/4.95      | v1_funct_1(X1) != iProver_top ),
% 35.39/4.95      inference(superposition,[status(thm)],[c_1889,c_2677]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_33178,plain,
% 35.39/4.95      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),k2_relat_1(k2_partfun1(k1_xboole_0,sK2,X0,X1)))) = k2_relat_1(k2_partfun1(k1_xboole_0,sK2,X0,X1))
% 35.39/4.95      | sK1 = k1_xboole_0
% 35.39/4.95      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 35.39/4.95      | v1_funct_1(X0) != iProver_top ),
% 35.39/4.95      inference(superposition,[status(thm)],[c_2,c_4497]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_33192,plain,
% 35.39/4.95      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),k2_relat_1(k2_partfun1(k1_xboole_0,sK2,k7_relat_1(sK3,sK2),X0)))) = k2_relat_1(k2_partfun1(k1_xboole_0,sK2,k7_relat_1(sK3,sK2),X0))
% 35.39/4.95      | sK1 = k1_xboole_0
% 35.39/4.95      | r1_tarski(sK2,k1_xboole_0) != iProver_top
% 35.39/4.95      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 35.39/4.95      inference(superposition,[status(thm)],[c_7732,c_33178]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_10,plain,
% 35.39/4.95      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 35.39/4.95      inference(cnf_transformation,[],[f55]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_1110,plain,
% 35.39/4.95      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
% 35.39/4.95      | v1_relat_1(X0) != iProver_top ),
% 35.39/4.95      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_2478,plain,
% 35.39/4.95      ( sK1 = k1_xboole_0
% 35.39/4.95      | r1_tarski(sK2,sK2) = iProver_top
% 35.39/4.95      | v1_relat_1(sK3) != iProver_top ),
% 35.39/4.95      inference(superposition,[status(thm)],[c_2428,c_1110]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_2485,plain,
% 35.39/4.95      ( r1_tarski(sK2,sK2) = iProver_top | sK1 = k1_xboole_0 ),
% 35.39/4.95      inference(global_propositional_subsumption,
% 35.39/4.95                [status(thm)],
% 35.39/4.95                [c_2478,c_34,c_1311]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_2486,plain,
% 35.39/4.95      ( sK1 = k1_xboole_0 | r1_tarski(sK2,sK2) = iProver_top ),
% 35.39/4.95      inference(renaming,[status(thm)],[c_2485]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_2253,plain,
% 35.39/4.95      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 35.39/4.95      | r1_tarski(k1_relat_1(X2),X0) != iProver_top
% 35.39/4.95      | r1_tarski(k2_relat_1(X2),X1) != iProver_top
% 35.39/4.95      | v1_relat_1(X2) != iProver_top ),
% 35.39/4.95      inference(superposition,[status(thm)],[c_1105,c_1106]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_11254,plain,
% 35.39/4.95      ( k1_relset_1(X0,X1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
% 35.39/4.95      | sK1 = k1_xboole_0
% 35.39/4.95      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1) != iProver_top
% 35.39/4.95      | r1_tarski(sK2,X0) != iProver_top
% 35.39/4.95      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 35.39/4.95      inference(superposition,[status(thm)],[c_2428,c_2253]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_11714,plain,
% 35.39/4.95      ( k1_relset_1(X0,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
% 35.39/4.95      | sK1 = k1_xboole_0
% 35.39/4.95      | r1_tarski(sK2,X0) != iProver_top
% 35.39/4.95      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 35.39/4.95      inference(superposition,[status(thm)],[c_3240,c_11254]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_25292,plain,
% 35.39/4.95      ( k1_relset_1(X0,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
% 35.39/4.95      | sK1 = k1_xboole_0
% 35.39/4.95      | r1_tarski(sK2,X0) != iProver_top ),
% 35.39/4.95      inference(superposition,[status(thm)],[c_2122,c_11714]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_25298,plain,
% 35.39/4.95      ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
% 35.39/4.95      | sK1 = k1_xboole_0 ),
% 35.39/4.95      inference(superposition,[status(thm)],[c_2486,c_25292]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_20,plain,
% 35.39/4.95      ( v1_funct_2(X0,X1,X2)
% 35.39/4.95      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.39/4.95      | k1_relset_1(X1,X2,X0) != X1
% 35.39/4.95      | k1_xboole_0 = X2 ),
% 35.39/4.95      inference(cnf_transformation,[],[f64]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_26,negated_conjecture,
% 35.39/4.95      ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
% 35.39/4.95      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 35.39/4.95      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
% 35.39/4.95      inference(cnf_transformation,[],[f76]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_430,plain,
% 35.39/4.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 35.39/4.95      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 35.39/4.95      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 35.39/4.95      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 35.39/4.95      | k1_relset_1(X1,X2,X0) != X1
% 35.39/4.95      | sK2 != X1
% 35.39/4.95      | sK1 != X2
% 35.39/4.95      | k1_xboole_0 = X2 ),
% 35.39/4.95      inference(resolution_lifted,[status(thm)],[c_20,c_26]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_431,plain,
% 35.39/4.95      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 35.39/4.95      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 35.39/4.95      | k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 35.39/4.95      | k1_xboole_0 = sK1 ),
% 35.39/4.95      inference(unflattening,[status(thm)],[c_430]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_1093,plain,
% 35.39/4.95      ( k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 35.39/4.95      | k1_xboole_0 = sK1
% 35.39/4.95      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 35.39/4.95      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 35.39/4.95      inference(predicate_to_equality,[status(thm)],[c_431]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_3115,plain,
% 35.39/4.95      ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) != sK2
% 35.39/4.95      | sK1 = k1_xboole_0
% 35.39/4.95      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 35.39/4.95      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 35.39/4.95      inference(demodulation,[status(thm)],[c_3109,c_1093]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_25335,plain,
% 35.39/4.95      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 35.39/4.95      | sK1 = k1_xboole_0
% 35.39/4.95      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 35.39/4.95      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 35.39/4.95      inference(superposition,[status(thm)],[c_25298,c_3115]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_25338,plain,
% 35.39/4.95      ( sK1 = k1_xboole_0
% 35.39/4.95      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 35.39/4.95      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 35.39/4.95      inference(global_propositional_subsumption,
% 35.39/4.95                [status(thm)],
% 35.39/4.95                [c_25335,c_2428]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_25342,plain,
% 35.39/4.95      ( sK1 = k1_xboole_0
% 35.39/4.95      | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) != iProver_top
% 35.39/4.95      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
% 35.39/4.95      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
% 35.39/4.95      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 35.39/4.95      inference(superposition,[status(thm)],[c_1105,c_25338]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_23866,plain,
% 35.39/4.95      ( r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)
% 35.39/4.95      | ~ v1_relat_1(sK3) ),
% 35.39/4.95      inference(instantiation,[status(thm)],[c_10]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_23867,plain,
% 35.39/4.95      ( r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) = iProver_top
% 35.39/4.95      | v1_relat_1(sK3) != iProver_top ),
% 35.39/4.95      inference(predicate_to_equality,[status(thm)],[c_23866]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_44267,plain,
% 35.39/4.95      ( sK1 = k1_xboole_0
% 35.39/4.95      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
% 35.39/4.95      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
% 35.39/4.95      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 35.39/4.95      inference(global_propositional_subsumption,
% 35.39/4.95                [status(thm)],
% 35.39/4.95                [c_25342,c_34,c_1311,c_23867]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_44271,plain,
% 35.39/4.95      ( sK1 = k1_xboole_0
% 35.39/4.95      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
% 35.39/4.95      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 35.39/4.95      inference(superposition,[status(thm)],[c_3240,c_44267]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_37278,plain,
% 35.39/4.95      ( ~ v4_relat_1(sK3,X0)
% 35.39/4.95      | v1_relat_1(k7_relat_1(sK3,X1))
% 35.39/4.95      | ~ v1_relat_1(sK3) ),
% 35.39/4.95      inference(instantiation,[status(thm)],[c_8]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_43251,plain,
% 35.39/4.95      ( ~ v4_relat_1(sK3,X0)
% 35.39/4.95      | v1_relat_1(k7_relat_1(sK3,sK2))
% 35.39/4.95      | ~ v1_relat_1(sK3) ),
% 35.39/4.95      inference(instantiation,[status(thm)],[c_37278]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_50930,plain,
% 35.39/4.95      ( ~ v4_relat_1(sK3,sK0)
% 35.39/4.95      | v1_relat_1(k7_relat_1(sK3,sK2))
% 35.39/4.95      | ~ v1_relat_1(sK3) ),
% 35.39/4.95      inference(instantiation,[status(thm)],[c_43251]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_50934,plain,
% 35.39/4.95      ( v4_relat_1(sK3,sK0) != iProver_top
% 35.39/4.95      | v1_relat_1(k7_relat_1(sK3,sK2)) = iProver_top
% 35.39/4.95      | v1_relat_1(sK3) != iProver_top ),
% 35.39/4.95      inference(predicate_to_equality,[status(thm)],[c_50930]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_58014,plain,
% 35.39/4.95      ( sK1 = k1_xboole_0
% 35.39/4.95      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 35.39/4.95      inference(global_propositional_subsumption,
% 35.39/4.95                [status(thm)],
% 35.39/4.95                [c_33192,c_34,c_1311,c_1732,c_44271,c_50934]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_58018,plain,
% 35.39/4.95      ( sK1 = k1_xboole_0 ),
% 35.39/4.95      inference(superposition,[status(thm)],[c_3116,c_58014]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_17,plain,
% 35.39/4.95      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
% 35.39/4.95      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 35.39/4.95      | k1_xboole_0 = X0 ),
% 35.39/4.95      inference(cnf_transformation,[],[f80]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_352,plain,
% 35.39/4.95      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 35.39/4.95      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 35.39/4.95      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 35.39/4.95      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 35.39/4.95      | sK2 != X0
% 35.39/4.95      | sK1 != k1_xboole_0
% 35.39/4.95      | k1_xboole_0 = X0 ),
% 35.39/4.95      inference(resolution_lifted,[status(thm)],[c_17,c_26]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_353,plain,
% 35.39/4.95      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 35.39/4.95      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
% 35.39/4.95      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 35.39/4.95      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 35.39/4.95      | sK1 != k1_xboole_0
% 35.39/4.95      | k1_xboole_0 = sK2 ),
% 35.39/4.95      inference(unflattening,[status(thm)],[c_352]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_1097,plain,
% 35.39/4.95      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 35.39/4.95      | sK1 != k1_xboole_0
% 35.39/4.95      | k1_xboole_0 = sK2
% 35.39/4.95      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 35.39/4.95      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
% 35.39/4.95      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 35.39/4.95      inference(predicate_to_equality,[status(thm)],[c_353]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_1,plain,
% 35.39/4.95      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 35.39/4.95      inference(cnf_transformation,[],[f77]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_1118,plain,
% 35.39/4.95      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 35.39/4.95      | sK2 = k1_xboole_0
% 35.39/4.95      | sK1 != k1_xboole_0
% 35.39/4.95      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 35.39/4.95      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 35.39/4.95      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 35.39/4.95      inference(demodulation,[status(thm)],[c_1097,c_1]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_3113,plain,
% 35.39/4.95      ( k7_relat_1(sK3,sK2) != k1_xboole_0
% 35.39/4.95      | sK2 = k1_xboole_0
% 35.39/4.95      | sK1 != k1_xboole_0
% 35.39/4.95      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 35.39/4.95      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 35.39/4.95      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 35.39/4.95      inference(demodulation,[status(thm)],[c_3109,c_1118]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_3,plain,
% 35.39/4.95      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 35.39/4.95      | k1_xboole_0 = X0
% 35.39/4.95      | k1_xboole_0 = X1 ),
% 35.39/4.95      inference(cnf_transformation,[],[f46]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_101,plain,
% 35.39/4.95      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 35.39/4.95      | k1_xboole_0 = k1_xboole_0 ),
% 35.39/4.95      inference(instantiation,[status(thm)],[c_3]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_102,plain,
% 35.39/4.95      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 35.39/4.95      inference(instantiation,[status(thm)],[c_2]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_676,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_1154,plain,
% 35.39/4.95      ( sK2 != X0 | sK2 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 35.39/4.95      inference(instantiation,[status(thm)],[c_676]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_1161,plain,
% 35.39/4.95      ( sK2 != sK2 | sK2 = k1_xboole_0 | k1_xboole_0 != sK2 ),
% 35.39/4.95      inference(instantiation,[status(thm)],[c_1154]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_0,plain,
% 35.39/4.95      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 35.39/4.95      inference(cnf_transformation,[],[f45]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_1170,plain,
% 35.39/4.95      ( ~ r1_tarski(sK2,k1_xboole_0) | k1_xboole_0 = sK2 ),
% 35.39/4.95      inference(instantiation,[status(thm)],[c_0]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_675,plain,( X0 = X0 ),theory(equality) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_1192,plain,
% 35.39/4.95      ( sK2 = sK2 ),
% 35.39/4.95      inference(instantiation,[status(thm)],[c_675]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_677,plain,
% 35.39/4.95      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 35.39/4.95      theory(equality) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_1194,plain,
% 35.39/4.95      ( ~ r1_tarski(X0,X1)
% 35.39/4.95      | r1_tarski(sK2,k1_xboole_0)
% 35.39/4.95      | sK2 != X0
% 35.39/4.95      | k1_xboole_0 != X1 ),
% 35.39/4.95      inference(instantiation,[status(thm)],[c_677]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_1249,plain,
% 35.39/4.95      ( ~ r1_tarski(sK2,X0)
% 35.39/4.95      | r1_tarski(sK2,k1_xboole_0)
% 35.39/4.95      | sK2 != sK2
% 35.39/4.95      | k1_xboole_0 != X0 ),
% 35.39/4.95      inference(instantiation,[status(thm)],[c_1194]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_1368,plain,
% 35.39/4.95      ( ~ r1_tarski(sK2,sK0)
% 35.39/4.95      | r1_tarski(sK2,k1_xboole_0)
% 35.39/4.95      | sK2 != sK2
% 35.39/4.95      | k1_xboole_0 != sK0 ),
% 35.39/4.95      inference(instantiation,[status(thm)],[c_1249]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_1384,plain,
% 35.39/4.95      ( sK0 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK0 ),
% 35.39/4.95      inference(instantiation,[status(thm)],[c_676]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_1385,plain,
% 35.39/4.95      ( sK0 != k1_xboole_0
% 35.39/4.95      | k1_xboole_0 = sK0
% 35.39/4.95      | k1_xboole_0 != k1_xboole_0 ),
% 35.39/4.95      inference(instantiation,[status(thm)],[c_1384]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_18,plain,
% 35.39/4.95      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 35.39/4.95      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 35.39/4.95      | k1_xboole_0 = X1
% 35.39/4.95      | k1_xboole_0 = X0 ),
% 35.39/4.95      inference(cnf_transformation,[],[f81]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_378,plain,
% 35.39/4.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 35.39/4.95      | sK3 != X0
% 35.39/4.95      | sK1 != k1_xboole_0
% 35.39/4.95      | sK0 != X1
% 35.39/4.95      | k1_xboole_0 = X0
% 35.39/4.95      | k1_xboole_0 = X1 ),
% 35.39/4.95      inference(resolution_lifted,[status(thm)],[c_18,c_30]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_379,plain,
% 35.39/4.95      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
% 35.39/4.95      | sK1 != k1_xboole_0
% 35.39/4.95      | k1_xboole_0 = sK3
% 35.39/4.95      | k1_xboole_0 = sK0 ),
% 35.39/4.95      inference(unflattening,[status(thm)],[c_378]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_1096,plain,
% 35.39/4.95      ( sK1 != k1_xboole_0
% 35.39/4.95      | k1_xboole_0 = sK3
% 35.39/4.95      | k1_xboole_0 = sK0
% 35.39/4.95      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
% 35.39/4.95      inference(predicate_to_equality,[status(thm)],[c_379]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_1117,plain,
% 35.39/4.95      ( sK3 = k1_xboole_0
% 35.39/4.95      | sK1 != k1_xboole_0
% 35.39/4.95      | sK0 = k1_xboole_0
% 35.39/4.95      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 35.39/4.95      inference(demodulation,[status(thm)],[c_1096,c_1]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_27,negated_conjecture,
% 35.39/4.95      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 35.39/4.95      inference(cnf_transformation,[],[f75]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_1155,plain,
% 35.39/4.95      ( sK0 != X0 | sK0 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 35.39/4.95      inference(instantiation,[status(thm)],[c_676]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_1163,plain,
% 35.39/4.95      ( sK0 != sK0 | sK0 = k1_xboole_0 | k1_xboole_0 != sK0 ),
% 35.39/4.95      inference(instantiation,[status(thm)],[c_1155]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_1176,plain,
% 35.39/4.95      ( sK0 = sK0 ),
% 35.39/4.95      inference(instantiation,[status(thm)],[c_675]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_1394,plain,
% 35.39/4.95      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 35.39/4.95      inference(instantiation,[status(thm)],[c_676]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_1395,plain,
% 35.39/4.95      ( sK1 != k1_xboole_0
% 35.39/4.95      | k1_xboole_0 = sK1
% 35.39/4.95      | k1_xboole_0 != k1_xboole_0 ),
% 35.39/4.95      inference(instantiation,[status(thm)],[c_1394]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_1463,plain,
% 35.39/4.95      ( sK0 = k1_xboole_0 | sK1 != k1_xboole_0 ),
% 35.39/4.95      inference(global_propositional_subsumption,
% 35.39/4.95                [status(thm)],
% 35.39/4.95                [c_1117,c_27,c_101,c_102,c_1163,c_1176,c_1395]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_1464,plain,
% 35.39/4.95      ( sK1 != k1_xboole_0 | sK0 = k1_xboole_0 ),
% 35.39/4.95      inference(renaming,[status(thm)],[c_1463]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_3337,plain,
% 35.39/4.95      ( sK1 != k1_xboole_0 | sK2 = k1_xboole_0 ),
% 35.39/4.95      inference(global_propositional_subsumption,
% 35.39/4.95                [status(thm)],
% 35.39/4.95                [c_3113,c_28,c_101,c_102,c_1161,c_1170,c_1192,c_1368,
% 35.39/4.95                 c_1385,c_1464]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_3338,plain,
% 35.39/4.95      ( sK2 = k1_xboole_0 | sK1 != k1_xboole_0 ),
% 35.39/4.95      inference(renaming,[status(thm)],[c_3337]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_58357,plain,
% 35.39/4.95      ( sK2 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 35.39/4.95      inference(demodulation,[status(thm)],[c_58018,c_3338]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_58384,plain,
% 35.39/4.95      ( sK2 = k1_xboole_0 ),
% 35.39/4.95      inference(equality_resolution_simp,[status(thm)],[c_58357]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_19,plain,
% 35.39/4.95      ( v1_funct_2(X0,k1_xboole_0,X1)
% 35.39/4.95      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 35.39/4.95      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 35.39/4.95      inference(cnf_transformation,[],[f82]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_398,plain,
% 35.39/4.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 35.39/4.95      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 35.39/4.95      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 35.39/4.95      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 35.39/4.95      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 35.39/4.95      | sK2 != k1_xboole_0
% 35.39/4.95      | sK1 != X1 ),
% 35.39/4.95      inference(resolution_lifted,[status(thm)],[c_19,c_26]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_399,plain,
% 35.39/4.95      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 35.39/4.95      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 35.39/4.95      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 35.39/4.95      | k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
% 35.39/4.95      | sK2 != k1_xboole_0 ),
% 35.39/4.95      inference(unflattening,[status(thm)],[c_398]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_1095,plain,
% 35.39/4.95      ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
% 35.39/4.95      | sK2 != k1_xboole_0
% 35.39/4.95      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 35.39/4.95      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
% 35.39/4.95      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 35.39/4.95      inference(predicate_to_equality,[status(thm)],[c_399]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_1119,plain,
% 35.39/4.95      ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
% 35.39/4.95      | sK2 != k1_xboole_0
% 35.39/4.95      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 35.39/4.95      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 35.39/4.95      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 35.39/4.95      inference(demodulation,[status(thm)],[c_1095,c_2]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_1397,plain,
% 35.39/4.95      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 35.39/4.95      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 35.39/4.95      | ~ v1_funct_1(sK3) ),
% 35.39/4.95      inference(instantiation,[status(thm)],[c_24]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_1398,plain,
% 35.39/4.95      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 35.39/4.95      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) = iProver_top
% 35.39/4.95      | v1_funct_1(sK3) != iProver_top ),
% 35.39/4.95      inference(predicate_to_equality,[status(thm)],[c_1397]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_1458,plain,
% 35.39/4.95      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 35.39/4.95      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 35.39/4.95      | sK2 != k1_xboole_0
% 35.39/4.95      | k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0 ),
% 35.39/4.95      inference(global_propositional_subsumption,
% 35.39/4.95                [status(thm)],
% 35.39/4.95                [c_1119,c_32,c_34,c_1398]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_1459,plain,
% 35.39/4.95      ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
% 35.39/4.95      | sK2 != k1_xboole_0
% 35.39/4.95      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 35.39/4.95      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 35.39/4.95      inference(renaming,[status(thm)],[c_1458]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_3112,plain,
% 35.39/4.95      ( k1_relset_1(k1_xboole_0,sK1,k7_relat_1(sK3,sK2)) != k1_xboole_0
% 35.39/4.95      | sK2 != k1_xboole_0
% 35.39/4.95      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 35.39/4.95      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 35.39/4.95      inference(demodulation,[status(thm)],[c_3109,c_1459]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_58358,plain,
% 35.39/4.95      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,sK2)) != k1_xboole_0
% 35.39/4.95      | sK2 != k1_xboole_0
% 35.39/4.95      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
% 35.39/4.95      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 35.39/4.95      inference(demodulation,[status(thm)],[c_58018,c_3112]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_58383,plain,
% 35.39/4.95      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,sK2)) != k1_xboole_0
% 35.39/4.95      | sK2 != k1_xboole_0
% 35.39/4.95      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 35.39/4.95      inference(demodulation,[status(thm)],[c_58358,c_1]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_58385,plain,
% 35.39/4.95      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0
% 35.39/4.95      | k1_xboole_0 != k1_xboole_0
% 35.39/4.95      | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 35.39/4.95      inference(demodulation,[status(thm)],[c_58384,c_58383]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_58388,plain,
% 35.39/4.95      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0
% 35.39/4.95      | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 35.39/4.95      inference(equality_resolution_simp,[status(thm)],[c_58385]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_1108,plain,
% 35.39/4.95      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 35.39/4.95      | v1_relat_1(X0) = iProver_top ),
% 35.39/4.95      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_1518,plain,
% 35.39/4.95      ( v1_relat_1(sK3) = iProver_top ),
% 35.39/4.95      inference(superposition,[status(thm)],[c_1100,c_1108]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_1115,plain,
% 35.39/4.95      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 35.39/4.95      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_1621,plain,
% 35.39/4.95      ( k1_relat_1(k7_relat_1(X0,k1_xboole_0)) = k1_xboole_0
% 35.39/4.95      | v1_relat_1(X0) != iProver_top ),
% 35.39/4.95      inference(superposition,[status(thm)],[c_1110,c_1115]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_1786,plain,
% 35.39/4.95      ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
% 35.39/4.95      inference(superposition,[status(thm)],[c_1518,c_1621]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_2251,plain,
% 35.39/4.95      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 35.39/4.95      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 35.39/4.95      | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 35.39/4.95      | v1_relat_1(X0) != iProver_top ),
% 35.39/4.95      inference(superposition,[status(thm)],[c_1,c_1105]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_3419,plain,
% 35.39/4.95      ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 35.39/4.95      | r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_xboole_0)),k1_xboole_0) != iProver_top
% 35.39/4.95      | r1_tarski(k1_xboole_0,X0) != iProver_top
% 35.39/4.95      | v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
% 35.39/4.95      inference(superposition,[status(thm)],[c_1786,c_2251]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_2015,plain,
% 35.39/4.95      ( v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = iProver_top
% 35.39/4.95      | v1_relat_1(sK3) != iProver_top ),
% 35.39/4.95      inference(instantiation,[status(thm)],[c_2013]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_7,plain,
% 35.39/4.95      ( ~ v4_relat_1(X0,X1)
% 35.39/4.95      | v4_relat_1(k7_relat_1(X0,X2),X2)
% 35.39/4.95      | ~ v1_relat_1(X0) ),
% 35.39/4.95      inference(cnf_transformation,[],[f52]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_1113,plain,
% 35.39/4.95      ( v4_relat_1(X0,X1) != iProver_top
% 35.39/4.95      | v4_relat_1(k7_relat_1(X0,X2),X2) = iProver_top
% 35.39/4.95      | v1_relat_1(X0) != iProver_top ),
% 35.39/4.95      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_2298,plain,
% 35.39/4.95      ( v4_relat_1(k7_relat_1(sK3,X0),X0) = iProver_top
% 35.39/4.95      | v1_relat_1(sK3) != iProver_top ),
% 35.39/4.95      inference(superposition,[status(thm)],[c_1732,c_1113]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_2403,plain,
% 35.39/4.95      ( v4_relat_1(k7_relat_1(sK3,X0),X0) = iProver_top ),
% 35.39/4.95      inference(global_propositional_subsumption,
% 35.39/4.95                [status(thm)],
% 35.39/4.95                [c_2298,c_34,c_1311]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_9,plain,
% 35.39/4.95      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 35.39/4.95      inference(cnf_transformation,[],[f54]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_1111,plain,
% 35.39/4.95      ( k7_relat_1(X0,X1) = X0
% 35.39/4.95      | v4_relat_1(X0,X1) != iProver_top
% 35.39/4.95      | v1_relat_1(X0) != iProver_top ),
% 35.39/4.95      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_2412,plain,
% 35.39/4.95      ( k7_relat_1(k7_relat_1(sK3,X0),X0) = k7_relat_1(sK3,X0)
% 35.39/4.95      | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
% 35.39/4.95      inference(superposition,[status(thm)],[c_2403,c_1111]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_2796,plain,
% 35.39/4.95      ( k7_relat_1(k7_relat_1(sK3,X0),X0) = k7_relat_1(sK3,X0) ),
% 35.39/4.95      inference(global_propositional_subsumption,
% 35.39/4.95                [status(thm)],
% 35.39/4.95                [c_2412,c_34,c_1311,c_2013]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_2800,plain,
% 35.39/4.95      ( r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X0) = iProver_top
% 35.39/4.95      | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
% 35.39/4.95      inference(superposition,[status(thm)],[c_2796,c_1110]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_2805,plain,
% 35.39/4.95      ( r1_tarski(k1_relat_1(k7_relat_1(sK3,k1_xboole_0)),k1_xboole_0) = iProver_top
% 35.39/4.95      | v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
% 35.39/4.95      inference(instantiation,[status(thm)],[c_2800]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_3638,plain,
% 35.39/4.95      ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 35.39/4.95      | r1_tarski(k1_relat_1(k7_relat_1(sK3,k1_xboole_0)),k1_xboole_0) != iProver_top
% 35.39/4.95      | v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
% 35.39/4.95      inference(instantiation,[status(thm)],[c_3636]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_3996,plain,
% 35.39/4.95      ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 35.39/4.95      inference(global_propositional_subsumption,
% 35.39/4.95                [status(thm)],
% 35.39/4.95                [c_3419,c_34,c_1311,c_2015,c_2805,c_3638]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_1843,plain,
% 35.39/4.95      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
% 35.39/4.95      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 35.39/4.95      inference(superposition,[status(thm)],[c_2,c_1106]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_4005,plain,
% 35.39/4.95      ( k1_relset_1(k1_xboole_0,X0,k7_relat_1(sK3,k1_xboole_0)) = k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) ),
% 35.39/4.95      inference(superposition,[status(thm)],[c_3996,c_1843]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_4008,plain,
% 35.39/4.95      ( k1_relset_1(k1_xboole_0,X0,k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
% 35.39/4.95      inference(light_normalisation,[status(thm)],[c_4005,c_1786]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_58389,plain,
% 35.39/4.95      ( k1_xboole_0 != k1_xboole_0
% 35.39/4.95      | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 35.39/4.95      inference(demodulation,[status(thm)],[c_58388,c_4008]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(c_58390,plain,
% 35.39/4.95      ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 35.39/4.95      inference(equality_resolution_simp,[status(thm)],[c_58389]) ).
% 35.39/4.95  
% 35.39/4.95  cnf(contradiction,plain,
% 35.39/4.95      ( $false ),
% 35.39/4.95      inference(minisat,
% 35.39/4.95                [status(thm)],
% 35.39/4.95                [c_58390,c_3638,c_2805,c_2015,c_1311,c_34]) ).
% 35.39/4.95  
% 35.39/4.95  
% 35.39/4.95  % SZS output end CNFRefutation for theBenchmark.p
% 35.39/4.95  
% 35.39/4.95  ------                               Statistics
% 35.39/4.95  
% 35.39/4.95  ------ General
% 35.39/4.95  
% 35.39/4.95  abstr_ref_over_cycles:                  0
% 35.39/4.95  abstr_ref_under_cycles:                 0
% 35.39/4.95  gc_basic_clause_elim:                   0
% 35.39/4.95  forced_gc_time:                         0
% 35.39/4.95  parsing_time:                           0.011
% 35.39/4.95  unif_index_cands_time:                  0.
% 35.39/4.95  unif_index_add_time:                    0.
% 35.39/4.95  orderings_time:                         0.
% 35.39/4.95  out_proof_time:                         0.046
% 35.39/4.95  total_time:                             4.429
% 35.39/4.95  num_of_symbols:                         50
% 35.39/4.95  num_of_terms:                           95724
% 35.39/4.95  
% 35.39/4.95  ------ Preprocessing
% 35.39/4.95  
% 35.39/4.95  num_of_splits:                          0
% 35.39/4.95  num_of_split_atoms:                     0
% 35.39/4.95  num_of_reused_defs:                     0
% 35.39/4.95  num_eq_ax_congr_red:                    16
% 35.39/4.95  num_of_sem_filtered_clauses:            1
% 35.39/4.95  num_of_subtypes:                        0
% 35.39/4.95  monotx_restored_types:                  0
% 35.39/4.95  sat_num_of_epr_types:                   0
% 35.39/4.95  sat_num_of_non_cyclic_types:            0
% 35.39/4.95  sat_guarded_non_collapsed_types:        0
% 35.39/4.95  num_pure_diseq_elim:                    0
% 35.39/4.95  simp_replaced_by:                       0
% 35.39/4.95  res_preprocessed:                       144
% 35.39/4.95  prep_upred:                             0
% 35.39/4.95  prep_unflattend:                        35
% 35.39/4.95  smt_new_axioms:                         0
% 35.39/4.95  pred_elim_cands:                        5
% 35.39/4.95  pred_elim:                              2
% 35.39/4.95  pred_elim_cl:                           3
% 35.39/4.95  pred_elim_cycles:                       4
% 35.39/4.95  merged_defs:                            0
% 35.39/4.95  merged_defs_ncl:                        0
% 35.39/4.95  bin_hyper_res:                          0
% 35.39/4.95  prep_cycles:                            4
% 35.39/4.95  pred_elim_time:                         0.009
% 35.39/4.95  splitting_time:                         0.
% 35.39/4.95  sem_filter_time:                        0.
% 35.39/4.95  monotx_time:                            0.
% 35.39/4.95  subtype_inf_time:                       0.
% 35.39/4.95  
% 35.39/4.95  ------ Problem properties
% 35.39/4.95  
% 35.39/4.95  clauses:                                29
% 35.39/4.95  conjectures:                            4
% 35.39/4.95  epr:                                    4
% 35.39/4.95  horn:                                   26
% 35.39/4.95  ground:                                 11
% 35.39/4.95  unary:                                  5
% 35.39/4.95  binary:                                 8
% 35.39/4.95  lits:                                   78
% 35.39/4.95  lits_eq:                                28
% 35.39/4.95  fd_pure:                                0
% 35.39/4.95  fd_pseudo:                              0
% 35.39/4.95  fd_cond:                                2
% 35.39/4.95  fd_pseudo_cond:                         0
% 35.39/4.95  ac_symbols:                             0
% 35.39/4.95  
% 35.39/4.95  ------ Propositional Solver
% 35.39/4.95  
% 35.39/4.95  prop_solver_calls:                      49
% 35.39/4.95  prop_fast_solver_calls:                 3498
% 35.39/4.95  smt_solver_calls:                       0
% 35.39/4.95  smt_fast_solver_calls:                  0
% 35.39/4.95  prop_num_of_clauses:                    35247
% 35.39/4.95  prop_preprocess_simplified:             45523
% 35.39/4.95  prop_fo_subsumed:                       158
% 35.39/4.95  prop_solver_time:                       0.
% 35.39/4.95  smt_solver_time:                        0.
% 35.39/4.95  smt_fast_solver_time:                   0.
% 35.39/4.95  prop_fast_solver_time:                  0.
% 35.39/4.95  prop_unsat_core_time:                   0.004
% 35.39/4.95  
% 35.39/4.95  ------ QBF
% 35.39/4.95  
% 35.39/4.95  qbf_q_res:                              0
% 35.39/4.95  qbf_num_tautologies:                    0
% 35.39/4.95  qbf_prep_cycles:                        0
% 35.39/4.95  
% 35.39/4.95  ------ BMC1
% 35.39/4.95  
% 35.39/4.95  bmc1_current_bound:                     -1
% 35.39/4.95  bmc1_last_solved_bound:                 -1
% 35.39/4.95  bmc1_unsat_core_size:                   -1
% 35.39/4.95  bmc1_unsat_core_parents_size:           -1
% 35.39/4.95  bmc1_merge_next_fun:                    0
% 35.39/4.95  bmc1_unsat_core_clauses_time:           0.
% 35.39/4.95  
% 35.39/4.95  ------ Instantiation
% 35.39/4.95  
% 35.39/4.95  inst_num_of_clauses:                    2688
% 35.39/4.95  inst_num_in_passive:                    690
% 35.39/4.95  inst_num_in_active:                     4016
% 35.39/4.95  inst_num_in_unprocessed:                813
% 35.39/4.95  inst_num_of_loops:                      4199
% 35.39/4.95  inst_num_of_learning_restarts:          1
% 35.39/4.95  inst_num_moves_active_passive:          170
% 35.39/4.95  inst_lit_activity:                      0
% 35.39/4.95  inst_lit_activity_moves:                0
% 35.39/4.95  inst_num_tautologies:                   0
% 35.39/4.95  inst_num_prop_implied:                  0
% 35.39/4.95  inst_num_existing_simplified:           0
% 35.39/4.95  inst_num_eq_res_simplified:             0
% 35.39/4.95  inst_num_child_elim:                    0
% 35.39/4.95  inst_num_of_dismatching_blockings:      2892
% 35.39/4.95  inst_num_of_non_proper_insts:           7576
% 35.39/4.95  inst_num_of_duplicates:                 0
% 35.39/4.95  inst_inst_num_from_inst_to_res:         0
% 35.39/4.95  inst_dismatching_checking_time:         0.
% 35.39/4.95  
% 35.39/4.95  ------ Resolution
% 35.39/4.95  
% 35.39/4.95  res_num_of_clauses:                     41
% 35.39/4.95  res_num_in_passive:                     41
% 35.39/4.95  res_num_in_active:                      0
% 35.39/4.95  res_num_of_loops:                       148
% 35.39/4.95  res_forward_subset_subsumed:            234
% 35.39/4.95  res_backward_subset_subsumed:           0
% 35.39/4.95  res_forward_subsumed:                   0
% 35.39/4.95  res_backward_subsumed:                  0
% 35.39/4.95  res_forward_subsumption_resolution:     0
% 35.39/4.95  res_backward_subsumption_resolution:    0
% 35.39/4.95  res_clause_to_clause_subsumption:       26293
% 35.39/4.95  res_orphan_elimination:                 0
% 35.39/4.95  res_tautology_del:                      414
% 35.39/4.95  res_num_eq_res_simplified:              1
% 35.39/4.95  res_num_sel_changes:                    0
% 35.39/4.95  res_moves_from_active_to_pass:          0
% 35.39/4.95  
% 35.39/4.95  ------ Superposition
% 35.39/4.95  
% 35.39/4.95  sup_time_total:                         0.
% 35.39/4.95  sup_time_generating:                    0.
% 35.39/4.95  sup_time_sim_full:                      0.
% 35.39/4.95  sup_time_sim_immed:                     0.
% 35.39/4.95  
% 35.39/4.95  sup_num_of_clauses:                     5424
% 35.39/4.95  sup_num_in_active:                      236
% 35.39/4.95  sup_num_in_passive:                     5188
% 35.39/4.95  sup_num_of_loops:                       838
% 35.39/4.95  sup_fw_superposition:                   7194
% 35.39/4.95  sup_bw_superposition:                   6330
% 35.39/4.95  sup_immediate_simplified:               3297
% 35.39/4.95  sup_given_eliminated:                   9
% 35.39/4.95  comparisons_done:                       0
% 35.39/4.95  comparisons_avoided:                    1089
% 35.39/4.95  
% 35.39/4.95  ------ Simplifications
% 35.39/4.95  
% 35.39/4.95  
% 35.39/4.95  sim_fw_subset_subsumed:                 351
% 35.39/4.95  sim_bw_subset_subsumed:                 1206
% 35.39/4.95  sim_fw_subsumed:                        780
% 35.39/4.95  sim_bw_subsumed:                        497
% 35.39/4.95  sim_fw_subsumption_res:                 0
% 35.39/4.95  sim_bw_subsumption_res:                 0
% 35.39/4.95  sim_tautology_del:                      30
% 35.39/4.95  sim_eq_tautology_del:                   542
% 35.39/4.95  sim_eq_res_simp:                        7
% 35.39/4.95  sim_fw_demodulated:                     1109
% 35.39/4.95  sim_bw_demodulated:                     191
% 35.39/4.95  sim_light_normalised:                   1118
% 35.39/4.95  sim_joinable_taut:                      0
% 35.39/4.95  sim_joinable_simp:                      0
% 35.39/4.95  sim_ac_normalised:                      0
% 35.39/4.95  sim_smt_subsumption:                    0
% 35.39/4.95  
%------------------------------------------------------------------------------
