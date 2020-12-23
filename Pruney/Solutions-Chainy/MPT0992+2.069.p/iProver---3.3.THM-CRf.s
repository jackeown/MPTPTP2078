%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:04:00 EST 2020

% Result     : Theorem 15.48s
% Output     : CNFRefutation 15.48s
% Verified   : 
% Statistics : Number of formulae       :  307 (7776 expanded)
%              Number of clauses        :  233 (3141 expanded)
%              Number of leaves         :   23 (1452 expanded)
%              Depth                    :   33
%              Number of atoms          :  901 (35711 expanded)
%              Number of equality atoms :  559 (10592 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f16,conjecture,(
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

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f17])).

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
    inference(flattening,[],[f36])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f37,f43])).

fof(f73,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f44])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
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
    inference(flattening,[],[f30])).

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
    inference(nnf_transformation,[],[f31])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f71,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f72,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f44])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f40])).

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

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f70,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

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

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f38])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f77,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f76,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f48])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f80,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f65])).

fof(f74,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f44])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

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

fof(f45,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f75,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f44])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_15,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1353,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_27,negated_conjecture,
    ( r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1349,plain,
    ( r1_tarski(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_494,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X0
    | sK1 != X2
    | sK0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_29])).

cnf(c_495,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_494])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_497,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_495,c_28])).

cnf(c_1348,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1354,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2852,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1348,c_1354])).

cnf(c_3206,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_497,c_2852])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1355,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3241,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3206,c_1355])).

cnf(c_33,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1569,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1570,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1569])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_4,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_219,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_4])).

cnf(c_220,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_219])).

cnf(c_278,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_220])).

cnf(c_1586,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_278])).

cnf(c_2002,plain,
    ( ~ r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1586])).

cnf(c_2003,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2002])).

cnf(c_9,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2096,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2097,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2096])).

cnf(c_3246,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | sK1 = k1_xboole_0
    | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3241,c_33,c_1570,c_2003,c_2097])).

cnf(c_3247,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3246])).

cnf(c_3257,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1349,c_3247])).

cnf(c_10,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1357,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3423,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(sK2,sK2) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3257,c_1357])).

cnf(c_3444,plain,
    ( r1_tarski(sK2,sK2) = iProver_top
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3423,c_33,c_1570,c_2003,c_2097])).

cnf(c_3445,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(sK2,sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_3444])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1350,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4488,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1348,c_1350])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1651,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_4429,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_1651])).

cnf(c_4637,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4488,c_30,c_28,c_4429])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1352,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4679,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4637,c_1352])).

cnf(c_31,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_4754,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4679,c_31,c_33])).

cnf(c_13,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_8,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_373,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_13,c_8])).

cnf(c_1345,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_373])).

cnf(c_4765,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) = iProver_top
    | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4754,c_1345])).

cnf(c_1359,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4761,plain,
    ( r1_tarski(k7_relat_1(sK3,X0),k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4754,c_1359])).

cnf(c_1346,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_278])).

cnf(c_4853,plain,
    ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4761,c_1346])).

cnf(c_4891,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4765,c_2097,c_4853])).

cnf(c_4202,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | r1_tarski(k1_relat_1(X2),X0) != iProver_top
    | r1_tarski(k2_relat_1(X2),X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1353,c_1354])).

cnf(c_46839,plain,
    ( k1_relset_1(X0,X1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
    | sK1 = k1_xboole_0
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3257,c_4202])).

cnf(c_3,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_97,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_98,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1358,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1899,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_1358])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_426,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK3 != X0
    | sK1 != k1_xboole_0
    | sK0 != X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_29])).

cnf(c_427,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0 ),
    inference(unflattening,[status(thm)],[c_426])).

cnf(c_1343,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_427])).

cnf(c_1431,plain,
    ( sK3 = k1_xboole_0
    | sK1 != k1_xboole_0
    | sK0 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1343,c_1])).

cnf(c_26,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_775,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1603,plain,
    ( sK0 != X0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_775])).

cnf(c_1806,plain,
    ( sK0 != sK0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1603])).

cnf(c_774,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1807,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_774])).

cnf(c_1854,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_775])).

cnf(c_1855,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1854])).

cnf(c_2021,plain,
    ( sK0 = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1431,c_26,c_97,c_98,c_1806,c_1807,c_1855])).

cnf(c_2022,plain,
    ( sK1 != k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_2021])).

cnf(c_11,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1356,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1361,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2092,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1356,c_1361])).

cnf(c_2193,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2092,c_1899])).

cnf(c_2197,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2193,c_1356])).

cnf(c_776,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3569,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK0,k1_xboole_0)
    | sK0 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_776])).

cnf(c_3570,plain,
    ( sK0 != X0
    | k1_xboole_0 != X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(sK0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3569])).

cnf(c_3572,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3570])).

cnf(c_1769,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1348,c_1345])).

cnf(c_4200,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_1353])).

cnf(c_5427,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1769,c_4200])).

cnf(c_5604,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5427,c_33,c_1570,c_2003,c_2097])).

cnf(c_5605,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5604])).

cnf(c_5610,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3206,c_5605])).

cnf(c_3499,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) != iProver_top
    | m1_subset_1(k2_partfun1(X1,k1_xboole_0,X0,X2),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_1352])).

cnf(c_3543,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(k2_partfun1(X1,k1_xboole_0,X0,X2),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3499,c_1])).

cnf(c_4490,plain,
    ( k2_partfun1(k1_xboole_0,X0,X1,X2) = k7_relat_1(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_1350])).

cnf(c_5120,plain,
    ( k2_partfun1(k1_xboole_0,X0,k2_partfun1(X1,k1_xboole_0,X2,X3),X4) = k7_relat_1(k2_partfun1(X1,k1_xboole_0,X2,X3),X4)
    | m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(k2_partfun1(X1,k1_xboole_0,X2,X3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3543,c_4490])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1351,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2761,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_partfun1(X1,k1_xboole_0,X0,X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_1351])).

cnf(c_35150,plain,
    ( k2_partfun1(k1_xboole_0,X0,k2_partfun1(X1,k1_xboole_0,X2,X3),X4) = k7_relat_1(k2_partfun1(X1,k1_xboole_0,X2,X3),X4)
    | m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5120,c_2761])).

cnf(c_35153,plain,
    ( k2_partfun1(k1_xboole_0,X0,k2_partfun1(X1,k1_xboole_0,sK3,X2),X3) = k7_relat_1(k2_partfun1(X1,k1_xboole_0,sK3,X2),X3)
    | sK1 = k1_xboole_0
    | r1_tarski(sK0,k1_xboole_0) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5610,c_35150])).

cnf(c_25,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_505,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != sK3
    | sK2 != sK0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_29])).

cnf(c_1604,plain,
    ( sK2 != X0
    | sK2 = sK0
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_775])).

cnf(c_1605,plain,
    ( sK2 = sK0
    | sK2 != k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1604])).

cnf(c_1679,plain,
    ( ~ r1_tarski(sK3,k1_xboole_0)
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1689,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1636,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(sK2,sK0)
    | X0 != sK2
    | X1 != sK0 ),
    inference(instantiation,[status(thm)],[c_776])).

cnf(c_1694,plain,
    ( r1_tarski(sK2,X0)
    | ~ r1_tarski(sK2,sK0)
    | X0 != sK0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1636])).

cnf(c_1697,plain,
    ( ~ r1_tarski(sK2,sK0)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != sK2
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1694])).

cnf(c_1695,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_774])).

cnf(c_1706,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_774])).

cnf(c_1800,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_774])).

cnf(c_1602,plain,
    ( sK2 != X0
    | sK2 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_775])).

cnf(c_1805,plain,
    ( sK2 != sK2
    | sK2 = k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_1602])).

cnf(c_1840,plain,
    ( ~ r1_tarski(sK0,k1_xboole_0)
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1843,plain,
    ( k1_xboole_0 = sK0
    | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1840])).

cnf(c_1901,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1899])).

cnf(c_1671,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))
    | X1 != k2_zfmisc_1(sK0,sK1)
    | X0 != sK3 ),
    inference(instantiation,[status(thm)],[c_776])).

cnf(c_1913,plain,
    ( r1_tarski(sK3,X0)
    | ~ r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))
    | X0 != k2_zfmisc_1(sK0,sK1)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1671])).

cnf(c_1915,plain,
    ( ~ r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))
    | r1_tarski(sK3,k1_xboole_0)
    | sK3 != sK3
    | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_1913])).

cnf(c_1983,plain,
    ( X0 != X1
    | X0 = k2_zfmisc_1(X2,X3)
    | k2_zfmisc_1(X2,X3) != X1 ),
    inference(instantiation,[status(thm)],[c_775])).

cnf(c_1984,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1983])).

cnf(c_1631,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(k2_partfun1(X0,X1,sK3,X2))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_1860,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1631])).

cnf(c_2031,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1860])).

cnf(c_2198,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2197])).

cnf(c_2328,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),X0) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2193,c_1357])).

cnf(c_2593,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2328,c_1899])).

cnf(c_2600,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2593,c_1361])).

cnf(c_1919,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_775])).

cnf(c_2724,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1919])).

cnf(c_2725,plain,
    ( sK3 != sK3
    | sK3 = k1_xboole_0
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_2724])).

cnf(c_3571,plain,
    ( r1_tarski(sK0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | sK0 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3569])).

cnf(c_4431,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(sK0,sK1,sK3,k1_xboole_0) = k7_relat_1(sK3,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4429])).

cnf(c_777,plain,
    ( X0 != X1
    | X2 != X3
    | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
    theory(equality)).

cnf(c_4885,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(X0,X1)
    | sK1 != X1
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_777])).

cnf(c_4887,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | sK1 != k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4885])).

cnf(c_5616,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(sK3,k1_xboole_0) = iProver_top
    | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5610,c_1359])).

cnf(c_5673,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | ~ r1_tarski(sK0,k1_xboole_0)
    | sK1 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5616])).

cnf(c_1943,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_774])).

cnf(c_6381,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) = k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_1943])).

cnf(c_5428,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),k1_xboole_0) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4891,c_4200])).

cnf(c_7436,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),k1_xboole_0) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5428,c_2097,c_4853])).

cnf(c_7437,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_7436])).

cnf(c_7444,plain,
    ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1357,c_7437])).

cnf(c_7787,plain,
    ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7444,c_33,c_1570,c_2003,c_2097])).

cnf(c_7792,plain,
    ( r1_tarski(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_7787,c_1359])).

cnf(c_7823,plain,
    ( r1_tarski(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7792])).

cnf(c_7913,plain,
    ( k7_relat_1(sK3,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7792,c_1361])).

cnf(c_7951,plain,
    ( r1_tarski(k2_relat_1(k1_xboole_0),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_7913,c_4891])).

cnf(c_7991,plain,
    ( r1_tarski(k2_relat_1(k1_xboole_0),sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7951])).

cnf(c_5752,plain,
    ( X0 != X1
    | X0 = k2_zfmisc_1(sK0,sK1)
    | k2_zfmisc_1(sK0,sK1) != X1 ),
    inference(instantiation,[status(thm)],[c_1983])).

cnf(c_8690,plain,
    ( X0 != k2_zfmisc_1(X1,X2)
    | X0 = k2_zfmisc_1(sK0,sK1)
    | k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X1,X2) ),
    inference(instantiation,[status(thm)],[c_5752])).

cnf(c_8692,plain,
    ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_8690])).

cnf(c_4419,plain,
    ( X0 != X1
    | k2_partfun1(sK0,sK1,sK3,X2) != X1
    | k2_partfun1(sK0,sK1,sK3,X2) = X0 ),
    inference(instantiation,[status(thm)],[c_775])).

cnf(c_8806,plain,
    ( X0 != k7_relat_1(sK3,X1)
    | k2_partfun1(sK0,sK1,sK3,X1) = X0
    | k2_partfun1(sK0,sK1,sK3,X1) != k7_relat_1(sK3,X1) ),
    inference(instantiation,[status(thm)],[c_4419])).

cnf(c_8807,plain,
    ( k2_partfun1(sK0,sK1,sK3,k1_xboole_0) != k7_relat_1(sK3,k1_xboole_0)
    | k2_partfun1(sK0,sK1,sK3,k1_xboole_0) = k1_xboole_0
    | k1_xboole_0 != k7_relat_1(sK3,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_8806])).

cnf(c_11804,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k1_relat_1(X0),sK2)
    | ~ r1_tarski(k2_relat_1(X0),sK1)
    | ~ v1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_11806,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k1_relat_1(k1_xboole_0),sK2)
    | ~ r1_tarski(k2_relat_1(k1_xboole_0),sK1)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_11804])).

cnf(c_13058,plain,
    ( ~ r1_tarski(k7_relat_1(sK3,X0),k1_xboole_0)
    | k1_xboole_0 = k7_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_13060,plain,
    ( ~ r1_tarski(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0)
    | k1_xboole_0 = k7_relat_1(sK3,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_13058])).

cnf(c_779,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2166,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | X0 != X2
    | X1 != k1_zfmisc_1(X3) ),
    inference(instantiation,[status(thm)],[c_779])).

cnf(c_4173,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(X2,k1_zfmisc_1(X1))
    | X2 != X0
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_2166])).

cnf(c_8492,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_4173])).

cnf(c_17176,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k2_partfun1(sK0,sK1,sK3,X0)
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_8492])).

cnf(c_17182,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k2_partfun1(sK0,sK1,sK3,k1_xboole_0)
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_17176])).

cnf(c_783,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | X6 != X7
    | k2_partfun1(X0,X2,X4,X6) = k2_partfun1(X1,X3,X5,X7) ),
    theory(equality)).

cnf(c_2271,plain,
    ( X0 != X1
    | X2 != sK3
    | X3 != sK1
    | X4 != sK0
    | k2_partfun1(X4,X3,X2,X0) = k2_partfun1(sK0,sK1,sK3,X1) ),
    inference(instantiation,[status(thm)],[c_783])).

cnf(c_4704,plain,
    ( X0 != X1
    | X2 != sK1
    | X3 != sK0
    | k2_partfun1(X3,X2,sK3,X0) = k2_partfun1(sK0,sK1,sK3,X1)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2271])).

cnf(c_6977,plain,
    ( X0 != X1
    | X2 != sK0
    | k2_partfun1(X2,sK1,sK3,X0) = k2_partfun1(sK0,sK1,sK3,X1)
    | sK3 != sK3
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_4704])).

cnf(c_22390,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) = k2_partfun1(sK0,sK1,sK3,X0)
    | sK2 != X0
    | sK3 != sK3
    | sK1 != sK1
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_6977])).

cnf(c_22394,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) = k2_partfun1(sK0,sK1,sK3,k1_xboole_0)
    | sK2 != k1_xboole_0
    | sK3 != sK3
    | sK1 != sK1
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_22390])).

cnf(c_8523,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_partfun1(sK0,sK1,sK3,X3) != X0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_4173])).

cnf(c_31705,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | k2_partfun1(sK0,sK1,sK3,X1) != X0
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_8523])).

cnf(c_31707,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | k2_partfun1(sK0,sK1,sK3,k1_xboole_0) != k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_31705])).

cnf(c_32681,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(X2),sK2)
    | k1_relat_1(X2) != X0
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_776])).

cnf(c_32683,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),sK2)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_relat_1(k1_xboole_0) != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_32681])).

cnf(c_2268,plain,
    ( X0 != X1
    | X0 = k2_partfun1(sK0,sK1,sK3,X2)
    | k2_partfun1(sK0,sK1,sK3,X2) != X1 ),
    inference(instantiation,[status(thm)],[c_775])).

cnf(c_35476,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) != X1
    | sK3 != X1
    | sK3 = k2_partfun1(sK0,sK1,sK3,X0) ),
    inference(instantiation,[status(thm)],[c_2268])).

cnf(c_35517,plain,
    ( k2_partfun1(sK0,sK1,sK3,k1_xboole_0) != k1_xboole_0
    | sK3 = k2_partfun1(sK0,sK1,sK3,k1_xboole_0)
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_35476])).

cnf(c_1685,plain,
    ( X0 != X1
    | X0 = sK3
    | sK3 != X1 ),
    inference(instantiation,[status(thm)],[c_775])).

cnf(c_12760,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k2_partfun1(sK0,sK1,sK3,sK2) = sK3
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_1685])).

cnf(c_35509,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k2_partfun1(sK0,sK1,sK3,X0)
    | k2_partfun1(sK0,sK1,sK3,sK2) = sK3
    | sK3 != k2_partfun1(sK0,sK1,sK3,X0) ),
    inference(instantiation,[status(thm)],[c_12760])).

cnf(c_35533,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k2_partfun1(sK0,sK1,sK3,k1_xboole_0)
    | k2_partfun1(sK0,sK1,sK3,sK2) = sK3
    | sK3 != k2_partfun1(sK0,sK1,sK3,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_35509])).

cnf(c_35940,plain,
    ( r1_tarski(sK0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_35153,c_30,c_28,c_27,c_97,c_98,c_505,c_1569,c_1605,c_1679,c_1689,c_1697,c_1695,c_1706,c_1800,c_1805,c_1806,c_1807,c_1843,c_1901,c_1915,c_1984,c_2031,c_2198,c_2600,c_2725,c_3571,c_4431,c_4887,c_5673,c_6381,c_7823,c_7991,c_8692,c_8807,c_11806,c_13060,c_17182,c_22394,c_31707,c_32683,c_35517,c_35533])).

cnf(c_48459,plain,
    ( k1_relset_1(X0,X1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_46839,c_30,c_28,c_27,c_26,c_97,c_98,c_505,c_1569,c_1605,c_1679,c_1689,c_1697,c_1695,c_1706,c_1800,c_1805,c_1806,c_1807,c_1855,c_1901,c_1915,c_1984,c_2031,c_2198,c_2600,c_2725,c_3571,c_4431,c_4887,c_5673,c_6381,c_7823,c_7991,c_8692,c_8807,c_11806,c_13060,c_17182,c_22394,c_31707,c_32683,c_35517,c_35533])).

cnf(c_7367,plain,
    ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4853,c_2097])).

cnf(c_48469,plain,
    ( k1_relset_1(X0,X1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_48459,c_7367])).

cnf(c_48476,plain,
    ( k1_relset_1(X0,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4891,c_48469])).

cnf(c_63014,plain,
    ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3445,c_48476])).

cnf(c_63107,plain,
    ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_63014,c_30,c_28,c_27,c_26,c_97,c_98,c_505,c_1569,c_1605,c_1679,c_1689,c_1697,c_1695,c_1706,c_1800,c_1805,c_1806,c_1807,c_1855,c_1901,c_1915,c_1984,c_2031,c_2198,c_2600,c_2725,c_3571,c_4431,c_4887,c_5673,c_6381,c_7823,c_7991,c_8692,c_8807,c_11806,c_13060,c_17182,c_22394,c_31707,c_32683,c_35517,c_35533])).

cnf(c_19,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_478,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_relset_1(X1,X2,X0) != X1
    | sK2 != X1
    | sK1 != X2
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_25])).

cnf(c_479,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_478])).

cnf(c_1340,plain,
    ( k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | k1_xboole_0 = sK1
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_479])).

cnf(c_4643,plain,
    ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) != sK2
    | sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4637,c_1340])).

cnf(c_2760,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1348,c_1351])).

cnf(c_1861,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1860])).

cnf(c_3209,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2760,c_31,c_33,c_1861])).

cnf(c_4644,plain,
    ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4637,c_3209])).

cnf(c_4651,plain,
    ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) != sK2
    | sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4643,c_4644])).

cnf(c_63110,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_63107,c_4651])).

cnf(c_65217,plain,
    ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_63110,c_30,c_28,c_27,c_26,c_97,c_98,c_505,c_1569,c_1605,c_1679,c_1689,c_1697,c_1695,c_1706,c_1800,c_1805,c_1806,c_1807,c_1855,c_1901,c_1915,c_1984,c_2031,c_2198,c_2600,c_2725,c_3257,c_3571,c_4431,c_4887,c_5673,c_6381,c_7823,c_7991,c_8692,c_8807,c_11806,c_13060,c_17182,c_22394,c_31707,c_32683,c_35517,c_35533])).

cnf(c_65223,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) != iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1353,c_65217])).

cnf(c_2301,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1348,c_1359])).

cnf(c_2356,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2301,c_1346])).

cnf(c_2383,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2356,c_33,c_1570,c_2003,c_2097])).

cnf(c_2203,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1356,c_1346])).

cnf(c_3424,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK2) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3257,c_1355])).

cnf(c_3491,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2203,c_3424])).

cnf(c_3977,plain,
    ( r1_tarski(X0,sK2) != iProver_top
    | sK1 = k1_xboole_0
    | k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3491,c_33,c_1570,c_2003,c_2097])).

cnf(c_3978,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_3977])).

cnf(c_3986,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),k1_relat_1(k7_relat_1(X0,sK2)))) = k1_relat_1(k7_relat_1(X0,sK2))
    | sK1 = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1357,c_3978])).

cnf(c_11634,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),k1_relat_1(k7_relat_1(sK3,sK2)))) = k1_relat_1(k7_relat_1(sK3,sK2))
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2383,c_3986])).

cnf(c_11695,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3257,c_11634])).

cnf(c_11915,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) = iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11695,c_1357])).

cnf(c_12129,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_11915,c_7367])).

cnf(c_66160,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_65223,c_30,c_28,c_27,c_26,c_97,c_98,c_505,c_1569,c_1605,c_1679,c_1689,c_1697,c_1695,c_1706,c_1800,c_1805,c_1806,c_1807,c_1855,c_1901,c_1915,c_1984,c_2031,c_2198,c_2600,c_2725,c_3571,c_4431,c_4887,c_5673,c_6381,c_7823,c_7991,c_8692,c_8807,c_11806,c_12129,c_13060,c_17182,c_22394,c_31707,c_32683,c_35517,c_35533])).

cnf(c_66166,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_66160,c_7367,c_4891])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:19:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 15.48/2.53  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.48/2.53  
% 15.48/2.53  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.48/2.53  
% 15.48/2.53  ------  iProver source info
% 15.48/2.53  
% 15.48/2.53  git: date: 2020-06-30 10:37:57 +0100
% 15.48/2.53  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.48/2.53  git: non_committed_changes: false
% 15.48/2.53  git: last_make_outside_of_git: false
% 15.48/2.53  
% 15.48/2.53  ------ 
% 15.48/2.53  
% 15.48/2.53  ------ Input Options
% 15.48/2.53  
% 15.48/2.53  --out_options                           all
% 15.48/2.53  --tptp_safe_out                         true
% 15.48/2.53  --problem_path                          ""
% 15.48/2.53  --include_path                          ""
% 15.48/2.53  --clausifier                            res/vclausify_rel
% 15.48/2.53  --clausifier_options                    --mode clausify
% 15.48/2.53  --stdin                                 false
% 15.48/2.53  --stats_out                             all
% 15.48/2.53  
% 15.48/2.53  ------ General Options
% 15.48/2.53  
% 15.48/2.53  --fof                                   false
% 15.48/2.53  --time_out_real                         305.
% 15.48/2.53  --time_out_virtual                      -1.
% 15.48/2.53  --symbol_type_check                     false
% 15.48/2.53  --clausify_out                          false
% 15.48/2.53  --sig_cnt_out                           false
% 15.48/2.53  --trig_cnt_out                          false
% 15.48/2.53  --trig_cnt_out_tolerance                1.
% 15.48/2.53  --trig_cnt_out_sk_spl                   false
% 15.48/2.53  --abstr_cl_out                          false
% 15.48/2.53  
% 15.48/2.53  ------ Global Options
% 15.48/2.53  
% 15.48/2.53  --schedule                              default
% 15.48/2.53  --add_important_lit                     false
% 15.48/2.53  --prop_solver_per_cl                    1000
% 15.48/2.53  --min_unsat_core                        false
% 15.48/2.53  --soft_assumptions                      false
% 15.48/2.53  --soft_lemma_size                       3
% 15.48/2.53  --prop_impl_unit_size                   0
% 15.48/2.53  --prop_impl_unit                        []
% 15.48/2.53  --share_sel_clauses                     true
% 15.48/2.53  --reset_solvers                         false
% 15.48/2.53  --bc_imp_inh                            [conj_cone]
% 15.48/2.53  --conj_cone_tolerance                   3.
% 15.48/2.53  --extra_neg_conj                        none
% 15.48/2.53  --large_theory_mode                     true
% 15.48/2.53  --prolific_symb_bound                   200
% 15.48/2.53  --lt_threshold                          2000
% 15.48/2.53  --clause_weak_htbl                      true
% 15.48/2.53  --gc_record_bc_elim                     false
% 15.48/2.53  
% 15.48/2.53  ------ Preprocessing Options
% 15.48/2.53  
% 15.48/2.53  --preprocessing_flag                    true
% 15.48/2.53  --time_out_prep_mult                    0.1
% 15.48/2.53  --splitting_mode                        input
% 15.48/2.53  --splitting_grd                         true
% 15.48/2.53  --splitting_cvd                         false
% 15.48/2.53  --splitting_cvd_svl                     false
% 15.48/2.53  --splitting_nvd                         32
% 15.48/2.53  --sub_typing                            true
% 15.48/2.53  --prep_gs_sim                           true
% 15.48/2.53  --prep_unflatten                        true
% 15.48/2.53  --prep_res_sim                          true
% 15.48/2.53  --prep_upred                            true
% 15.48/2.53  --prep_sem_filter                       exhaustive
% 15.48/2.53  --prep_sem_filter_out                   false
% 15.48/2.53  --pred_elim                             true
% 15.48/2.53  --res_sim_input                         true
% 15.48/2.53  --eq_ax_congr_red                       true
% 15.48/2.53  --pure_diseq_elim                       true
% 15.48/2.53  --brand_transform                       false
% 15.48/2.53  --non_eq_to_eq                          false
% 15.48/2.53  --prep_def_merge                        true
% 15.48/2.53  --prep_def_merge_prop_impl              false
% 15.48/2.53  --prep_def_merge_mbd                    true
% 15.48/2.53  --prep_def_merge_tr_red                 false
% 15.48/2.53  --prep_def_merge_tr_cl                  false
% 15.48/2.53  --smt_preprocessing                     true
% 15.48/2.53  --smt_ac_axioms                         fast
% 15.48/2.53  --preprocessed_out                      false
% 15.48/2.53  --preprocessed_stats                    false
% 15.48/2.53  
% 15.48/2.53  ------ Abstraction refinement Options
% 15.48/2.53  
% 15.48/2.53  --abstr_ref                             []
% 15.48/2.53  --abstr_ref_prep                        false
% 15.48/2.53  --abstr_ref_until_sat                   false
% 15.48/2.53  --abstr_ref_sig_restrict                funpre
% 15.48/2.53  --abstr_ref_af_restrict_to_split_sk     false
% 15.48/2.53  --abstr_ref_under                       []
% 15.48/2.53  
% 15.48/2.53  ------ SAT Options
% 15.48/2.53  
% 15.48/2.53  --sat_mode                              false
% 15.48/2.53  --sat_fm_restart_options                ""
% 15.48/2.53  --sat_gr_def                            false
% 15.48/2.53  --sat_epr_types                         true
% 15.48/2.53  --sat_non_cyclic_types                  false
% 15.48/2.53  --sat_finite_models                     false
% 15.48/2.53  --sat_fm_lemmas                         false
% 15.48/2.53  --sat_fm_prep                           false
% 15.48/2.53  --sat_fm_uc_incr                        true
% 15.48/2.53  --sat_out_model                         small
% 15.48/2.53  --sat_out_clauses                       false
% 15.48/2.53  
% 15.48/2.53  ------ QBF Options
% 15.48/2.53  
% 15.48/2.53  --qbf_mode                              false
% 15.48/2.53  --qbf_elim_univ                         false
% 15.48/2.53  --qbf_dom_inst                          none
% 15.48/2.53  --qbf_dom_pre_inst                      false
% 15.48/2.53  --qbf_sk_in                             false
% 15.48/2.53  --qbf_pred_elim                         true
% 15.48/2.53  --qbf_split                             512
% 15.48/2.53  
% 15.48/2.53  ------ BMC1 Options
% 15.48/2.53  
% 15.48/2.53  --bmc1_incremental                      false
% 15.48/2.53  --bmc1_axioms                           reachable_all
% 15.48/2.53  --bmc1_min_bound                        0
% 15.48/2.53  --bmc1_max_bound                        -1
% 15.48/2.53  --bmc1_max_bound_default                -1
% 15.48/2.53  --bmc1_symbol_reachability              true
% 15.48/2.53  --bmc1_property_lemmas                  false
% 15.48/2.53  --bmc1_k_induction                      false
% 15.48/2.53  --bmc1_non_equiv_states                 false
% 15.48/2.53  --bmc1_deadlock                         false
% 15.48/2.53  --bmc1_ucm                              false
% 15.48/2.53  --bmc1_add_unsat_core                   none
% 15.48/2.54  --bmc1_unsat_core_children              false
% 15.48/2.54  --bmc1_unsat_core_extrapolate_axioms    false
% 15.48/2.54  --bmc1_out_stat                         full
% 15.48/2.54  --bmc1_ground_init                      false
% 15.48/2.54  --bmc1_pre_inst_next_state              false
% 15.48/2.54  --bmc1_pre_inst_state                   false
% 15.48/2.54  --bmc1_pre_inst_reach_state             false
% 15.48/2.54  --bmc1_out_unsat_core                   false
% 15.48/2.54  --bmc1_aig_witness_out                  false
% 15.48/2.54  --bmc1_verbose                          false
% 15.48/2.54  --bmc1_dump_clauses_tptp                false
% 15.48/2.54  --bmc1_dump_unsat_core_tptp             false
% 15.48/2.54  --bmc1_dump_file                        -
% 15.48/2.54  --bmc1_ucm_expand_uc_limit              128
% 15.48/2.54  --bmc1_ucm_n_expand_iterations          6
% 15.48/2.54  --bmc1_ucm_extend_mode                  1
% 15.48/2.54  --bmc1_ucm_init_mode                    2
% 15.48/2.54  --bmc1_ucm_cone_mode                    none
% 15.48/2.54  --bmc1_ucm_reduced_relation_type        0
% 15.48/2.54  --bmc1_ucm_relax_model                  4
% 15.48/2.54  --bmc1_ucm_full_tr_after_sat            true
% 15.48/2.54  --bmc1_ucm_expand_neg_assumptions       false
% 15.48/2.54  --bmc1_ucm_layered_model                none
% 15.48/2.54  --bmc1_ucm_max_lemma_size               10
% 15.48/2.54  
% 15.48/2.54  ------ AIG Options
% 15.48/2.54  
% 15.48/2.54  --aig_mode                              false
% 15.48/2.54  
% 15.48/2.54  ------ Instantiation Options
% 15.48/2.54  
% 15.48/2.54  --instantiation_flag                    true
% 15.48/2.54  --inst_sos_flag                         false
% 15.48/2.54  --inst_sos_phase                        true
% 15.48/2.54  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.48/2.54  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.48/2.54  --inst_lit_sel_side                     num_symb
% 15.48/2.54  --inst_solver_per_active                1400
% 15.48/2.54  --inst_solver_calls_frac                1.
% 15.48/2.54  --inst_passive_queue_type               priority_queues
% 15.48/2.54  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.48/2.54  --inst_passive_queues_freq              [25;2]
% 15.48/2.54  --inst_dismatching                      true
% 15.48/2.54  --inst_eager_unprocessed_to_passive     true
% 15.48/2.54  --inst_prop_sim_given                   true
% 15.48/2.54  --inst_prop_sim_new                     false
% 15.48/2.54  --inst_subs_new                         false
% 15.48/2.54  --inst_eq_res_simp                      false
% 15.48/2.54  --inst_subs_given                       false
% 15.48/2.54  --inst_orphan_elimination               true
% 15.48/2.54  --inst_learning_loop_flag               true
% 15.48/2.54  --inst_learning_start                   3000
% 15.48/2.54  --inst_learning_factor                  2
% 15.48/2.54  --inst_start_prop_sim_after_learn       3
% 15.48/2.54  --inst_sel_renew                        solver
% 15.48/2.54  --inst_lit_activity_flag                true
% 15.48/2.54  --inst_restr_to_given                   false
% 15.48/2.54  --inst_activity_threshold               500
% 15.48/2.54  --inst_out_proof                        true
% 15.48/2.54  
% 15.48/2.54  ------ Resolution Options
% 15.48/2.54  
% 15.48/2.54  --resolution_flag                       true
% 15.48/2.54  --res_lit_sel                           adaptive
% 15.48/2.54  --res_lit_sel_side                      none
% 15.48/2.54  --res_ordering                          kbo
% 15.48/2.54  --res_to_prop_solver                    active
% 15.48/2.54  --res_prop_simpl_new                    false
% 15.48/2.54  --res_prop_simpl_given                  true
% 15.48/2.54  --res_passive_queue_type                priority_queues
% 15.48/2.54  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.48/2.54  --res_passive_queues_freq               [15;5]
% 15.48/2.54  --res_forward_subs                      full
% 15.48/2.54  --res_backward_subs                     full
% 15.48/2.54  --res_forward_subs_resolution           true
% 15.48/2.54  --res_backward_subs_resolution          true
% 15.48/2.54  --res_orphan_elimination                true
% 15.48/2.54  --res_time_limit                        2.
% 15.48/2.54  --res_out_proof                         true
% 15.48/2.54  
% 15.48/2.54  ------ Superposition Options
% 15.48/2.54  
% 15.48/2.54  --superposition_flag                    true
% 15.48/2.54  --sup_passive_queue_type                priority_queues
% 15.48/2.54  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.48/2.54  --sup_passive_queues_freq               [8;1;4]
% 15.48/2.54  --demod_completeness_check              fast
% 15.48/2.54  --demod_use_ground                      true
% 15.48/2.54  --sup_to_prop_solver                    passive
% 15.48/2.54  --sup_prop_simpl_new                    true
% 15.48/2.54  --sup_prop_simpl_given                  true
% 15.48/2.54  --sup_fun_splitting                     false
% 15.48/2.54  --sup_smt_interval                      50000
% 15.48/2.54  
% 15.48/2.54  ------ Superposition Simplification Setup
% 15.48/2.54  
% 15.48/2.54  --sup_indices_passive                   []
% 15.48/2.54  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.48/2.54  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.48/2.54  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.48/2.54  --sup_full_triv                         [TrivRules;PropSubs]
% 15.48/2.54  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.48/2.54  --sup_full_bw                           [BwDemod]
% 15.48/2.54  --sup_immed_triv                        [TrivRules]
% 15.48/2.54  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.48/2.54  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.48/2.54  --sup_immed_bw_main                     []
% 15.48/2.54  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.48/2.54  --sup_input_triv                        [Unflattening;TrivRules]
% 15.48/2.54  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.48/2.54  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.48/2.54  
% 15.48/2.54  ------ Combination Options
% 15.48/2.54  
% 15.48/2.54  --comb_res_mult                         3
% 15.48/2.54  --comb_sup_mult                         2
% 15.48/2.54  --comb_inst_mult                        10
% 15.48/2.54  
% 15.48/2.54  ------ Debug Options
% 15.48/2.54  
% 15.48/2.54  --dbg_backtrace                         false
% 15.48/2.54  --dbg_dump_prop_clauses                 false
% 15.48/2.54  --dbg_dump_prop_clauses_file            -
% 15.48/2.54  --dbg_out_stat                          false
% 15.48/2.54  ------ Parsing...
% 15.48/2.54  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.48/2.54  
% 15.48/2.54  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 15.48/2.54  
% 15.48/2.54  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.48/2.54  
% 15.48/2.54  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.48/2.54  ------ Proving...
% 15.48/2.54  ------ Problem Properties 
% 15.48/2.54  
% 15.48/2.54  
% 15.48/2.54  clauses                                 28
% 15.48/2.54  conjectures                             4
% 15.48/2.54  EPR                                     5
% 15.48/2.54  Horn                                    25
% 15.48/2.54  unary                                   6
% 15.48/2.54  binary                                  8
% 15.48/2.54  lits                                    73
% 15.48/2.54  lits eq                                 27
% 15.48/2.54  fd_pure                                 0
% 15.48/2.54  fd_pseudo                               0
% 15.48/2.54  fd_cond                                 2
% 15.48/2.54  fd_pseudo_cond                          0
% 15.48/2.54  AC symbols                              0
% 15.48/2.54  
% 15.48/2.54  ------ Schedule dynamic 5 is on 
% 15.48/2.54  
% 15.48/2.54  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 15.48/2.54  
% 15.48/2.54  
% 15.48/2.54  ------ 
% 15.48/2.54  Current options:
% 15.48/2.54  ------ 
% 15.48/2.54  
% 15.48/2.54  ------ Input Options
% 15.48/2.54  
% 15.48/2.54  --out_options                           all
% 15.48/2.54  --tptp_safe_out                         true
% 15.48/2.54  --problem_path                          ""
% 15.48/2.54  --include_path                          ""
% 15.48/2.54  --clausifier                            res/vclausify_rel
% 15.48/2.54  --clausifier_options                    --mode clausify
% 15.48/2.54  --stdin                                 false
% 15.48/2.54  --stats_out                             all
% 15.48/2.54  
% 15.48/2.54  ------ General Options
% 15.48/2.54  
% 15.48/2.54  --fof                                   false
% 15.48/2.54  --time_out_real                         305.
% 15.48/2.54  --time_out_virtual                      -1.
% 15.48/2.54  --symbol_type_check                     false
% 15.48/2.54  --clausify_out                          false
% 15.48/2.54  --sig_cnt_out                           false
% 15.48/2.54  --trig_cnt_out                          false
% 15.48/2.54  --trig_cnt_out_tolerance                1.
% 15.48/2.54  --trig_cnt_out_sk_spl                   false
% 15.48/2.54  --abstr_cl_out                          false
% 15.48/2.54  
% 15.48/2.54  ------ Global Options
% 15.48/2.54  
% 15.48/2.54  --schedule                              default
% 15.48/2.54  --add_important_lit                     false
% 15.48/2.54  --prop_solver_per_cl                    1000
% 15.48/2.54  --min_unsat_core                        false
% 15.48/2.54  --soft_assumptions                      false
% 15.48/2.54  --soft_lemma_size                       3
% 15.48/2.54  --prop_impl_unit_size                   0
% 15.48/2.54  --prop_impl_unit                        []
% 15.48/2.54  --share_sel_clauses                     true
% 15.48/2.54  --reset_solvers                         false
% 15.48/2.54  --bc_imp_inh                            [conj_cone]
% 15.48/2.54  --conj_cone_tolerance                   3.
% 15.48/2.54  --extra_neg_conj                        none
% 15.48/2.54  --large_theory_mode                     true
% 15.48/2.54  --prolific_symb_bound                   200
% 15.48/2.54  --lt_threshold                          2000
% 15.48/2.54  --clause_weak_htbl                      true
% 15.48/2.54  --gc_record_bc_elim                     false
% 15.48/2.54  
% 15.48/2.54  ------ Preprocessing Options
% 15.48/2.54  
% 15.48/2.54  --preprocessing_flag                    true
% 15.48/2.54  --time_out_prep_mult                    0.1
% 15.48/2.54  --splitting_mode                        input
% 15.48/2.54  --splitting_grd                         true
% 15.48/2.54  --splitting_cvd                         false
% 15.48/2.54  --splitting_cvd_svl                     false
% 15.48/2.54  --splitting_nvd                         32
% 15.48/2.54  --sub_typing                            true
% 15.48/2.54  --prep_gs_sim                           true
% 15.48/2.54  --prep_unflatten                        true
% 15.48/2.54  --prep_res_sim                          true
% 15.48/2.54  --prep_upred                            true
% 15.48/2.54  --prep_sem_filter                       exhaustive
% 15.48/2.54  --prep_sem_filter_out                   false
% 15.48/2.54  --pred_elim                             true
% 15.48/2.54  --res_sim_input                         true
% 15.48/2.54  --eq_ax_congr_red                       true
% 15.48/2.54  --pure_diseq_elim                       true
% 15.48/2.54  --brand_transform                       false
% 15.48/2.54  --non_eq_to_eq                          false
% 15.48/2.54  --prep_def_merge                        true
% 15.48/2.54  --prep_def_merge_prop_impl              false
% 15.48/2.54  --prep_def_merge_mbd                    true
% 15.48/2.54  --prep_def_merge_tr_red                 false
% 15.48/2.54  --prep_def_merge_tr_cl                  false
% 15.48/2.54  --smt_preprocessing                     true
% 15.48/2.54  --smt_ac_axioms                         fast
% 15.48/2.54  --preprocessed_out                      false
% 15.48/2.54  --preprocessed_stats                    false
% 15.48/2.54  
% 15.48/2.54  ------ Abstraction refinement Options
% 15.48/2.54  
% 15.48/2.54  --abstr_ref                             []
% 15.48/2.54  --abstr_ref_prep                        false
% 15.48/2.54  --abstr_ref_until_sat                   false
% 15.48/2.54  --abstr_ref_sig_restrict                funpre
% 15.48/2.54  --abstr_ref_af_restrict_to_split_sk     false
% 15.48/2.54  --abstr_ref_under                       []
% 15.48/2.54  
% 15.48/2.54  ------ SAT Options
% 15.48/2.54  
% 15.48/2.54  --sat_mode                              false
% 15.48/2.54  --sat_fm_restart_options                ""
% 15.48/2.54  --sat_gr_def                            false
% 15.48/2.54  --sat_epr_types                         true
% 15.48/2.54  --sat_non_cyclic_types                  false
% 15.48/2.54  --sat_finite_models                     false
% 15.48/2.54  --sat_fm_lemmas                         false
% 15.48/2.54  --sat_fm_prep                           false
% 15.48/2.54  --sat_fm_uc_incr                        true
% 15.48/2.54  --sat_out_model                         small
% 15.48/2.54  --sat_out_clauses                       false
% 15.48/2.54  
% 15.48/2.54  ------ QBF Options
% 15.48/2.54  
% 15.48/2.54  --qbf_mode                              false
% 15.48/2.54  --qbf_elim_univ                         false
% 15.48/2.54  --qbf_dom_inst                          none
% 15.48/2.54  --qbf_dom_pre_inst                      false
% 15.48/2.54  --qbf_sk_in                             false
% 15.48/2.54  --qbf_pred_elim                         true
% 15.48/2.54  --qbf_split                             512
% 15.48/2.54  
% 15.48/2.54  ------ BMC1 Options
% 15.48/2.54  
% 15.48/2.54  --bmc1_incremental                      false
% 15.48/2.54  --bmc1_axioms                           reachable_all
% 15.48/2.54  --bmc1_min_bound                        0
% 15.48/2.54  --bmc1_max_bound                        -1
% 15.48/2.54  --bmc1_max_bound_default                -1
% 15.48/2.54  --bmc1_symbol_reachability              true
% 15.48/2.54  --bmc1_property_lemmas                  false
% 15.48/2.54  --bmc1_k_induction                      false
% 15.48/2.54  --bmc1_non_equiv_states                 false
% 15.48/2.54  --bmc1_deadlock                         false
% 15.48/2.54  --bmc1_ucm                              false
% 15.48/2.54  --bmc1_add_unsat_core                   none
% 15.48/2.54  --bmc1_unsat_core_children              false
% 15.48/2.54  --bmc1_unsat_core_extrapolate_axioms    false
% 15.48/2.54  --bmc1_out_stat                         full
% 15.48/2.54  --bmc1_ground_init                      false
% 15.48/2.54  --bmc1_pre_inst_next_state              false
% 15.48/2.54  --bmc1_pre_inst_state                   false
% 15.48/2.54  --bmc1_pre_inst_reach_state             false
% 15.48/2.54  --bmc1_out_unsat_core                   false
% 15.48/2.54  --bmc1_aig_witness_out                  false
% 15.48/2.54  --bmc1_verbose                          false
% 15.48/2.54  --bmc1_dump_clauses_tptp                false
% 15.48/2.54  --bmc1_dump_unsat_core_tptp             false
% 15.48/2.54  --bmc1_dump_file                        -
% 15.48/2.54  --bmc1_ucm_expand_uc_limit              128
% 15.48/2.54  --bmc1_ucm_n_expand_iterations          6
% 15.48/2.54  --bmc1_ucm_extend_mode                  1
% 15.48/2.54  --bmc1_ucm_init_mode                    2
% 15.48/2.54  --bmc1_ucm_cone_mode                    none
% 15.48/2.54  --bmc1_ucm_reduced_relation_type        0
% 15.48/2.54  --bmc1_ucm_relax_model                  4
% 15.48/2.54  --bmc1_ucm_full_tr_after_sat            true
% 15.48/2.54  --bmc1_ucm_expand_neg_assumptions       false
% 15.48/2.54  --bmc1_ucm_layered_model                none
% 15.48/2.54  --bmc1_ucm_max_lemma_size               10
% 15.48/2.54  
% 15.48/2.54  ------ AIG Options
% 15.48/2.54  
% 15.48/2.54  --aig_mode                              false
% 15.48/2.54  
% 15.48/2.54  ------ Instantiation Options
% 15.48/2.54  
% 15.48/2.54  --instantiation_flag                    true
% 15.48/2.54  --inst_sos_flag                         false
% 15.48/2.54  --inst_sos_phase                        true
% 15.48/2.54  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.48/2.54  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.48/2.54  --inst_lit_sel_side                     none
% 15.48/2.54  --inst_solver_per_active                1400
% 15.48/2.54  --inst_solver_calls_frac                1.
% 15.48/2.54  --inst_passive_queue_type               priority_queues
% 15.48/2.54  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.48/2.54  --inst_passive_queues_freq              [25;2]
% 15.48/2.54  --inst_dismatching                      true
% 15.48/2.54  --inst_eager_unprocessed_to_passive     true
% 15.48/2.54  --inst_prop_sim_given                   true
% 15.48/2.54  --inst_prop_sim_new                     false
% 15.48/2.54  --inst_subs_new                         false
% 15.48/2.54  --inst_eq_res_simp                      false
% 15.48/2.54  --inst_subs_given                       false
% 15.48/2.54  --inst_orphan_elimination               true
% 15.48/2.54  --inst_learning_loop_flag               true
% 15.48/2.54  --inst_learning_start                   3000
% 15.48/2.54  --inst_learning_factor                  2
% 15.48/2.54  --inst_start_prop_sim_after_learn       3
% 15.48/2.54  --inst_sel_renew                        solver
% 15.48/2.54  --inst_lit_activity_flag                true
% 15.48/2.54  --inst_restr_to_given                   false
% 15.48/2.54  --inst_activity_threshold               500
% 15.48/2.54  --inst_out_proof                        true
% 15.48/2.54  
% 15.48/2.54  ------ Resolution Options
% 15.48/2.54  
% 15.48/2.54  --resolution_flag                       false
% 15.48/2.54  --res_lit_sel                           adaptive
% 15.48/2.54  --res_lit_sel_side                      none
% 15.48/2.54  --res_ordering                          kbo
% 15.48/2.54  --res_to_prop_solver                    active
% 15.48/2.54  --res_prop_simpl_new                    false
% 15.48/2.54  --res_prop_simpl_given                  true
% 15.48/2.54  --res_passive_queue_type                priority_queues
% 15.48/2.54  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.48/2.54  --res_passive_queues_freq               [15;5]
% 15.48/2.54  --res_forward_subs                      full
% 15.48/2.54  --res_backward_subs                     full
% 15.48/2.54  --res_forward_subs_resolution           true
% 15.48/2.54  --res_backward_subs_resolution          true
% 15.48/2.54  --res_orphan_elimination                true
% 15.48/2.54  --res_time_limit                        2.
% 15.48/2.54  --res_out_proof                         true
% 15.48/2.54  
% 15.48/2.54  ------ Superposition Options
% 15.48/2.54  
% 15.48/2.54  --superposition_flag                    true
% 15.48/2.54  --sup_passive_queue_type                priority_queues
% 15.48/2.54  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.48/2.54  --sup_passive_queues_freq               [8;1;4]
% 15.48/2.54  --demod_completeness_check              fast
% 15.48/2.54  --demod_use_ground                      true
% 15.48/2.54  --sup_to_prop_solver                    passive
% 15.48/2.54  --sup_prop_simpl_new                    true
% 15.48/2.54  --sup_prop_simpl_given                  true
% 15.48/2.54  --sup_fun_splitting                     false
% 15.48/2.54  --sup_smt_interval                      50000
% 15.48/2.54  
% 15.48/2.54  ------ Superposition Simplification Setup
% 15.48/2.54  
% 15.48/2.54  --sup_indices_passive                   []
% 15.48/2.54  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.48/2.54  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.48/2.54  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.48/2.54  --sup_full_triv                         [TrivRules;PropSubs]
% 15.48/2.54  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.48/2.54  --sup_full_bw                           [BwDemod]
% 15.48/2.54  --sup_immed_triv                        [TrivRules]
% 15.48/2.54  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.48/2.54  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.48/2.54  --sup_immed_bw_main                     []
% 15.48/2.54  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.48/2.54  --sup_input_triv                        [Unflattening;TrivRules]
% 15.48/2.54  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.48/2.54  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.48/2.54  
% 15.48/2.54  ------ Combination Options
% 15.48/2.54  
% 15.48/2.54  --comb_res_mult                         3
% 15.48/2.54  --comb_sup_mult                         2
% 15.48/2.54  --comb_inst_mult                        10
% 15.48/2.54  
% 15.48/2.54  ------ Debug Options
% 15.48/2.54  
% 15.48/2.54  --dbg_backtrace                         false
% 15.48/2.54  --dbg_dump_prop_clauses                 false
% 15.48/2.54  --dbg_dump_prop_clauses_file            -
% 15.48/2.54  --dbg_out_stat                          false
% 15.48/2.54  
% 15.48/2.54  
% 15.48/2.54  
% 15.48/2.54  
% 15.48/2.54  ------ Proving...
% 15.48/2.54  
% 15.48/2.54  
% 15.48/2.54  % SZS status Theorem for theBenchmark.p
% 15.48/2.54  
% 15.48/2.54   Resolution empty clause
% 15.48/2.54  
% 15.48/2.54  % SZS output start CNFRefutation for theBenchmark.p
% 15.48/2.54  
% 15.48/2.54  fof(f12,axiom,(
% 15.48/2.54    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 15.48/2.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.48/2.54  
% 15.48/2.54  fof(f28,plain,(
% 15.48/2.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 15.48/2.54    inference(ennf_transformation,[],[f12])).
% 15.48/2.54  
% 15.48/2.54  fof(f29,plain,(
% 15.48/2.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 15.48/2.54    inference(flattening,[],[f28])).
% 15.48/2.54  
% 15.48/2.54  fof(f60,plain,(
% 15.48/2.54    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 15.48/2.54    inference(cnf_transformation,[],[f29])).
% 15.48/2.54  
% 15.48/2.54  fof(f16,conjecture,(
% 15.48/2.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 15.48/2.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.48/2.54  
% 15.48/2.54  fof(f17,negated_conjecture,(
% 15.48/2.54    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 15.48/2.54    inference(negated_conjecture,[],[f16])).
% 15.48/2.54  
% 15.48/2.54  fof(f36,plain,(
% 15.48/2.54    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 15.48/2.54    inference(ennf_transformation,[],[f17])).
% 15.48/2.54  
% 15.48/2.54  fof(f37,plain,(
% 15.48/2.54    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 15.48/2.54    inference(flattening,[],[f36])).
% 15.48/2.54  
% 15.48/2.54  fof(f43,plain,(
% 15.48/2.54    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 15.48/2.54    introduced(choice_axiom,[])).
% 15.48/2.54  
% 15.48/2.54  fof(f44,plain,(
% 15.48/2.54    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 15.48/2.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f37,f43])).
% 15.48/2.54  
% 15.48/2.54  fof(f73,plain,(
% 15.48/2.54    r1_tarski(sK2,sK0)),
% 15.48/2.54    inference(cnf_transformation,[],[f44])).
% 15.48/2.54  
% 15.48/2.54  fof(f13,axiom,(
% 15.48/2.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 15.48/2.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.48/2.54  
% 15.48/2.54  fof(f30,plain,(
% 15.48/2.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.48/2.54    inference(ennf_transformation,[],[f13])).
% 15.48/2.54  
% 15.48/2.54  fof(f31,plain,(
% 15.48/2.54    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.48/2.54    inference(flattening,[],[f30])).
% 15.48/2.54  
% 15.48/2.54  fof(f42,plain,(
% 15.48/2.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.48/2.54    inference(nnf_transformation,[],[f31])).
% 15.48/2.54  
% 15.48/2.54  fof(f61,plain,(
% 15.48/2.54    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.48/2.54    inference(cnf_transformation,[],[f42])).
% 15.48/2.54  
% 15.48/2.54  fof(f71,plain,(
% 15.48/2.54    v1_funct_2(sK3,sK0,sK1)),
% 15.48/2.54    inference(cnf_transformation,[],[f44])).
% 15.48/2.54  
% 15.48/2.54  fof(f72,plain,(
% 15.48/2.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 15.48/2.54    inference(cnf_transformation,[],[f44])).
% 15.48/2.54  
% 15.48/2.54  fof(f11,axiom,(
% 15.48/2.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 15.48/2.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.48/2.54  
% 15.48/2.54  fof(f27,plain,(
% 15.48/2.54    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.48/2.54    inference(ennf_transformation,[],[f11])).
% 15.48/2.54  
% 15.48/2.54  fof(f59,plain,(
% 15.48/2.54    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.48/2.54    inference(cnf_transformation,[],[f27])).
% 15.48/2.54  
% 15.48/2.54  fof(f9,axiom,(
% 15.48/2.54    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 15.48/2.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.48/2.54  
% 15.48/2.54  fof(f24,plain,(
% 15.48/2.54    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 15.48/2.54    inference(ennf_transformation,[],[f9])).
% 15.48/2.54  
% 15.48/2.54  fof(f25,plain,(
% 15.48/2.54    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 15.48/2.54    inference(flattening,[],[f24])).
% 15.48/2.54  
% 15.48/2.54  fof(f57,plain,(
% 15.48/2.54    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 15.48/2.54    inference(cnf_transformation,[],[f25])).
% 15.48/2.54  
% 15.48/2.54  fof(f3,axiom,(
% 15.48/2.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 15.48/2.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.48/2.54  
% 15.48/2.54  fof(f40,plain,(
% 15.48/2.54    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 15.48/2.54    inference(nnf_transformation,[],[f3])).
% 15.48/2.54  
% 15.48/2.54  fof(f49,plain,(
% 15.48/2.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 15.48/2.54    inference(cnf_transformation,[],[f40])).
% 15.48/2.54  
% 15.48/2.54  fof(f4,axiom,(
% 15.48/2.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 15.48/2.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.48/2.54  
% 15.48/2.54  fof(f20,plain,(
% 15.48/2.54    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 15.48/2.54    inference(ennf_transformation,[],[f4])).
% 15.48/2.54  
% 15.48/2.54  fof(f51,plain,(
% 15.48/2.54    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 15.48/2.54    inference(cnf_transformation,[],[f20])).
% 15.48/2.54  
% 15.48/2.54  fof(f50,plain,(
% 15.48/2.54    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 15.48/2.54    inference(cnf_transformation,[],[f40])).
% 15.48/2.54  
% 15.48/2.54  fof(f6,axiom,(
% 15.48/2.54    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 15.48/2.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.48/2.54  
% 15.48/2.54  fof(f54,plain,(
% 15.48/2.54    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 15.48/2.54    inference(cnf_transformation,[],[f6])).
% 15.48/2.54  
% 15.48/2.54  fof(f7,axiom,(
% 15.48/2.54    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 15.48/2.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.48/2.54  
% 15.48/2.54  fof(f22,plain,(
% 15.48/2.54    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 15.48/2.54    inference(ennf_transformation,[],[f7])).
% 15.48/2.54  
% 15.48/2.54  fof(f55,plain,(
% 15.48/2.54    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 15.48/2.54    inference(cnf_transformation,[],[f22])).
% 15.48/2.54  
% 15.48/2.54  fof(f15,axiom,(
% 15.48/2.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 15.48/2.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.48/2.54  
% 15.48/2.54  fof(f34,plain,(
% 15.48/2.54    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 15.48/2.54    inference(ennf_transformation,[],[f15])).
% 15.48/2.54  
% 15.48/2.54  fof(f35,plain,(
% 15.48/2.54    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 15.48/2.54    inference(flattening,[],[f34])).
% 15.48/2.54  
% 15.48/2.54  fof(f69,plain,(
% 15.48/2.54    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 15.48/2.54    inference(cnf_transformation,[],[f35])).
% 15.48/2.54  
% 15.48/2.54  fof(f70,plain,(
% 15.48/2.54    v1_funct_1(sK3)),
% 15.48/2.54    inference(cnf_transformation,[],[f44])).
% 15.48/2.54  
% 15.48/2.54  fof(f14,axiom,(
% 15.48/2.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 15.48/2.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.48/2.54  
% 15.48/2.54  fof(f32,plain,(
% 15.48/2.54    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 15.48/2.54    inference(ennf_transformation,[],[f14])).
% 15.48/2.54  
% 15.48/2.54  fof(f33,plain,(
% 15.48/2.54    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 15.48/2.54    inference(flattening,[],[f32])).
% 15.48/2.54  
% 15.48/2.54  fof(f68,plain,(
% 15.48/2.54    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 15.48/2.54    inference(cnf_transformation,[],[f33])).
% 15.48/2.54  
% 15.48/2.54  fof(f10,axiom,(
% 15.48/2.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 15.48/2.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.48/2.54  
% 15.48/2.54  fof(f18,plain,(
% 15.48/2.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 15.48/2.54    inference(pure_predicate_removal,[],[f10])).
% 15.48/2.54  
% 15.48/2.54  fof(f26,plain,(
% 15.48/2.54    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.48/2.54    inference(ennf_transformation,[],[f18])).
% 15.48/2.54  
% 15.48/2.54  fof(f58,plain,(
% 15.48/2.54    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.48/2.54    inference(cnf_transformation,[],[f26])).
% 15.48/2.54  
% 15.48/2.54  fof(f5,axiom,(
% 15.48/2.54    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 15.48/2.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.48/2.54  
% 15.48/2.54  fof(f21,plain,(
% 15.48/2.54    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 15.48/2.54    inference(ennf_transformation,[],[f5])).
% 15.48/2.54  
% 15.48/2.54  fof(f41,plain,(
% 15.48/2.54    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 15.48/2.54    inference(nnf_transformation,[],[f21])).
% 15.48/2.54  
% 15.48/2.54  fof(f52,plain,(
% 15.48/2.54    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 15.48/2.54    inference(cnf_transformation,[],[f41])).
% 15.48/2.54  
% 15.48/2.54  fof(f2,axiom,(
% 15.48/2.54    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 15.48/2.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.48/2.54  
% 15.48/2.54  fof(f38,plain,(
% 15.48/2.54    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 15.48/2.54    inference(nnf_transformation,[],[f2])).
% 15.48/2.54  
% 15.48/2.54  fof(f39,plain,(
% 15.48/2.54    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 15.48/2.54    inference(flattening,[],[f38])).
% 15.48/2.54  
% 15.48/2.54  fof(f46,plain,(
% 15.48/2.54    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 15.48/2.54    inference(cnf_transformation,[],[f39])).
% 15.48/2.54  
% 15.48/2.54  fof(f47,plain,(
% 15.48/2.54    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 15.48/2.54    inference(cnf_transformation,[],[f39])).
% 15.48/2.54  
% 15.48/2.54  fof(f77,plain,(
% 15.48/2.54    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 15.48/2.54    inference(equality_resolution,[],[f47])).
% 15.48/2.54  
% 15.48/2.54  fof(f48,plain,(
% 15.48/2.54    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 15.48/2.54    inference(cnf_transformation,[],[f39])).
% 15.48/2.54  
% 15.48/2.54  fof(f76,plain,(
% 15.48/2.54    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 15.48/2.54    inference(equality_resolution,[],[f48])).
% 15.48/2.54  
% 15.48/2.54  fof(f65,plain,(
% 15.48/2.54    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.48/2.54    inference(cnf_transformation,[],[f42])).
% 15.48/2.54  
% 15.48/2.54  fof(f80,plain,(
% 15.48/2.54    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 15.48/2.54    inference(equality_resolution,[],[f65])).
% 15.48/2.54  
% 15.48/2.54  fof(f74,plain,(
% 15.48/2.54    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 15.48/2.54    inference(cnf_transformation,[],[f44])).
% 15.48/2.54  
% 15.48/2.54  fof(f8,axiom,(
% 15.48/2.54    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 15.48/2.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.48/2.54  
% 15.48/2.54  fof(f23,plain,(
% 15.48/2.54    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 15.48/2.54    inference(ennf_transformation,[],[f8])).
% 15.48/2.54  
% 15.48/2.54  fof(f56,plain,(
% 15.48/2.54    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 15.48/2.54    inference(cnf_transformation,[],[f23])).
% 15.48/2.54  
% 15.48/2.54  fof(f1,axiom,(
% 15.48/2.54    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 15.48/2.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.48/2.54  
% 15.48/2.54  fof(f19,plain,(
% 15.48/2.54    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 15.48/2.54    inference(ennf_transformation,[],[f1])).
% 15.48/2.54  
% 15.48/2.54  fof(f45,plain,(
% 15.48/2.54    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 15.48/2.54    inference(cnf_transformation,[],[f19])).
% 15.48/2.54  
% 15.48/2.54  fof(f67,plain,(
% 15.48/2.54    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 15.48/2.54    inference(cnf_transformation,[],[f33])).
% 15.48/2.54  
% 15.48/2.54  fof(f75,plain,(
% 15.48/2.54    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 15.48/2.54    inference(cnf_transformation,[],[f44])).
% 15.48/2.54  
% 15.48/2.54  fof(f63,plain,(
% 15.48/2.54    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.48/2.54    inference(cnf_transformation,[],[f42])).
% 15.48/2.54  
% 15.48/2.54  cnf(c_15,plain,
% 15.48/2.54      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.48/2.54      | ~ r1_tarski(k1_relat_1(X0),X1)
% 15.48/2.54      | ~ r1_tarski(k2_relat_1(X0),X2)
% 15.48/2.54      | ~ v1_relat_1(X0) ),
% 15.48/2.54      inference(cnf_transformation,[],[f60]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_1353,plain,
% 15.48/2.54      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 15.48/2.54      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 15.48/2.54      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 15.48/2.54      | v1_relat_1(X0) != iProver_top ),
% 15.48/2.54      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_27,negated_conjecture,
% 15.48/2.54      ( r1_tarski(sK2,sK0) ),
% 15.48/2.54      inference(cnf_transformation,[],[f73]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_1349,plain,
% 15.48/2.54      ( r1_tarski(sK2,sK0) = iProver_top ),
% 15.48/2.54      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_21,plain,
% 15.48/2.54      ( ~ v1_funct_2(X0,X1,X2)
% 15.48/2.54      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.48/2.54      | k1_relset_1(X1,X2,X0) = X1
% 15.48/2.54      | k1_xboole_0 = X2 ),
% 15.48/2.54      inference(cnf_transformation,[],[f61]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_29,negated_conjecture,
% 15.48/2.54      ( v1_funct_2(sK3,sK0,sK1) ),
% 15.48/2.54      inference(cnf_transformation,[],[f71]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_494,plain,
% 15.48/2.54      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.48/2.54      | k1_relset_1(X1,X2,X0) = X1
% 15.48/2.54      | sK3 != X0
% 15.48/2.54      | sK1 != X2
% 15.48/2.54      | sK0 != X1
% 15.48/2.54      | k1_xboole_0 = X2 ),
% 15.48/2.54      inference(resolution_lifted,[status(thm)],[c_21,c_29]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_495,plain,
% 15.48/2.54      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 15.48/2.54      | k1_relset_1(sK0,sK1,sK3) = sK0
% 15.48/2.54      | k1_xboole_0 = sK1 ),
% 15.48/2.54      inference(unflattening,[status(thm)],[c_494]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_28,negated_conjecture,
% 15.48/2.54      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 15.48/2.54      inference(cnf_transformation,[],[f72]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_497,plain,
% 15.48/2.54      ( k1_relset_1(sK0,sK1,sK3) = sK0 | k1_xboole_0 = sK1 ),
% 15.48/2.54      inference(global_propositional_subsumption,[status(thm)],[c_495,c_28]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_1348,plain,
% 15.48/2.54      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 15.48/2.54      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_14,plain,
% 15.48/2.54      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.48/2.54      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 15.48/2.54      inference(cnf_transformation,[],[f59]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_1354,plain,
% 15.48/2.54      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 15.48/2.54      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 15.48/2.54      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_2852,plain,
% 15.48/2.54      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 15.48/2.54      inference(superposition,[status(thm)],[c_1348,c_1354]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_3206,plain,
% 15.48/2.54      ( k1_relat_1(sK3) = sK0 | sK1 = k1_xboole_0 ),
% 15.48/2.54      inference(superposition,[status(thm)],[c_497,c_2852]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_12,plain,
% 15.48/2.54      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 15.48/2.54      | ~ v1_relat_1(X1)
% 15.48/2.54      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 15.48/2.54      inference(cnf_transformation,[],[f57]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_1355,plain,
% 15.48/2.54      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 15.48/2.54      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 15.48/2.54      | v1_relat_1(X0) != iProver_top ),
% 15.48/2.54      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_3241,plain,
% 15.48/2.54      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 15.48/2.54      | sK1 = k1_xboole_0
% 15.48/2.54      | r1_tarski(X0,sK0) != iProver_top
% 15.48/2.54      | v1_relat_1(sK3) != iProver_top ),
% 15.48/2.54      inference(superposition,[status(thm)],[c_3206,c_1355]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_33,plain,
% 15.48/2.54      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 15.48/2.54      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_5,plain,
% 15.48/2.54      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 15.48/2.54      inference(cnf_transformation,[],[f49]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_1569,plain,
% 15.48/2.54      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 15.48/2.54      | r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_5]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_1570,plain,
% 15.48/2.54      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 15.48/2.54      | r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 15.48/2.54      inference(predicate_to_equality,[status(thm)],[c_1569]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_6,plain,
% 15.48/2.54      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 15.48/2.54      inference(cnf_transformation,[],[f51]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_4,plain,
% 15.48/2.54      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 15.48/2.54      inference(cnf_transformation,[],[f50]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_219,plain,
% 15.48/2.54      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 15.48/2.54      inference(prop_impl,[status(thm)],[c_4]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_220,plain,
% 15.48/2.54      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 15.48/2.54      inference(renaming,[status(thm)],[c_219]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_278,plain,
% 15.48/2.54      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 15.48/2.54      inference(bin_hyper_res,[status(thm)],[c_6,c_220]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_1586,plain,
% 15.48/2.54      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 15.48/2.54      | v1_relat_1(X0)
% 15.48/2.54      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_278]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_2002,plain,
% 15.48/2.54      ( ~ r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))
% 15.48/2.54      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
% 15.48/2.54      | v1_relat_1(sK3) ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_1586]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_2003,plain,
% 15.48/2.54      ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) != iProver_top
% 15.48/2.54      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 15.48/2.54      | v1_relat_1(sK3) = iProver_top ),
% 15.48/2.54      inference(predicate_to_equality,[status(thm)],[c_2002]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_9,plain,
% 15.48/2.54      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 15.48/2.54      inference(cnf_transformation,[],[f54]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_2096,plain,
% 15.48/2.54      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_9]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_2097,plain,
% 15.48/2.54      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 15.48/2.54      inference(predicate_to_equality,[status(thm)],[c_2096]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_3246,plain,
% 15.48/2.54      ( r1_tarski(X0,sK0) != iProver_top
% 15.48/2.54      | sK1 = k1_xboole_0
% 15.48/2.54      | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
% 15.48/2.54      inference(global_propositional_subsumption,
% 15.48/2.54                [status(thm)],
% 15.48/2.54                [c_3241,c_33,c_1570,c_2003,c_2097]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_3247,plain,
% 15.48/2.54      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 15.48/2.54      | sK1 = k1_xboole_0
% 15.48/2.54      | r1_tarski(X0,sK0) != iProver_top ),
% 15.48/2.54      inference(renaming,[status(thm)],[c_3246]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_3257,plain,
% 15.48/2.54      ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2 | sK1 = k1_xboole_0 ),
% 15.48/2.54      inference(superposition,[status(thm)],[c_1349,c_3247]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_10,plain,
% 15.48/2.54      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 15.48/2.54      inference(cnf_transformation,[],[f55]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_1357,plain,
% 15.48/2.54      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
% 15.48/2.54      | v1_relat_1(X0) != iProver_top ),
% 15.48/2.54      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_3423,plain,
% 15.48/2.54      ( sK1 = k1_xboole_0
% 15.48/2.54      | r1_tarski(sK2,sK2) = iProver_top
% 15.48/2.54      | v1_relat_1(sK3) != iProver_top ),
% 15.48/2.54      inference(superposition,[status(thm)],[c_3257,c_1357]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_3444,plain,
% 15.48/2.54      ( r1_tarski(sK2,sK2) = iProver_top | sK1 = k1_xboole_0 ),
% 15.48/2.54      inference(global_propositional_subsumption,
% 15.48/2.54                [status(thm)],
% 15.48/2.54                [c_3423,c_33,c_1570,c_2003,c_2097]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_3445,plain,
% 15.48/2.54      ( sK1 = k1_xboole_0 | r1_tarski(sK2,sK2) = iProver_top ),
% 15.48/2.54      inference(renaming,[status(thm)],[c_3444]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_24,plain,
% 15.48/2.54      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.48/2.54      | ~ v1_funct_1(X0)
% 15.48/2.54      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 15.48/2.54      inference(cnf_transformation,[],[f69]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_1350,plain,
% 15.48/2.54      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 15.48/2.54      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.48/2.54      | v1_funct_1(X2) != iProver_top ),
% 15.48/2.54      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_4488,plain,
% 15.48/2.54      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
% 15.48/2.54      | v1_funct_1(sK3) != iProver_top ),
% 15.48/2.54      inference(superposition,[status(thm)],[c_1348,c_1350]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_30,negated_conjecture,
% 15.48/2.54      ( v1_funct_1(sK3) ),
% 15.48/2.54      inference(cnf_transformation,[],[f70]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_1651,plain,
% 15.48/2.54      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 15.48/2.54      | ~ v1_funct_1(sK3)
% 15.48/2.54      | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_24]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_4429,plain,
% 15.48/2.54      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 15.48/2.54      | ~ v1_funct_1(sK3)
% 15.48/2.54      | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_1651]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_4637,plain,
% 15.48/2.54      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 15.48/2.54      inference(global_propositional_subsumption,
% 15.48/2.54                [status(thm)],
% 15.48/2.54                [c_4488,c_30,c_28,c_4429]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_22,plain,
% 15.48/2.54      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.48/2.54      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.48/2.54      | ~ v1_funct_1(X0) ),
% 15.48/2.54      inference(cnf_transformation,[],[f68]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_1352,plain,
% 15.48/2.54      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 15.48/2.54      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 15.48/2.54      | v1_funct_1(X0) != iProver_top ),
% 15.48/2.54      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_4679,plain,
% 15.48/2.54      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 15.48/2.54      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 15.48/2.54      | v1_funct_1(sK3) != iProver_top ),
% 15.48/2.54      inference(superposition,[status(thm)],[c_4637,c_1352]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_31,plain,
% 15.48/2.54      ( v1_funct_1(sK3) = iProver_top ),
% 15.48/2.54      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_4754,plain,
% 15.48/2.54      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 15.48/2.54      inference(global_propositional_subsumption,
% 15.48/2.54                [status(thm)],
% 15.48/2.54                [c_4679,c_31,c_33]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_13,plain,
% 15.48/2.54      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 15.48/2.54      inference(cnf_transformation,[],[f58]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_8,plain,
% 15.48/2.54      ( ~ v5_relat_1(X0,X1) | r1_tarski(k2_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 15.48/2.54      inference(cnf_transformation,[],[f52]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_373,plain,
% 15.48/2.54      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.48/2.54      | r1_tarski(k2_relat_1(X0),X2)
% 15.48/2.54      | ~ v1_relat_1(X0) ),
% 15.48/2.54      inference(resolution,[status(thm)],[c_13,c_8]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_1345,plain,
% 15.48/2.54      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 15.48/2.54      | r1_tarski(k2_relat_1(X0),X2) = iProver_top
% 15.48/2.54      | v1_relat_1(X0) != iProver_top ),
% 15.48/2.54      inference(predicate_to_equality,[status(thm)],[c_373]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_4765,plain,
% 15.48/2.54      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) = iProver_top
% 15.48/2.54      | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
% 15.48/2.54      inference(superposition,[status(thm)],[c_4754,c_1345]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_1359,plain,
% 15.48/2.54      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 15.48/2.54      | r1_tarski(X0,X1) = iProver_top ),
% 15.48/2.54      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_4761,plain,
% 15.48/2.54      ( r1_tarski(k7_relat_1(sK3,X0),k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 15.48/2.54      inference(superposition,[status(thm)],[c_4754,c_1359]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_1346,plain,
% 15.48/2.54      ( r1_tarski(X0,X1) != iProver_top
% 15.48/2.54      | v1_relat_1(X1) != iProver_top
% 15.48/2.54      | v1_relat_1(X0) = iProver_top ),
% 15.48/2.54      inference(predicate_to_equality,[status(thm)],[c_278]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_4853,plain,
% 15.48/2.54      ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top
% 15.48/2.54      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top ),
% 15.48/2.54      inference(superposition,[status(thm)],[c_4761,c_1346]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_4891,plain,
% 15.48/2.54      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) = iProver_top ),
% 15.48/2.54      inference(global_propositional_subsumption,
% 15.48/2.54                [status(thm)],
% 15.48/2.54                [c_4765,c_2097,c_4853]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_4202,plain,
% 15.48/2.54      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 15.48/2.54      | r1_tarski(k1_relat_1(X2),X0) != iProver_top
% 15.48/2.54      | r1_tarski(k2_relat_1(X2),X1) != iProver_top
% 15.48/2.54      | v1_relat_1(X2) != iProver_top ),
% 15.48/2.54      inference(superposition,[status(thm)],[c_1353,c_1354]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_46839,plain,
% 15.48/2.54      ( k1_relset_1(X0,X1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
% 15.48/2.54      | sK1 = k1_xboole_0
% 15.48/2.54      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1) != iProver_top
% 15.48/2.54      | r1_tarski(sK2,X0) != iProver_top
% 15.48/2.54      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 15.48/2.54      inference(superposition,[status(thm)],[c_3257,c_4202]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_3,plain,
% 15.48/2.54      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 15.48/2.54      | k1_xboole_0 = X0
% 15.48/2.54      | k1_xboole_0 = X1 ),
% 15.48/2.54      inference(cnf_transformation,[],[f46]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_97,plain,
% 15.48/2.54      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 15.48/2.54      | k1_xboole_0 = k1_xboole_0 ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_3]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_2,plain,
% 15.48/2.54      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 15.48/2.54      inference(cnf_transformation,[],[f77]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_98,plain,
% 15.48/2.54      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_2]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_1,plain,
% 15.48/2.54      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 15.48/2.54      inference(cnf_transformation,[],[f76]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_1358,plain,
% 15.48/2.54      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 15.48/2.54      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_1899,plain,
% 15.48/2.54      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 15.48/2.54      inference(superposition,[status(thm)],[c_1,c_1358]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_17,plain,
% 15.48/2.54      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 15.48/2.54      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 15.48/2.54      | k1_xboole_0 = X1
% 15.48/2.54      | k1_xboole_0 = X0 ),
% 15.48/2.54      inference(cnf_transformation,[],[f80]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_426,plain,
% 15.48/2.54      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 15.48/2.54      | sK3 != X0
% 15.48/2.54      | sK1 != k1_xboole_0
% 15.48/2.54      | sK0 != X1
% 15.48/2.54      | k1_xboole_0 = X0
% 15.48/2.54      | k1_xboole_0 = X1 ),
% 15.48/2.54      inference(resolution_lifted,[status(thm)],[c_17,c_29]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_427,plain,
% 15.48/2.54      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
% 15.48/2.54      | sK1 != k1_xboole_0
% 15.48/2.54      | k1_xboole_0 = sK3
% 15.48/2.54      | k1_xboole_0 = sK0 ),
% 15.48/2.54      inference(unflattening,[status(thm)],[c_426]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_1343,plain,
% 15.48/2.54      ( sK1 != k1_xboole_0
% 15.48/2.54      | k1_xboole_0 = sK3
% 15.48/2.54      | k1_xboole_0 = sK0
% 15.48/2.54      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
% 15.48/2.54      inference(predicate_to_equality,[status(thm)],[c_427]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_1431,plain,
% 15.48/2.54      ( sK3 = k1_xboole_0
% 15.48/2.54      | sK1 != k1_xboole_0
% 15.48/2.54      | sK0 = k1_xboole_0
% 15.48/2.54      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 15.48/2.54      inference(demodulation,[status(thm)],[c_1343,c_1]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_26,negated_conjecture,
% 15.48/2.54      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 15.48/2.54      inference(cnf_transformation,[],[f74]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_775,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_1603,plain,
% 15.48/2.54      ( sK0 != X0 | sK0 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_775]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_1806,plain,
% 15.48/2.54      ( sK0 != sK0 | sK0 = k1_xboole_0 | k1_xboole_0 != sK0 ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_1603]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_774,plain,( X0 = X0 ),theory(equality) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_1807,plain,
% 15.48/2.54      ( sK0 = sK0 ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_774]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_1854,plain,
% 15.48/2.54      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_775]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_1855,plain,
% 15.48/2.54      ( sK1 != k1_xboole_0 | k1_xboole_0 = sK1 | k1_xboole_0 != k1_xboole_0 ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_1854]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_2021,plain,
% 15.48/2.54      ( sK0 = k1_xboole_0 | sK1 != k1_xboole_0 ),
% 15.48/2.54      inference(global_propositional_subsumption,
% 15.48/2.54                [status(thm)],
% 15.48/2.54                [c_1431,c_26,c_97,c_98,c_1806,c_1807,c_1855]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_2022,plain,
% 15.48/2.54      ( sK1 != k1_xboole_0 | sK0 = k1_xboole_0 ),
% 15.48/2.54      inference(renaming,[status(thm)],[c_2021]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_11,plain,
% 15.48/2.54      ( r1_tarski(k7_relat_1(X0,X1),X0) | ~ v1_relat_1(X0) ),
% 15.48/2.54      inference(cnf_transformation,[],[f56]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_1356,plain,
% 15.48/2.54      ( r1_tarski(k7_relat_1(X0,X1),X0) = iProver_top
% 15.48/2.54      | v1_relat_1(X0) != iProver_top ),
% 15.48/2.54      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_0,plain,
% 15.48/2.54      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 15.48/2.54      inference(cnf_transformation,[],[f45]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_1361,plain,
% 15.48/2.54      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 15.48/2.54      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_2092,plain,
% 15.48/2.54      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0
% 15.48/2.54      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 15.48/2.54      inference(superposition,[status(thm)],[c_1356,c_1361]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_2193,plain,
% 15.48/2.54      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 15.48/2.54      inference(global_propositional_subsumption,[status(thm)],[c_2092,c_1899]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_2197,plain,
% 15.48/2.54      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top
% 15.48/2.54      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 15.48/2.54      inference(superposition,[status(thm)],[c_2193,c_1356]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_776,plain,
% 15.48/2.54      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 15.48/2.54      theory(equality) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_3569,plain,
% 15.48/2.54      ( ~ r1_tarski(X0,X1)
% 15.48/2.54      | r1_tarski(sK0,k1_xboole_0)
% 15.48/2.54      | sK0 != X0
% 15.48/2.54      | k1_xboole_0 != X1 ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_776]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_3570,plain,
% 15.48/2.54      ( sK0 != X0
% 15.48/2.54      | k1_xboole_0 != X1
% 15.48/2.54      | r1_tarski(X0,X1) != iProver_top
% 15.48/2.54      | r1_tarski(sK0,k1_xboole_0) = iProver_top ),
% 15.48/2.54      inference(predicate_to_equality,[status(thm)],[c_3569]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_3572,plain,
% 15.48/2.54      ( sK0 != k1_xboole_0
% 15.48/2.54      | k1_xboole_0 != k1_xboole_0
% 15.48/2.54      | r1_tarski(sK0,k1_xboole_0) = iProver_top
% 15.48/2.54      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_3570]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_1769,plain,
% 15.48/2.54      ( r1_tarski(k2_relat_1(sK3),sK1) = iProver_top
% 15.48/2.54      | v1_relat_1(sK3) != iProver_top ),
% 15.48/2.54      inference(superposition,[status(thm)],[c_1348,c_1345]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_4200,plain,
% 15.48/2.54      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 15.48/2.54      | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
% 15.48/2.54      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 15.48/2.54      | v1_relat_1(X0) != iProver_top ),
% 15.48/2.54      inference(superposition,[status(thm)],[c_2,c_1353]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_5427,plain,
% 15.48/2.54      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 15.48/2.54      | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top
% 15.48/2.54      | v1_relat_1(sK3) != iProver_top ),
% 15.48/2.54      inference(superposition,[status(thm)],[c_1769,c_4200]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_5604,plain,
% 15.48/2.54      ( r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top
% 15.48/2.54      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 15.48/2.54      inference(global_propositional_subsumption,
% 15.48/2.54                [status(thm)],
% 15.48/2.54                [c_5427,c_33,c_1570,c_2003,c_2097]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_5605,plain,
% 15.48/2.54      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 15.48/2.54      | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top ),
% 15.48/2.54      inference(renaming,[status(thm)],[c_5604]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_5610,plain,
% 15.48/2.54      ( sK1 = k1_xboole_0
% 15.48/2.54      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 15.48/2.54      | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
% 15.48/2.54      inference(superposition,[status(thm)],[c_3206,c_5605]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_3499,plain,
% 15.48/2.54      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) != iProver_top
% 15.48/2.54      | m1_subset_1(k2_partfun1(X1,k1_xboole_0,X0,X2),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 15.48/2.54      | v1_funct_1(X0) != iProver_top ),
% 15.48/2.54      inference(superposition,[status(thm)],[c_1,c_1352]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_3543,plain,
% 15.48/2.54      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 15.48/2.54      | m1_subset_1(k2_partfun1(X1,k1_xboole_0,X0,X2),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 15.48/2.54      | v1_funct_1(X0) != iProver_top ),
% 15.48/2.54      inference(demodulation,[status(thm)],[c_3499,c_1]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_4490,plain,
% 15.48/2.54      ( k2_partfun1(k1_xboole_0,X0,X1,X2) = k7_relat_1(X1,X2)
% 15.48/2.54      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 15.48/2.54      | v1_funct_1(X1) != iProver_top ),
% 15.48/2.54      inference(superposition,[status(thm)],[c_2,c_1350]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_5120,plain,
% 15.48/2.54      ( k2_partfun1(k1_xboole_0,X0,k2_partfun1(X1,k1_xboole_0,X2,X3),X4) = k7_relat_1(k2_partfun1(X1,k1_xboole_0,X2,X3),X4)
% 15.48/2.54      | m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 15.48/2.54      | v1_funct_1(X2) != iProver_top
% 15.48/2.54      | v1_funct_1(k2_partfun1(X1,k1_xboole_0,X2,X3)) != iProver_top ),
% 15.48/2.54      inference(superposition,[status(thm)],[c_3543,c_4490]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_23,plain,
% 15.48/2.54      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.48/2.54      | ~ v1_funct_1(X0)
% 15.48/2.54      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
% 15.48/2.54      inference(cnf_transformation,[],[f67]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_1351,plain,
% 15.48/2.54      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 15.48/2.54      | v1_funct_1(X0) != iProver_top
% 15.48/2.54      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
% 15.48/2.54      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_2761,plain,
% 15.48/2.54      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 15.48/2.54      | v1_funct_1(X0) != iProver_top
% 15.48/2.54      | v1_funct_1(k2_partfun1(X1,k1_xboole_0,X0,X2)) = iProver_top ),
% 15.48/2.54      inference(superposition,[status(thm)],[c_1,c_1351]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_35150,plain,
% 15.48/2.54      ( k2_partfun1(k1_xboole_0,X0,k2_partfun1(X1,k1_xboole_0,X2,X3),X4) = k7_relat_1(k2_partfun1(X1,k1_xboole_0,X2,X3),X4)
% 15.48/2.54      | m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 15.48/2.54      | v1_funct_1(X2) != iProver_top ),
% 15.48/2.54      inference(forward_subsumption_resolution,[status(thm)],[c_5120,c_2761]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_35153,plain,
% 15.48/2.54      ( k2_partfun1(k1_xboole_0,X0,k2_partfun1(X1,k1_xboole_0,sK3,X2),X3) = k7_relat_1(k2_partfun1(X1,k1_xboole_0,sK3,X2),X3)
% 15.48/2.54      | sK1 = k1_xboole_0
% 15.48/2.54      | r1_tarski(sK0,k1_xboole_0) != iProver_top
% 15.48/2.54      | v1_funct_1(sK3) != iProver_top ),
% 15.48/2.54      inference(superposition,[status(thm)],[c_5610,c_35150]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_25,negated_conjecture,
% 15.48/2.54      ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
% 15.48/2.54      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 15.48/2.54      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
% 15.48/2.54      inference(cnf_transformation,[],[f75]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_505,plain,
% 15.48/2.54      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 15.48/2.54      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 15.48/2.54      | k2_partfun1(sK0,sK1,sK3,sK2) != sK3
% 15.48/2.54      | sK2 != sK0
% 15.48/2.54      | sK1 != sK1 ),
% 15.48/2.54      inference(resolution_lifted,[status(thm)],[c_25,c_29]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_1604,plain,
% 15.48/2.54      ( sK2 != X0 | sK2 = sK0 | sK0 != X0 ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_775]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_1605,plain,
% 15.48/2.54      ( sK2 = sK0 | sK2 != k1_xboole_0 | sK0 != k1_xboole_0 ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_1604]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_1679,plain,
% 15.48/2.54      ( ~ r1_tarski(sK3,k1_xboole_0) | k1_xboole_0 = sK3 ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_0]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_1689,plain,
% 15.48/2.54      ( ~ r1_tarski(sK2,k1_xboole_0) | k1_xboole_0 = sK2 ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_0]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_1636,plain,
% 15.48/2.54      ( r1_tarski(X0,X1) | ~ r1_tarski(sK2,sK0) | X0 != sK2 | X1 != sK0 ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_776]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_1694,plain,
% 15.48/2.54      ( r1_tarski(sK2,X0) | ~ r1_tarski(sK2,sK0) | X0 != sK0 | sK2 != sK2 ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_1636]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_1697,plain,
% 15.48/2.54      ( ~ r1_tarski(sK2,sK0)
% 15.48/2.54      | r1_tarski(sK2,k1_xboole_0)
% 15.48/2.54      | sK2 != sK2
% 15.48/2.54      | k1_xboole_0 != sK0 ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_1694]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_1695,plain,
% 15.48/2.54      ( sK2 = sK2 ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_774]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_1706,plain,
% 15.48/2.54      ( sK3 = sK3 ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_774]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_1800,plain,
% 15.48/2.54      ( sK1 = sK1 ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_774]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_1602,plain,
% 15.48/2.54      ( sK2 != X0 | sK2 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_775]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_1805,plain,
% 15.48/2.54      ( sK2 != sK2 | sK2 = k1_xboole_0 | k1_xboole_0 != sK2 ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_1602]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_1840,plain,
% 15.48/2.54      ( ~ r1_tarski(sK0,k1_xboole_0) | k1_xboole_0 = sK0 ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_0]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_1843,plain,
% 15.48/2.54      ( k1_xboole_0 = sK0 | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
% 15.48/2.54      inference(predicate_to_equality,[status(thm)],[c_1840]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_1901,plain,
% 15.48/2.54      ( v1_relat_1(k1_xboole_0) ),
% 15.48/2.54      inference(predicate_to_equality_rev,[status(thm)],[c_1899]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_1671,plain,
% 15.48/2.54      ( r1_tarski(X0,X1)
% 15.48/2.54      | ~ r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))
% 15.48/2.54      | X1 != k2_zfmisc_1(sK0,sK1)
% 15.48/2.54      | X0 != sK3 ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_776]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_1913,plain,
% 15.48/2.54      ( r1_tarski(sK3,X0)
% 15.48/2.54      | ~ r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))
% 15.48/2.54      | X0 != k2_zfmisc_1(sK0,sK1)
% 15.48/2.54      | sK3 != sK3 ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_1671]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_1915,plain,
% 15.48/2.54      ( ~ r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))
% 15.48/2.54      | r1_tarski(sK3,k1_xboole_0)
% 15.48/2.54      | sK3 != sK3
% 15.48/2.54      | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_1913]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_1983,plain,
% 15.48/2.54      ( X0 != X1 | X0 = k2_zfmisc_1(X2,X3) | k2_zfmisc_1(X2,X3) != X1 ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_775]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_1984,plain,
% 15.48/2.54      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 15.48/2.54      | k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
% 15.48/2.54      | k1_xboole_0 != k1_xboole_0 ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_1983]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_1631,plain,
% 15.48/2.54      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 15.48/2.54      | v1_funct_1(k2_partfun1(X0,X1,sK3,X2))
% 15.48/2.54      | ~ v1_funct_1(sK3) ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_23]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_1860,plain,
% 15.48/2.54      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 15.48/2.54      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
% 15.48/2.54      | ~ v1_funct_1(sK3) ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_1631]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_2031,plain,
% 15.48/2.54      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 15.48/2.54      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 15.48/2.54      | ~ v1_funct_1(sK3) ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_1860]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_2198,plain,
% 15.48/2.54      ( r1_tarski(k1_xboole_0,k1_xboole_0) | ~ v1_relat_1(k1_xboole_0) ),
% 15.48/2.54      inference(predicate_to_equality_rev,[status(thm)],[c_2197]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_2328,plain,
% 15.48/2.54      ( r1_tarski(k1_relat_1(k1_xboole_0),X0) = iProver_top
% 15.48/2.54      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 15.48/2.54      inference(superposition,[status(thm)],[c_2193,c_1357]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_2593,plain,
% 15.48/2.54      ( r1_tarski(k1_relat_1(k1_xboole_0),X0) = iProver_top ),
% 15.48/2.54      inference(global_propositional_subsumption,[status(thm)],[c_2328,c_1899]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_2600,plain,
% 15.48/2.54      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 15.48/2.54      inference(superposition,[status(thm)],[c_2593,c_1361]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_1919,plain,
% 15.48/2.54      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_775]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_2724,plain,
% 15.48/2.54      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_1919]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_2725,plain,
% 15.48/2.54      ( sK3 != sK3 | sK3 = k1_xboole_0 | k1_xboole_0 != sK3 ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_2724]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_3571,plain,
% 15.48/2.54      ( r1_tarski(sK0,k1_xboole_0)
% 15.48/2.54      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 15.48/2.54      | sK0 != k1_xboole_0
% 15.48/2.54      | k1_xboole_0 != k1_xboole_0 ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_3569]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_4431,plain,
% 15.48/2.54      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 15.48/2.54      | ~ v1_funct_1(sK3)
% 15.48/2.54      | k2_partfun1(sK0,sK1,sK3,k1_xboole_0) = k7_relat_1(sK3,k1_xboole_0) ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_4429]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_777,plain,
% 15.48/2.54      ( X0 != X1 | X2 != X3 | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
% 15.48/2.54      theory(equality) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_4885,plain,
% 15.48/2.54      ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(X0,X1) | sK1 != X1 | sK0 != X0 ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_777]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_4887,plain,
% 15.48/2.54      ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
% 15.48/2.54      | sK1 != k1_xboole_0
% 15.48/2.54      | sK0 != k1_xboole_0 ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_4885]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_5616,plain,
% 15.48/2.54      ( sK1 = k1_xboole_0
% 15.48/2.54      | r1_tarski(sK3,k1_xboole_0) = iProver_top
% 15.48/2.54      | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
% 15.48/2.54      inference(superposition,[status(thm)],[c_5610,c_1359]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_5673,plain,
% 15.48/2.54      ( r1_tarski(sK3,k1_xboole_0)
% 15.48/2.54      | ~ r1_tarski(sK0,k1_xboole_0)
% 15.48/2.54      | sK1 = k1_xboole_0 ),
% 15.48/2.54      inference(predicate_to_equality_rev,[status(thm)],[c_5616]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_1943,plain,
% 15.48/2.54      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_774]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_6381,plain,
% 15.48/2.54      ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) = k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_1943]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_5428,plain,
% 15.48/2.54      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 15.48/2.54      | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),k1_xboole_0) != iProver_top
% 15.48/2.54      | v1_relat_1(k7_relat_1(sK3,X0)) != iProver_top ),
% 15.48/2.54      inference(superposition,[status(thm)],[c_4891,c_4200]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_7436,plain,
% 15.48/2.54      ( r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),k1_xboole_0) != iProver_top
% 15.48/2.54      | m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 15.48/2.54      inference(global_propositional_subsumption,
% 15.48/2.54                [status(thm)],
% 15.48/2.54                [c_5428,c_2097,c_4853]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_7437,plain,
% 15.48/2.54      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 15.48/2.54      | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),k1_xboole_0) != iProver_top ),
% 15.48/2.54      inference(renaming,[status(thm)],[c_7436]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_7444,plain,
% 15.48/2.54      ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 15.48/2.54      | v1_relat_1(sK3) != iProver_top ),
% 15.48/2.54      inference(superposition,[status(thm)],[c_1357,c_7437]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_7787,plain,
% 15.48/2.54      ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 15.48/2.54      inference(global_propositional_subsumption,
% 15.48/2.54                [status(thm)],
% 15.48/2.54                [c_7444,c_33,c_1570,c_2003,c_2097]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_7792,plain,
% 15.48/2.54      ( r1_tarski(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 15.48/2.54      inference(superposition,[status(thm)],[c_7787,c_1359]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_7823,plain,
% 15.48/2.54      ( r1_tarski(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0) ),
% 15.48/2.54      inference(predicate_to_equality_rev,[status(thm)],[c_7792]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_7913,plain,
% 15.48/2.54      ( k7_relat_1(sK3,k1_xboole_0) = k1_xboole_0 ),
% 15.48/2.54      inference(superposition,[status(thm)],[c_7792,c_1361]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_7951,plain,
% 15.48/2.54      ( r1_tarski(k2_relat_1(k1_xboole_0),sK1) = iProver_top ),
% 15.48/2.54      inference(superposition,[status(thm)],[c_7913,c_4891]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_7991,plain,
% 15.48/2.54      ( r1_tarski(k2_relat_1(k1_xboole_0),sK1) ),
% 15.48/2.54      inference(predicate_to_equality_rev,[status(thm)],[c_7951]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_5752,plain,
% 15.48/2.54      ( X0 != X1 | X0 = k2_zfmisc_1(sK0,sK1) | k2_zfmisc_1(sK0,sK1) != X1 ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_1983]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_8690,plain,
% 15.48/2.54      ( X0 != k2_zfmisc_1(X1,X2)
% 15.48/2.54      | X0 = k2_zfmisc_1(sK0,sK1)
% 15.48/2.54      | k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X1,X2) ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_5752]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_8692,plain,
% 15.48/2.54      ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
% 15.48/2.54      | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
% 15.48/2.54      | k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,k1_xboole_0) ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_8690]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_4419,plain,
% 15.48/2.54      ( X0 != X1
% 15.48/2.54      | k2_partfun1(sK0,sK1,sK3,X2) != X1
% 15.48/2.54      | k2_partfun1(sK0,sK1,sK3,X2) = X0 ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_775]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_8806,plain,
% 15.48/2.54      ( X0 != k7_relat_1(sK3,X1)
% 15.48/2.54      | k2_partfun1(sK0,sK1,sK3,X1) = X0
% 15.48/2.54      | k2_partfun1(sK0,sK1,sK3,X1) != k7_relat_1(sK3,X1) ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_4419]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_8807,plain,
% 15.48/2.54      ( k2_partfun1(sK0,sK1,sK3,k1_xboole_0) != k7_relat_1(sK3,k1_xboole_0)
% 15.48/2.54      | k2_partfun1(sK0,sK1,sK3,k1_xboole_0) = k1_xboole_0
% 15.48/2.54      | k1_xboole_0 != k7_relat_1(sK3,k1_xboole_0) ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_8806]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_11804,plain,
% 15.48/2.54      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 15.48/2.54      | ~ r1_tarski(k1_relat_1(X0),sK2)
% 15.48/2.54      | ~ r1_tarski(k2_relat_1(X0),sK1)
% 15.48/2.54      | ~ v1_relat_1(X0) ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_15]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_11806,plain,
% 15.48/2.54      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 15.48/2.54      | ~ r1_tarski(k1_relat_1(k1_xboole_0),sK2)
% 15.48/2.54      | ~ r1_tarski(k2_relat_1(k1_xboole_0),sK1)
% 15.48/2.54      | ~ v1_relat_1(k1_xboole_0) ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_11804]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_13058,plain,
% 15.48/2.54      ( ~ r1_tarski(k7_relat_1(sK3,X0),k1_xboole_0)
% 15.48/2.54      | k1_xboole_0 = k7_relat_1(sK3,X0) ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_0]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_13060,plain,
% 15.48/2.54      ( ~ r1_tarski(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0)
% 15.48/2.54      | k1_xboole_0 = k7_relat_1(sK3,k1_xboole_0) ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_13058]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_779,plain,
% 15.48/2.54      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 15.48/2.54      theory(equality) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_2166,plain,
% 15.48/2.54      ( m1_subset_1(X0,X1)
% 15.48/2.54      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
% 15.48/2.54      | X0 != X2
% 15.48/2.54      | X1 != k1_zfmisc_1(X3) ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_779]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_4173,plain,
% 15.48/2.54      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.48/2.54      | m1_subset_1(X2,k1_zfmisc_1(X1))
% 15.48/2.54      | X2 != X0
% 15.48/2.54      | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_2166]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_8492,plain,
% 15.48/2.54      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 15.48/2.54      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 15.48/2.54      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 15.48/2.54      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_4173]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_17176,plain,
% 15.48/2.54      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 15.48/2.54      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 15.48/2.54      | k2_partfun1(sK0,sK1,sK3,sK2) != k2_partfun1(sK0,sK1,sK3,X0)
% 15.48/2.54      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_8492]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_17182,plain,
% 15.48/2.54      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 15.48/2.54      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 15.48/2.54      | k2_partfun1(sK0,sK1,sK3,sK2) != k2_partfun1(sK0,sK1,sK3,k1_xboole_0)
% 15.48/2.54      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_17176]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_783,plain,
% 15.48/2.54      ( X0 != X1
% 15.48/2.54      | X2 != X3
% 15.48/2.54      | X4 != X5
% 15.48/2.54      | X6 != X7
% 15.48/2.54      | k2_partfun1(X0,X2,X4,X6) = k2_partfun1(X1,X3,X5,X7) ),
% 15.48/2.54      theory(equality) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_2271,plain,
% 15.48/2.54      ( X0 != X1
% 15.48/2.54      | X2 != sK3
% 15.48/2.54      | X3 != sK1
% 15.48/2.54      | X4 != sK0
% 15.48/2.54      | k2_partfun1(X4,X3,X2,X0) = k2_partfun1(sK0,sK1,sK3,X1) ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_783]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_4704,plain,
% 15.48/2.54      ( X0 != X1
% 15.48/2.54      | X2 != sK1
% 15.48/2.54      | X3 != sK0
% 15.48/2.54      | k2_partfun1(X3,X2,sK3,X0) = k2_partfun1(sK0,sK1,sK3,X1)
% 15.48/2.54      | sK3 != sK3 ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_2271]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_6977,plain,
% 15.48/2.54      ( X0 != X1
% 15.48/2.54      | X2 != sK0
% 15.48/2.54      | k2_partfun1(X2,sK1,sK3,X0) = k2_partfun1(sK0,sK1,sK3,X1)
% 15.48/2.54      | sK3 != sK3
% 15.48/2.54      | sK1 != sK1 ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_4704]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_22390,plain,
% 15.48/2.54      ( k2_partfun1(sK0,sK1,sK3,sK2) = k2_partfun1(sK0,sK1,sK3,X0)
% 15.48/2.54      | sK2 != X0
% 15.48/2.54      | sK3 != sK3
% 15.48/2.54      | sK1 != sK1
% 15.48/2.54      | sK0 != sK0 ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_6977]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_22394,plain,
% 15.48/2.54      ( k2_partfun1(sK0,sK1,sK3,sK2) = k2_partfun1(sK0,sK1,sK3,k1_xboole_0)
% 15.48/2.54      | sK2 != k1_xboole_0
% 15.48/2.54      | sK3 != sK3
% 15.48/2.54      | sK1 != sK1
% 15.48/2.54      | sK0 != sK0 ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_22390]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_8523,plain,
% 15.48/2.54      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.48/2.54      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.48/2.54      | k2_partfun1(sK0,sK1,sK3,X3) != X0
% 15.48/2.54      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_4173]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_31705,plain,
% 15.48/2.54      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 15.48/2.54      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,X1),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 15.48/2.54      | k2_partfun1(sK0,sK1,sK3,X1) != X0
% 15.48/2.54      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_8523]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_31707,plain,
% 15.48/2.54      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 15.48/2.54      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 15.48/2.54      | k2_partfun1(sK0,sK1,sK3,k1_xboole_0) != k1_xboole_0
% 15.48/2.54      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_31705]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_32681,plain,
% 15.48/2.54      ( ~ r1_tarski(X0,X1)
% 15.48/2.54      | r1_tarski(k1_relat_1(X2),sK2)
% 15.48/2.54      | k1_relat_1(X2) != X0
% 15.48/2.54      | sK2 != X1 ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_776]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_32683,plain,
% 15.48/2.54      ( r1_tarski(k1_relat_1(k1_xboole_0),sK2)
% 15.48/2.54      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 15.48/2.54      | k1_relat_1(k1_xboole_0) != k1_xboole_0
% 15.48/2.54      | sK2 != k1_xboole_0 ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_32681]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_2268,plain,
% 15.48/2.54      ( X0 != X1
% 15.48/2.54      | X0 = k2_partfun1(sK0,sK1,sK3,X2)
% 15.48/2.54      | k2_partfun1(sK0,sK1,sK3,X2) != X1 ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_775]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_35476,plain,
% 15.48/2.54      ( k2_partfun1(sK0,sK1,sK3,X0) != X1
% 15.48/2.54      | sK3 != X1
% 15.48/2.54      | sK3 = k2_partfun1(sK0,sK1,sK3,X0) ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_2268]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_35517,plain,
% 15.48/2.54      ( k2_partfun1(sK0,sK1,sK3,k1_xboole_0) != k1_xboole_0
% 15.48/2.54      | sK3 = k2_partfun1(sK0,sK1,sK3,k1_xboole_0)
% 15.48/2.54      | sK3 != k1_xboole_0 ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_35476]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_1685,plain,
% 15.48/2.54      ( X0 != X1 | X0 = sK3 | sK3 != X1 ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_775]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_12760,plain,
% 15.48/2.54      ( k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 15.48/2.54      | k2_partfun1(sK0,sK1,sK3,sK2) = sK3
% 15.48/2.54      | sK3 != X0 ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_1685]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_35509,plain,
% 15.48/2.54      ( k2_partfun1(sK0,sK1,sK3,sK2) != k2_partfun1(sK0,sK1,sK3,X0)
% 15.48/2.54      | k2_partfun1(sK0,sK1,sK3,sK2) = sK3
% 15.48/2.54      | sK3 != k2_partfun1(sK0,sK1,sK3,X0) ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_12760]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_35533,plain,
% 15.48/2.54      ( k2_partfun1(sK0,sK1,sK3,sK2) != k2_partfun1(sK0,sK1,sK3,k1_xboole_0)
% 15.48/2.54      | k2_partfun1(sK0,sK1,sK3,sK2) = sK3
% 15.48/2.54      | sK3 != k2_partfun1(sK0,sK1,sK3,k1_xboole_0) ),
% 15.48/2.54      inference(instantiation,[status(thm)],[c_35509]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_35940,plain,
% 15.48/2.54      ( r1_tarski(sK0,k1_xboole_0) != iProver_top ),
% 15.48/2.54      inference(global_propositional_subsumption,
% 15.48/2.54                [status(thm)],
% 15.48/2.54                [c_35153,c_30,c_28,c_27,c_97,c_98,c_505,c_1569,c_1605,c_1679,
% 15.48/2.54                 c_1689,c_1697,c_1695,c_1706,c_1800,c_1805,c_1806,c_1807,
% 15.48/2.54                 c_1843,c_1901,c_1915,c_1984,c_2031,c_2198,c_2600,c_2725,
% 15.48/2.54                 c_3571,c_4431,c_4887,c_5673,c_6381,c_7823,c_7991,c_8692,
% 15.48/2.54                 c_8807,c_11806,c_13060,c_17182,c_22394,c_31707,c_32683,
% 15.48/2.54                 c_35517,c_35533]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_48459,plain,
% 15.48/2.54      ( k1_relset_1(X0,X1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
% 15.48/2.54      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1) != iProver_top
% 15.48/2.54      | r1_tarski(sK2,X0) != iProver_top
% 15.48/2.54      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 15.48/2.54      inference(global_propositional_subsumption,
% 15.48/2.54                [status(thm)],
% 15.48/2.54                [c_46839,c_30,c_28,c_27,c_26,c_97,c_98,c_505,c_1569,c_1605,
% 15.48/2.54                 c_1679,c_1689,c_1697,c_1695,c_1706,c_1800,c_1805,c_1806,
% 15.48/2.54                 c_1807,c_1855,c_1901,c_1915,c_1984,c_2031,c_2198,c_2600,
% 15.48/2.54                 c_2725,c_3571,c_4431,c_4887,c_5673,c_6381,c_7823,c_7991,
% 15.48/2.54                 c_8692,c_8807,c_11806,c_13060,c_17182,c_22394,c_31707,
% 15.48/2.54                 c_32683,c_35517,c_35533]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_7367,plain,
% 15.48/2.54      ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 15.48/2.54      inference(global_propositional_subsumption,[status(thm)],[c_4853,c_2097]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_48469,plain,
% 15.48/2.54      ( k1_relset_1(X0,X1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
% 15.48/2.54      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X1) != iProver_top
% 15.48/2.54      | r1_tarski(sK2,X0) != iProver_top ),
% 15.48/2.54      inference(forward_subsumption_resolution,[status(thm)],[c_48459,c_7367]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_48476,plain,
% 15.48/2.54      ( k1_relset_1(X0,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
% 15.48/2.54      | r1_tarski(sK2,X0) != iProver_top ),
% 15.48/2.54      inference(superposition,[status(thm)],[c_4891,c_48469]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_63014,plain,
% 15.48/2.54      ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
% 15.48/2.54      | sK1 = k1_xboole_0 ),
% 15.48/2.54      inference(superposition,[status(thm)],[c_3445,c_48476]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_63107,plain,
% 15.48/2.54      ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2)) ),
% 15.48/2.54      inference(global_propositional_subsumption,
% 15.48/2.54                [status(thm)],
% 15.48/2.54                [c_63014,c_30,c_28,c_27,c_26,c_97,c_98,c_505,c_1569,c_1605,
% 15.48/2.54                 c_1679,c_1689,c_1697,c_1695,c_1706,c_1800,c_1805,c_1806,
% 15.48/2.54                 c_1807,c_1855,c_1901,c_1915,c_1984,c_2031,c_2198,c_2600,
% 15.48/2.54                 c_2725,c_3571,c_4431,c_4887,c_5673,c_6381,c_7823,c_7991,
% 15.48/2.54                 c_8692,c_8807,c_11806,c_13060,c_17182,c_22394,c_31707,
% 15.48/2.54                 c_32683,c_35517,c_35533]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_19,plain,
% 15.48/2.54      ( v1_funct_2(X0,X1,X2)
% 15.48/2.54      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.48/2.54      | k1_relset_1(X1,X2,X0) != X1
% 15.48/2.54      | k1_xboole_0 = X2 ),
% 15.48/2.54      inference(cnf_transformation,[],[f63]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_478,plain,
% 15.48/2.54      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.48/2.54      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 15.48/2.54      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 15.48/2.54      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 15.48/2.54      | k1_relset_1(X1,X2,X0) != X1
% 15.48/2.54      | sK2 != X1
% 15.48/2.54      | sK1 != X2
% 15.48/2.54      | k1_xboole_0 = X2 ),
% 15.48/2.54      inference(resolution_lifted,[status(thm)],[c_19,c_25]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_479,plain,
% 15.48/2.54      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 15.48/2.54      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 15.48/2.54      | k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 15.48/2.54      | k1_xboole_0 = sK1 ),
% 15.48/2.54      inference(unflattening,[status(thm)],[c_478]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_1340,plain,
% 15.48/2.54      ( k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 15.48/2.54      | k1_xboole_0 = sK1
% 15.48/2.54      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 15.48/2.54      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 15.48/2.54      inference(predicate_to_equality,[status(thm)],[c_479]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_4643,plain,
% 15.48/2.54      ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) != sK2
% 15.48/2.54      | sK1 = k1_xboole_0
% 15.48/2.54      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 15.48/2.54      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 15.48/2.54      inference(demodulation,[status(thm)],[c_4637,c_1340]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_2760,plain,
% 15.48/2.54      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
% 15.48/2.54      | v1_funct_1(sK3) != iProver_top ),
% 15.48/2.54      inference(superposition,[status(thm)],[c_1348,c_1351]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_1861,plain,
% 15.48/2.54      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 15.48/2.54      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
% 15.48/2.54      | v1_funct_1(sK3) != iProver_top ),
% 15.48/2.54      inference(predicate_to_equality,[status(thm)],[c_1860]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_3209,plain,
% 15.48/2.54      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
% 15.48/2.54      inference(global_propositional_subsumption,
% 15.48/2.54                [status(thm)],
% 15.48/2.54                [c_2760,c_31,c_33,c_1861]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_4644,plain,
% 15.48/2.54      ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 15.48/2.54      inference(demodulation,[status(thm)],[c_4637,c_3209]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_4651,plain,
% 15.48/2.54      ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) != sK2
% 15.48/2.54      | sK1 = k1_xboole_0
% 15.48/2.54      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 15.48/2.54      inference(forward_subsumption_resolution,[status(thm)],[c_4643,c_4644]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_63110,plain,
% 15.48/2.54      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 15.48/2.54      | sK1 = k1_xboole_0
% 15.48/2.54      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 15.48/2.54      inference(demodulation,[status(thm)],[c_63107,c_4651]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_65217,plain,
% 15.48/2.54      ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 15.48/2.54      inference(global_propositional_subsumption,
% 15.48/2.54                [status(thm)],
% 15.48/2.54                [c_63110,c_30,c_28,c_27,c_26,c_97,c_98,c_505,c_1569,c_1605,
% 15.48/2.54                 c_1679,c_1689,c_1697,c_1695,c_1706,c_1800,c_1805,c_1806,
% 15.48/2.54                 c_1807,c_1855,c_1901,c_1915,c_1984,c_2031,c_2198,c_2600,
% 15.48/2.54                 c_2725,c_3257,c_3571,c_4431,c_4887,c_5673,c_6381,c_7823,
% 15.48/2.54                 c_7991,c_8692,c_8807,c_11806,c_13060,c_17182,c_22394,c_31707,
% 15.48/2.54                 c_32683,c_35517,c_35533]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_65223,plain,
% 15.48/2.54      ( r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) != iProver_top
% 15.48/2.54      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
% 15.48/2.54      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 15.48/2.54      inference(superposition,[status(thm)],[c_1353,c_65217]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_2301,plain,
% 15.48/2.54      ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 15.48/2.54      inference(superposition,[status(thm)],[c_1348,c_1359]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_2356,plain,
% 15.48/2.54      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 15.48/2.54      | v1_relat_1(sK3) = iProver_top ),
% 15.48/2.54      inference(superposition,[status(thm)],[c_2301,c_1346]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_2383,plain,
% 15.48/2.54      ( v1_relat_1(sK3) = iProver_top ),
% 15.48/2.54      inference(global_propositional_subsumption,
% 15.48/2.54                [status(thm)],
% 15.48/2.54                [c_2356,c_33,c_1570,c_2003,c_2097]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_2203,plain,
% 15.48/2.54      ( v1_relat_1(X0) != iProver_top
% 15.48/2.54      | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
% 15.48/2.54      inference(superposition,[status(thm)],[c_1356,c_1346]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_3424,plain,
% 15.48/2.54      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),X0)) = X0
% 15.48/2.54      | sK1 = k1_xboole_0
% 15.48/2.54      | r1_tarski(X0,sK2) != iProver_top
% 15.48/2.54      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 15.48/2.54      inference(superposition,[status(thm)],[c_3257,c_1355]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_3491,plain,
% 15.48/2.54      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),X0)) = X0
% 15.48/2.54      | sK1 = k1_xboole_0
% 15.48/2.54      | r1_tarski(X0,sK2) != iProver_top
% 15.48/2.54      | v1_relat_1(sK3) != iProver_top ),
% 15.48/2.54      inference(superposition,[status(thm)],[c_2203,c_3424]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_3977,plain,
% 15.48/2.54      ( r1_tarski(X0,sK2) != iProver_top
% 15.48/2.54      | sK1 = k1_xboole_0
% 15.48/2.54      | k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),X0)) = X0 ),
% 15.48/2.54      inference(global_propositional_subsumption,
% 15.48/2.54                [status(thm)],
% 15.48/2.54                [c_3491,c_33,c_1570,c_2003,c_2097]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_3978,plain,
% 15.48/2.54      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),X0)) = X0
% 15.48/2.54      | sK1 = k1_xboole_0
% 15.48/2.54      | r1_tarski(X0,sK2) != iProver_top ),
% 15.48/2.54      inference(renaming,[status(thm)],[c_3977]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_3986,plain,
% 15.48/2.54      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),k1_relat_1(k7_relat_1(X0,sK2)))) = k1_relat_1(k7_relat_1(X0,sK2))
% 15.48/2.54      | sK1 = k1_xboole_0
% 15.48/2.54      | v1_relat_1(X0) != iProver_top ),
% 15.48/2.54      inference(superposition,[status(thm)],[c_1357,c_3978]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_11634,plain,
% 15.48/2.54      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),k1_relat_1(k7_relat_1(sK3,sK2)))) = k1_relat_1(k7_relat_1(sK3,sK2))
% 15.48/2.54      | sK1 = k1_xboole_0 ),
% 15.48/2.54      inference(superposition,[status(thm)],[c_2383,c_3986]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_11695,plain,
% 15.48/2.54      ( k1_relat_1(k7_relat_1(k7_relat_1(sK3,sK2),sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
% 15.48/2.54      | sK1 = k1_xboole_0 ),
% 15.48/2.54      inference(superposition,[status(thm)],[c_3257,c_11634]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_11915,plain,
% 15.48/2.54      ( sK1 = k1_xboole_0
% 15.48/2.54      | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) = iProver_top
% 15.48/2.54      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 15.48/2.54      inference(superposition,[status(thm)],[c_11695,c_1357]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_12129,plain,
% 15.48/2.54      ( sK1 = k1_xboole_0
% 15.48/2.54      | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) = iProver_top ),
% 15.48/2.54      inference(forward_subsumption_resolution,[status(thm)],[c_11915,c_7367]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_66160,plain,
% 15.48/2.54      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
% 15.48/2.54      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 15.48/2.54      inference(global_propositional_subsumption,
% 15.48/2.54                [status(thm)],
% 15.48/2.54                [c_65223,c_30,c_28,c_27,c_26,c_97,c_98,c_505,c_1569,c_1605,
% 15.48/2.54                 c_1679,c_1689,c_1697,c_1695,c_1706,c_1800,c_1805,c_1806,
% 15.48/2.54                 c_1807,c_1855,c_1901,c_1915,c_1984,c_2031,c_2198,c_2600,
% 15.48/2.54                 c_2725,c_3571,c_4431,c_4887,c_5673,c_6381,c_7823,c_7991,
% 15.48/2.54                 c_8692,c_8807,c_11806,c_12129,c_13060,c_17182,c_22394,
% 15.48/2.54                 c_31707,c_32683,c_35517,c_35533]) ).
% 15.48/2.54  
% 15.48/2.54  cnf(c_66166,plain,
% 15.48/2.54      ( $false ),
% 15.48/2.54      inference(forward_subsumption_resolution,
% 15.48/2.54                [status(thm)],
% 15.48/2.54                [c_66160,c_7367,c_4891]) ).
% 15.48/2.54  
% 15.48/2.54  
% 15.48/2.54  % SZS output end CNFRefutation for theBenchmark.p
% 15.48/2.54  
% 15.48/2.54  ------                               Statistics
% 15.48/2.54  
% 15.48/2.54  ------ General
% 15.48/2.54  
% 15.48/2.54  abstr_ref_over_cycles:                  0
% 15.48/2.54  abstr_ref_under_cycles:                 0
% 15.48/2.54  gc_basic_clause_elim:                   0
% 15.48/2.54  forced_gc_time:                         0
% 15.48/2.54  parsing_time:                           0.011
% 15.48/2.54  unif_index_cands_time:                  0.
% 15.48/2.54  unif_index_add_time:                    0.
% 15.48/2.54  orderings_time:                         0.
% 15.48/2.54  out_proof_time:                         0.022
% 15.48/2.54  total_time:                             1.627
% 15.48/2.54  num_of_symbols:                         49
% 15.48/2.54  num_of_terms:                           44352
% 15.48/2.54  
% 15.48/2.54  ------ Preprocessing
% 15.48/2.54  
% 15.48/2.54  num_of_splits:                          0
% 15.48/2.54  num_of_split_atoms:                     0
% 15.48/2.54  num_of_reused_defs:                     0
% 15.48/2.54  num_eq_ax_congr_red:                    13
% 15.48/2.54  num_of_sem_filtered_clauses:            1
% 15.48/2.54  num_of_subtypes:                        0
% 15.48/2.54  monotx_restored_types:                  0
% 15.48/2.54  sat_num_of_epr_types:                   0
% 15.48/2.54  sat_num_of_non_cyclic_types:            0
% 15.48/2.54  sat_guarded_non_collapsed_types:        0
% 15.48/2.54  num_pure_diseq_elim:                    0
% 15.48/2.54  simp_replaced_by:                       0
% 15.48/2.54  res_preprocessed:                       138
% 15.48/2.54  prep_upred:                             0
% 15.48/2.54  prep_unflattend:                        33
% 15.48/2.54  smt_new_axioms:                         0
% 15.48/2.54  pred_elim_cands:                        4
% 15.48/2.54  pred_elim:                              2
% 15.48/2.54  pred_elim_cl:                           3
% 15.48/2.54  pred_elim_cycles:                       4
% 15.48/2.54  merged_defs:                            8
% 15.48/2.54  merged_defs_ncl:                        0
% 15.48/2.54  bin_hyper_res:                          9
% 15.48/2.54  prep_cycles:                            4
% 15.48/2.54  pred_elim_time:                         0.003
% 15.48/2.54  splitting_time:                         0.
% 15.48/2.54  sem_filter_time:                        0.
% 15.48/2.54  monotx_time:                            0.
% 15.48/2.54  subtype_inf_time:                       0.
% 15.48/2.54  
% 15.48/2.54  ------ Problem properties
% 15.48/2.54  
% 15.48/2.54  clauses:                                28
% 15.48/2.54  conjectures:                            4
% 15.48/2.54  epr:                                    5
% 15.48/2.54  horn:                                   25
% 15.48/2.54  ground:                                 11
% 15.48/2.54  unary:                                  6
% 15.48/2.54  binary:                                 8
% 15.48/2.54  lits:                                   73
% 15.48/2.54  lits_eq:                                27
% 15.48/2.54  fd_pure:                                0
% 15.48/2.54  fd_pseudo:                              0
% 15.48/2.54  fd_cond:                                2
% 15.48/2.54  fd_pseudo_cond:                         0
% 15.48/2.54  ac_symbols:                             0
% 15.48/2.54  
% 15.48/2.54  ------ Propositional Solver
% 15.48/2.54  
% 15.48/2.54  prop_solver_calls:                      33
% 15.48/2.54  prop_fast_solver_calls:                 3338
% 15.48/2.54  smt_solver_calls:                       0
% 15.48/2.54  smt_fast_solver_calls:                  0
% 15.48/2.54  prop_num_of_clauses:                    20369
% 15.48/2.54  prop_preprocess_simplified:             35450
% 15.48/2.54  prop_fo_subsumed:                       231
% 15.48/2.54  prop_solver_time:                       0.
% 15.48/2.54  smt_solver_time:                        0.
% 15.48/2.54  smt_fast_solver_time:                   0.
% 15.48/2.54  prop_fast_solver_time:                  0.
% 15.48/2.54  prop_unsat_core_time:                   0.
% 15.48/2.54  
% 15.48/2.54  ------ QBF
% 15.48/2.54  
% 15.48/2.54  qbf_q_res:                              0
% 15.48/2.54  qbf_num_tautologies:                    0
% 15.48/2.54  qbf_prep_cycles:                        0
% 15.48/2.54  
% 15.48/2.54  ------ BMC1
% 15.48/2.54  
% 15.48/2.54  bmc1_current_bound:                     -1
% 15.48/2.54  bmc1_last_solved_bound:                 -1
% 15.48/2.54  bmc1_unsat_core_size:                   -1
% 15.48/2.54  bmc1_unsat_core_parents_size:           -1
% 15.48/2.54  bmc1_merge_next_fun:                    0
% 15.48/2.54  bmc1_unsat_core_clauses_time:           0.
% 15.48/2.54  
% 15.48/2.54  ------ Instantiation
% 15.48/2.54  
% 15.48/2.54  inst_num_of_clauses:                    71
% 15.48/2.54  inst_num_in_passive:                    0
% 15.48/2.54  inst_num_in_active:                     2334
% 15.48/2.54  inst_num_in_unprocessed:                23
% 15.48/2.54  inst_num_of_loops:                      3049
% 15.48/2.54  inst_num_of_learning_restarts:          1
% 15.48/2.54  inst_num_moves_active_passive:          712
% 15.48/2.54  inst_lit_activity:                      0
% 15.48/2.54  inst_lit_activity_moves:                0
% 15.48/2.54  inst_num_tautologies:                   0
% 15.48/2.54  inst_num_prop_implied:                  0
% 15.48/2.54  inst_num_existing_simplified:           0
% 15.48/2.54  inst_num_eq_res_simplified:             0
% 15.48/2.54  inst_num_child_elim:                    0
% 15.48/2.54  inst_num_of_dismatching_blockings:      3894
% 15.48/2.54  inst_num_of_non_proper_insts:           6445
% 15.48/2.54  inst_num_of_duplicates:                 0
% 15.48/2.54  inst_inst_num_from_inst_to_res:         0
% 15.48/2.54  inst_dismatching_checking_time:         0.
% 15.48/2.54  
% 15.48/2.54  ------ Resolution
% 15.48/2.54  
% 15.48/2.54  res_num_of_clauses:                     39
% 15.48/2.54  res_num_in_passive:                     39
% 15.48/2.54  res_num_in_active:                      0
% 15.48/2.54  res_num_of_loops:                       142
% 15.48/2.54  res_forward_subset_subsumed:            127
% 15.48/2.54  res_backward_subset_subsumed:           0
% 15.48/2.54  res_forward_subsumed:                   0
% 15.48/2.54  res_backward_subsumed:                  0
% 15.48/2.54  res_forward_subsumption_resolution:     0
% 15.48/2.54  res_backward_subsumption_resolution:    0
% 15.48/2.54  res_clause_to_clause_subsumption:       9616
% 15.48/2.54  res_orphan_elimination:                 0
% 15.48/2.54  res_tautology_del:                      646
% 15.48/2.54  res_num_eq_res_simplified:              1
% 15.48/2.54  res_num_sel_changes:                    0
% 15.48/2.54  res_moves_from_active_to_pass:          0
% 15.48/2.54  
% 15.48/2.54  ------ Superposition
% 15.48/2.54  
% 15.48/2.54  sup_time_total:                         0.
% 15.48/2.54  sup_time_generating:                    0.
% 15.48/2.54  sup_time_sim_full:                      0.
% 15.48/2.54  sup_time_sim_immed:                     0.
% 15.48/2.54  
% 15.48/2.54  sup_num_of_clauses:                     1871
% 15.48/2.54  sup_num_in_active:                      559
% 15.48/2.54  sup_num_in_passive:                     1312
% 15.48/2.54  sup_num_of_loops:                       608
% 15.48/2.54  sup_fw_superposition:                   1933
% 15.48/2.54  sup_bw_superposition:                   1494
% 15.48/2.54  sup_immediate_simplified:               1182
% 15.48/2.54  sup_given_eliminated:                   4
% 15.48/2.54  comparisons_done:                       0
% 15.48/2.54  comparisons_avoided:                    291
% 15.48/2.54  
% 15.48/2.54  ------ Simplifications
% 15.48/2.54  
% 15.48/2.54  
% 15.48/2.54  sim_fw_subset_subsumed:                 145
% 15.48/2.54  sim_bw_subset_subsumed:                 66
% 15.48/2.54  sim_fw_subsumed:                        157
% 15.48/2.54  sim_bw_subsumed:                        50
% 15.48/2.54  sim_fw_subsumption_res:                 85
% 15.48/2.54  sim_bw_subsumption_res:                 2
% 15.48/2.54  sim_tautology_del:                      110
% 15.48/2.54  sim_eq_tautology_del:                   387
% 15.48/2.54  sim_eq_res_simp:                        0
% 15.48/2.54  sim_fw_demodulated:                     515
% 15.48/2.54  sim_bw_demodulated:                     38
% 15.48/2.54  sim_light_normalised:                   600
% 15.48/2.54  sim_joinable_taut:                      0
% 15.48/2.54  sim_joinable_simp:                      0
% 15.48/2.54  sim_ac_normalised:                      0
% 15.48/2.54  sim_smt_subsumption:                    0
% 15.48/2.54  
%------------------------------------------------------------------------------
