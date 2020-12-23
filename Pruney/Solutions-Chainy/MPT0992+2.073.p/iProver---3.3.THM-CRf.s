%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:04:01 EST 2020

% Result     : Theorem 15.68s
% Output     : CNFRefutation 15.68s
% Verified   : 
% Statistics : Number of formulae       :  208 (1776 expanded)
%              Number of clauses        :  139 ( 678 expanded)
%              Number of leaves         :   18 ( 318 expanded)
%              Depth                    :   28
%              Number of atoms          :  615 (8391 expanded)
%              Number of equality atoms :  366 (2711 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
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

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

fof(f45,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f51,plain,
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

fof(f52,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f46,f51])).

fof(f84,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f52])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f43])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f82,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f85,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f52])).

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
    inference(ennf_transformation,[],[f16])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f40])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f83,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f37])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f87,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f52])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f93,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f76])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f47])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f89,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f56])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f90,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f78])).

fof(f91,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f90])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f88,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f57])).

fof(f86,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f52])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f2,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f54,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1511,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1514,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2656,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1511,c_1514])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1513,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2270,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1511,c_1513])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_35,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_2517,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2270,c_35])).

cnf(c_2659,plain,
    ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2656,c_2517])).

cnf(c_2936,plain,
    ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2659,c_35])).

cnf(c_31,negated_conjecture,
    ( r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1512,plain,
    ( r1_tarski(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_33,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_518,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X0
    | sK1 != X2
    | sK0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_33])).

cnf(c_519,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_518])).

cnf(c_521,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_519,c_32])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1517,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2810,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1511,c_1517])).

cnf(c_2870,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_521,c_2810])).

cnf(c_16,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1519,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3439,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2870,c_1519])).

cnf(c_12,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1523,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1528,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2357,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1511,c_1528])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_5,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_246,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_5])).

cnf(c_247,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_246])).

cnf(c_308,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_7,c_247])).

cnf(c_1509,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_308])).

cnf(c_2426,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2357,c_1509])).

cnf(c_2529,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1523,c_2426])).

cnf(c_3971,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | sK1 = k1_xboole_0
    | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3439,c_2529])).

cnf(c_3972,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3971])).

cnf(c_3977,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1512,c_3972])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1515,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3215,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2517,c_1515])).

cnf(c_37,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_3945,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3215,c_35,c_37])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1516,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) = iProver_top
    | r1_tarski(k1_relat_1(X0),X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4043,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3945,c_1516])).

cnf(c_7265,plain,
    ( k2_partfun1(X0,sK1,k7_relat_1(sK3,X1),X2) = k7_relat_1(k7_relat_1(sK3,X1),X2)
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,X1)),X0) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4043,c_1513])).

cnf(c_49839,plain,
    ( k2_partfun1(X0,sK1,k7_relat_1(sK3,sK2),X1) = k7_relat_1(k7_relat_1(sK3,sK2),X1)
    | sK1 = k1_xboole_0
    | r1_tarski(sK2,X0) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3977,c_7265])).

cnf(c_14,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1521,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_7264,plain,
    ( k1_relset_1(X0,sK1,k7_relat_1(sK3,X1)) = k1_relat_1(k7_relat_1(sK3,X1))
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,X1)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4043,c_1517])).

cnf(c_21102,plain,
    ( k1_relset_1(X0,sK1,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0))
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1521,c_7264])).

cnf(c_21912,plain,
    ( k1_relset_1(X0,sK1,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_21102,c_2529])).

cnf(c_23,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_29,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_502,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_relset_1(X1,X2,X0) != X1
    | sK2 != X1
    | sK1 != X2
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_29])).

cnf(c_503,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_502])).

cnf(c_1504,plain,
    ( k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | k1_xboole_0 = sK1
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_503])).

cnf(c_2523,plain,
    ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) != sK2
    | sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2517,c_1504])).

cnf(c_21915,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_21912,c_2523])).

cnf(c_22164,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_21915,c_3977])).

cnf(c_22171,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4043,c_22164])).

cnf(c_47544,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_47546,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47544])).

cnf(c_50215,plain,
    ( sK1 = k1_xboole_0
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_49839,c_2529,c_22171,c_47546])).

cnf(c_50219,plain,
    ( sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2936,c_50215])).

cnf(c_22,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_470,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | sK2 != k1_xboole_0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_29])).

cnf(c_471,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_470])).

cnf(c_1506,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_471])).

cnf(c_3,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1535,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1506,c_3])).

cnf(c_2520,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k7_relat_1(sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2517,c_1535])).

cnf(c_50606,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_50219,c_2520])).

cnf(c_20,plain,
    ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_424,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK2 != X0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_29])).

cnf(c_425,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_424])).

cnf(c_1508,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_425])).

cnf(c_2,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1534,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1508,c_2])).

cnf(c_2521,plain,
    ( k7_relat_1(sK3,sK2) != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2517,c_1534])).

cnf(c_30,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_106,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_107,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_845,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1574,plain,
    ( sK2 != X0
    | sK2 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_845])).

cnf(c_1581,plain,
    ( sK2 != sK2
    | sK2 = k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_1574])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1590,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_844,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1617,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_844])).

cnf(c_846,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1625,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_846])).

cnf(c_1872,plain,
    ( ~ r1_tarski(sK2,X0)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != sK2
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1625])).

cnf(c_2371,plain,
    ( ~ r1_tarski(sK2,sK0)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != sK2
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1872])).

cnf(c_2465,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_845])).

cnf(c_2466,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2465])).

cnf(c_2608,plain,
    ( sK1 != k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2521,c_31,c_30,c_106,c_107,c_1581,c_1590,c_1617,c_2371,c_2466])).

cnf(c_2609,plain,
    ( sK2 = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_2608])).

cnf(c_50607,plain,
    ( sK2 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_50219,c_2609])).

cnf(c_50627,plain,
    ( sK2 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_50607])).

cnf(c_50631,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_50606,c_50627])).

cnf(c_50632,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_50631])).

cnf(c_7259,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_4043])).

cnf(c_7424,plain,
    ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1521,c_7259])).

cnf(c_9153,plain,
    ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7424,c_2529])).

cnf(c_9157,plain,
    ( r1_tarski(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_9153,c_1528])).

cnf(c_1530,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_9641,plain,
    ( k7_relat_1(sK3,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9157,c_1530])).

cnf(c_50633,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_50632,c_9641])).

cnf(c_15,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1520,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2265,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1520,c_1530])).

cnf(c_1905,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_1523])).

cnf(c_3011,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2265,c_1905])).

cnf(c_3014,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),X0) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3011,c_1521])).

cnf(c_6963,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3014,c_1905])).

cnf(c_2418,plain,
    ( k1_relat_1(k7_relat_1(X0,k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1521,c_1530])).

cnf(c_3087,plain,
    ( k1_relat_1(k7_relat_1(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1905,c_2418])).

cnf(c_3089,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3087,c_3011])).

cnf(c_6969,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6963,c_3089])).

cnf(c_1529,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2812,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_1517])).

cnf(c_3248,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
    | r1_tarski(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1529,c_2812])).

cnf(c_8219,plain,
    ( k1_relset_1(k1_xboole_0,X0,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_6969,c_3248])).

cnf(c_8220,plain,
    ( k1_relset_1(k1_xboole_0,X0,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_8219,c_3089])).

cnf(c_50634,plain,
    ( k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_50633,c_3,c_8220])).

cnf(c_50635,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_50634])).

cnf(c_9849,plain,
    ( v1_funct_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_9641,c_2936])).

cnf(c_3015,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3011,c_1520])).

cnf(c_103,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_105,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_103])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_50635,c_9849,c_3015,c_1905,c_105])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:55:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 15.68/2.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.68/2.49  
% 15.68/2.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.68/2.49  
% 15.68/2.49  ------  iProver source info
% 15.68/2.49  
% 15.68/2.49  git: date: 2020-06-30 10:37:57 +0100
% 15.68/2.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.68/2.49  git: non_committed_changes: false
% 15.68/2.49  git: last_make_outside_of_git: false
% 15.68/2.49  
% 15.68/2.49  ------ 
% 15.68/2.49  
% 15.68/2.49  ------ Input Options
% 15.68/2.49  
% 15.68/2.49  --out_options                           all
% 15.68/2.49  --tptp_safe_out                         true
% 15.68/2.49  --problem_path                          ""
% 15.68/2.49  --include_path                          ""
% 15.68/2.49  --clausifier                            res/vclausify_rel
% 15.68/2.49  --clausifier_options                    ""
% 15.68/2.49  --stdin                                 false
% 15.68/2.49  --stats_out                             all
% 15.68/2.49  
% 15.68/2.49  ------ General Options
% 15.68/2.49  
% 15.68/2.49  --fof                                   false
% 15.68/2.49  --time_out_real                         305.
% 15.68/2.49  --time_out_virtual                      -1.
% 15.68/2.49  --symbol_type_check                     false
% 15.68/2.49  --clausify_out                          false
% 15.68/2.49  --sig_cnt_out                           false
% 15.68/2.49  --trig_cnt_out                          false
% 15.68/2.49  --trig_cnt_out_tolerance                1.
% 15.68/2.49  --trig_cnt_out_sk_spl                   false
% 15.68/2.49  --abstr_cl_out                          false
% 15.68/2.49  
% 15.68/2.49  ------ Global Options
% 15.68/2.49  
% 15.68/2.49  --schedule                              default
% 15.68/2.49  --add_important_lit                     false
% 15.68/2.49  --prop_solver_per_cl                    1000
% 15.68/2.49  --min_unsat_core                        false
% 15.68/2.49  --soft_assumptions                      false
% 15.68/2.49  --soft_lemma_size                       3
% 15.68/2.49  --prop_impl_unit_size                   0
% 15.68/2.49  --prop_impl_unit                        []
% 15.68/2.49  --share_sel_clauses                     true
% 15.68/2.49  --reset_solvers                         false
% 15.68/2.49  --bc_imp_inh                            [conj_cone]
% 15.68/2.49  --conj_cone_tolerance                   3.
% 15.68/2.49  --extra_neg_conj                        none
% 15.68/2.49  --large_theory_mode                     true
% 15.68/2.49  --prolific_symb_bound                   200
% 15.68/2.49  --lt_threshold                          2000
% 15.68/2.49  --clause_weak_htbl                      true
% 15.68/2.49  --gc_record_bc_elim                     false
% 15.68/2.49  
% 15.68/2.49  ------ Preprocessing Options
% 15.68/2.49  
% 15.68/2.49  --preprocessing_flag                    true
% 15.68/2.49  --time_out_prep_mult                    0.1
% 15.68/2.49  --splitting_mode                        input
% 15.68/2.49  --splitting_grd                         true
% 15.68/2.49  --splitting_cvd                         false
% 15.68/2.49  --splitting_cvd_svl                     false
% 15.68/2.49  --splitting_nvd                         32
% 15.68/2.49  --sub_typing                            true
% 15.68/2.49  --prep_gs_sim                           true
% 15.68/2.49  --prep_unflatten                        true
% 15.68/2.49  --prep_res_sim                          true
% 15.68/2.49  --prep_upred                            true
% 15.68/2.49  --prep_sem_filter                       exhaustive
% 15.68/2.49  --prep_sem_filter_out                   false
% 15.68/2.49  --pred_elim                             true
% 15.68/2.49  --res_sim_input                         true
% 15.68/2.49  --eq_ax_congr_red                       true
% 15.68/2.49  --pure_diseq_elim                       true
% 15.68/2.49  --brand_transform                       false
% 15.68/2.49  --non_eq_to_eq                          false
% 15.68/2.49  --prep_def_merge                        true
% 15.68/2.49  --prep_def_merge_prop_impl              false
% 15.68/2.49  --prep_def_merge_mbd                    true
% 15.68/2.49  --prep_def_merge_tr_red                 false
% 15.68/2.49  --prep_def_merge_tr_cl                  false
% 15.68/2.49  --smt_preprocessing                     true
% 15.68/2.49  --smt_ac_axioms                         fast
% 15.68/2.49  --preprocessed_out                      false
% 15.68/2.49  --preprocessed_stats                    false
% 15.68/2.49  
% 15.68/2.49  ------ Abstraction refinement Options
% 15.68/2.49  
% 15.68/2.49  --abstr_ref                             []
% 15.68/2.49  --abstr_ref_prep                        false
% 15.68/2.49  --abstr_ref_until_sat                   false
% 15.68/2.49  --abstr_ref_sig_restrict                funpre
% 15.68/2.49  --abstr_ref_af_restrict_to_split_sk     false
% 15.68/2.49  --abstr_ref_under                       []
% 15.68/2.49  
% 15.68/2.49  ------ SAT Options
% 15.68/2.49  
% 15.68/2.49  --sat_mode                              false
% 15.68/2.49  --sat_fm_restart_options                ""
% 15.68/2.49  --sat_gr_def                            false
% 15.68/2.49  --sat_epr_types                         true
% 15.68/2.49  --sat_non_cyclic_types                  false
% 15.68/2.49  --sat_finite_models                     false
% 15.68/2.49  --sat_fm_lemmas                         false
% 15.68/2.49  --sat_fm_prep                           false
% 15.68/2.49  --sat_fm_uc_incr                        true
% 15.68/2.49  --sat_out_model                         small
% 15.68/2.49  --sat_out_clauses                       false
% 15.68/2.49  
% 15.68/2.49  ------ QBF Options
% 15.68/2.49  
% 15.68/2.49  --qbf_mode                              false
% 15.68/2.49  --qbf_elim_univ                         false
% 15.68/2.49  --qbf_dom_inst                          none
% 15.68/2.49  --qbf_dom_pre_inst                      false
% 15.68/2.49  --qbf_sk_in                             false
% 15.68/2.49  --qbf_pred_elim                         true
% 15.68/2.49  --qbf_split                             512
% 15.68/2.49  
% 15.68/2.49  ------ BMC1 Options
% 15.68/2.49  
% 15.68/2.49  --bmc1_incremental                      false
% 15.68/2.49  --bmc1_axioms                           reachable_all
% 15.68/2.49  --bmc1_min_bound                        0
% 15.68/2.49  --bmc1_max_bound                        -1
% 15.68/2.49  --bmc1_max_bound_default                -1
% 15.68/2.49  --bmc1_symbol_reachability              true
% 15.68/2.49  --bmc1_property_lemmas                  false
% 15.68/2.49  --bmc1_k_induction                      false
% 15.68/2.49  --bmc1_non_equiv_states                 false
% 15.68/2.49  --bmc1_deadlock                         false
% 15.68/2.49  --bmc1_ucm                              false
% 15.68/2.49  --bmc1_add_unsat_core                   none
% 15.68/2.49  --bmc1_unsat_core_children              false
% 15.68/2.49  --bmc1_unsat_core_extrapolate_axioms    false
% 15.68/2.49  --bmc1_out_stat                         full
% 15.68/2.49  --bmc1_ground_init                      false
% 15.68/2.49  --bmc1_pre_inst_next_state              false
% 15.68/2.49  --bmc1_pre_inst_state                   false
% 15.68/2.49  --bmc1_pre_inst_reach_state             false
% 15.68/2.49  --bmc1_out_unsat_core                   false
% 15.68/2.49  --bmc1_aig_witness_out                  false
% 15.68/2.49  --bmc1_verbose                          false
% 15.68/2.49  --bmc1_dump_clauses_tptp                false
% 15.68/2.49  --bmc1_dump_unsat_core_tptp             false
% 15.68/2.49  --bmc1_dump_file                        -
% 15.68/2.49  --bmc1_ucm_expand_uc_limit              128
% 15.68/2.49  --bmc1_ucm_n_expand_iterations          6
% 15.68/2.49  --bmc1_ucm_extend_mode                  1
% 15.68/2.49  --bmc1_ucm_init_mode                    2
% 15.68/2.49  --bmc1_ucm_cone_mode                    none
% 15.68/2.49  --bmc1_ucm_reduced_relation_type        0
% 15.68/2.49  --bmc1_ucm_relax_model                  4
% 15.68/2.49  --bmc1_ucm_full_tr_after_sat            true
% 15.68/2.49  --bmc1_ucm_expand_neg_assumptions       false
% 15.68/2.49  --bmc1_ucm_layered_model                none
% 15.68/2.49  --bmc1_ucm_max_lemma_size               10
% 15.68/2.49  
% 15.68/2.49  ------ AIG Options
% 15.68/2.49  
% 15.68/2.49  --aig_mode                              false
% 15.68/2.49  
% 15.68/2.49  ------ Instantiation Options
% 15.68/2.49  
% 15.68/2.49  --instantiation_flag                    true
% 15.68/2.49  --inst_sos_flag                         true
% 15.68/2.49  --inst_sos_phase                        true
% 15.68/2.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.68/2.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.68/2.49  --inst_lit_sel_side                     num_symb
% 15.68/2.49  --inst_solver_per_active                1400
% 15.68/2.49  --inst_solver_calls_frac                1.
% 15.68/2.49  --inst_passive_queue_type               priority_queues
% 15.68/2.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.68/2.49  --inst_passive_queues_freq              [25;2]
% 15.68/2.49  --inst_dismatching                      true
% 15.68/2.49  --inst_eager_unprocessed_to_passive     true
% 15.68/2.49  --inst_prop_sim_given                   true
% 15.68/2.49  --inst_prop_sim_new                     false
% 15.68/2.49  --inst_subs_new                         false
% 15.68/2.49  --inst_eq_res_simp                      false
% 15.68/2.49  --inst_subs_given                       false
% 15.68/2.49  --inst_orphan_elimination               true
% 15.68/2.49  --inst_learning_loop_flag               true
% 15.68/2.49  --inst_learning_start                   3000
% 15.68/2.49  --inst_learning_factor                  2
% 15.68/2.49  --inst_start_prop_sim_after_learn       3
% 15.68/2.49  --inst_sel_renew                        solver
% 15.68/2.49  --inst_lit_activity_flag                true
% 15.68/2.49  --inst_restr_to_given                   false
% 15.68/2.49  --inst_activity_threshold               500
% 15.68/2.49  --inst_out_proof                        true
% 15.68/2.49  
% 15.68/2.49  ------ Resolution Options
% 15.68/2.49  
% 15.68/2.49  --resolution_flag                       true
% 15.68/2.49  --res_lit_sel                           adaptive
% 15.68/2.49  --res_lit_sel_side                      none
% 15.68/2.49  --res_ordering                          kbo
% 15.68/2.49  --res_to_prop_solver                    active
% 15.68/2.49  --res_prop_simpl_new                    false
% 15.68/2.49  --res_prop_simpl_given                  true
% 15.68/2.49  --res_passive_queue_type                priority_queues
% 15.68/2.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.68/2.49  --res_passive_queues_freq               [15;5]
% 15.68/2.49  --res_forward_subs                      full
% 15.68/2.49  --res_backward_subs                     full
% 15.68/2.49  --res_forward_subs_resolution           true
% 15.68/2.49  --res_backward_subs_resolution          true
% 15.68/2.49  --res_orphan_elimination                true
% 15.68/2.49  --res_time_limit                        2.
% 15.68/2.49  --res_out_proof                         true
% 15.68/2.49  
% 15.68/2.49  ------ Superposition Options
% 15.68/2.49  
% 15.68/2.49  --superposition_flag                    true
% 15.68/2.49  --sup_passive_queue_type                priority_queues
% 15.68/2.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.68/2.49  --sup_passive_queues_freq               [8;1;4]
% 15.68/2.49  --demod_completeness_check              fast
% 15.68/2.49  --demod_use_ground                      true
% 15.68/2.49  --sup_to_prop_solver                    passive
% 15.68/2.49  --sup_prop_simpl_new                    true
% 15.68/2.49  --sup_prop_simpl_given                  true
% 15.68/2.49  --sup_fun_splitting                     true
% 15.68/2.49  --sup_smt_interval                      50000
% 15.68/2.49  
% 15.68/2.49  ------ Superposition Simplification Setup
% 15.68/2.49  
% 15.68/2.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.68/2.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.68/2.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.68/2.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.68/2.49  --sup_full_triv                         [TrivRules;PropSubs]
% 15.68/2.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.68/2.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.68/2.49  --sup_immed_triv                        [TrivRules]
% 15.68/2.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.68/2.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.68/2.49  --sup_immed_bw_main                     []
% 15.68/2.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.68/2.49  --sup_input_triv                        [Unflattening;TrivRules]
% 15.68/2.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.68/2.49  --sup_input_bw                          []
% 15.68/2.49  
% 15.68/2.49  ------ Combination Options
% 15.68/2.49  
% 15.68/2.49  --comb_res_mult                         3
% 15.68/2.49  --comb_sup_mult                         2
% 15.68/2.49  --comb_inst_mult                        10
% 15.68/2.49  
% 15.68/2.49  ------ Debug Options
% 15.68/2.49  
% 15.68/2.49  --dbg_backtrace                         false
% 15.68/2.49  --dbg_dump_prop_clauses                 false
% 15.68/2.49  --dbg_dump_prop_clauses_file            -
% 15.68/2.49  --dbg_out_stat                          false
% 15.68/2.49  ------ Parsing...
% 15.68/2.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.68/2.49  
% 15.68/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 15.68/2.49  
% 15.68/2.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.68/2.49  
% 15.68/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.68/2.49  ------ Proving...
% 15.68/2.49  ------ Problem Properties 
% 15.68/2.49  
% 15.68/2.49  
% 15.68/2.49  clauses                                 34
% 15.68/2.49  conjectures                             4
% 15.68/2.49  EPR                                     6
% 15.68/2.49  Horn                                    31
% 15.68/2.49  unary                                   6
% 15.68/2.49  binary                                  10
% 15.68/2.49  lits                                    88
% 15.68/2.49  lits eq                                 28
% 15.68/2.49  fd_pure                                 0
% 15.68/2.49  fd_pseudo                               0
% 15.68/2.49  fd_cond                                 2
% 15.68/2.49  fd_pseudo_cond                          0
% 15.68/2.49  AC symbols                              0
% 15.68/2.49  
% 15.68/2.49  ------ Schedule dynamic 5 is on 
% 15.68/2.49  
% 15.68/2.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 15.68/2.49  
% 15.68/2.49  
% 15.68/2.49  ------ 
% 15.68/2.49  Current options:
% 15.68/2.49  ------ 
% 15.68/2.49  
% 15.68/2.49  ------ Input Options
% 15.68/2.49  
% 15.68/2.49  --out_options                           all
% 15.68/2.49  --tptp_safe_out                         true
% 15.68/2.49  --problem_path                          ""
% 15.68/2.49  --include_path                          ""
% 15.68/2.49  --clausifier                            res/vclausify_rel
% 15.68/2.49  --clausifier_options                    ""
% 15.68/2.49  --stdin                                 false
% 15.68/2.49  --stats_out                             all
% 15.68/2.49  
% 15.68/2.49  ------ General Options
% 15.68/2.49  
% 15.68/2.49  --fof                                   false
% 15.68/2.49  --time_out_real                         305.
% 15.68/2.49  --time_out_virtual                      -1.
% 15.68/2.50  --symbol_type_check                     false
% 15.68/2.50  --clausify_out                          false
% 15.68/2.50  --sig_cnt_out                           false
% 15.68/2.50  --trig_cnt_out                          false
% 15.68/2.50  --trig_cnt_out_tolerance                1.
% 15.68/2.50  --trig_cnt_out_sk_spl                   false
% 15.68/2.50  --abstr_cl_out                          false
% 15.68/2.50  
% 15.68/2.50  ------ Global Options
% 15.68/2.50  
% 15.68/2.50  --schedule                              default
% 15.68/2.50  --add_important_lit                     false
% 15.68/2.50  --prop_solver_per_cl                    1000
% 15.68/2.50  --min_unsat_core                        false
% 15.68/2.50  --soft_assumptions                      false
% 15.68/2.50  --soft_lemma_size                       3
% 15.68/2.50  --prop_impl_unit_size                   0
% 15.68/2.50  --prop_impl_unit                        []
% 15.68/2.50  --share_sel_clauses                     true
% 15.68/2.50  --reset_solvers                         false
% 15.68/2.50  --bc_imp_inh                            [conj_cone]
% 15.68/2.50  --conj_cone_tolerance                   3.
% 15.68/2.50  --extra_neg_conj                        none
% 15.68/2.50  --large_theory_mode                     true
% 15.68/2.50  --prolific_symb_bound                   200
% 15.68/2.50  --lt_threshold                          2000
% 15.68/2.50  --clause_weak_htbl                      true
% 15.68/2.50  --gc_record_bc_elim                     false
% 15.68/2.50  
% 15.68/2.50  ------ Preprocessing Options
% 15.68/2.50  
% 15.68/2.50  --preprocessing_flag                    true
% 15.68/2.50  --time_out_prep_mult                    0.1
% 15.68/2.50  --splitting_mode                        input
% 15.68/2.50  --splitting_grd                         true
% 15.68/2.50  --splitting_cvd                         false
% 15.68/2.50  --splitting_cvd_svl                     false
% 15.68/2.50  --splitting_nvd                         32
% 15.68/2.50  --sub_typing                            true
% 15.68/2.50  --prep_gs_sim                           true
% 15.68/2.50  --prep_unflatten                        true
% 15.68/2.50  --prep_res_sim                          true
% 15.68/2.50  --prep_upred                            true
% 15.68/2.50  --prep_sem_filter                       exhaustive
% 15.68/2.50  --prep_sem_filter_out                   false
% 15.68/2.50  --pred_elim                             true
% 15.68/2.50  --res_sim_input                         true
% 15.68/2.50  --eq_ax_congr_red                       true
% 15.68/2.50  --pure_diseq_elim                       true
% 15.68/2.50  --brand_transform                       false
% 15.68/2.50  --non_eq_to_eq                          false
% 15.68/2.50  --prep_def_merge                        true
% 15.68/2.50  --prep_def_merge_prop_impl              false
% 15.68/2.50  --prep_def_merge_mbd                    true
% 15.68/2.50  --prep_def_merge_tr_red                 false
% 15.68/2.50  --prep_def_merge_tr_cl                  false
% 15.68/2.50  --smt_preprocessing                     true
% 15.68/2.50  --smt_ac_axioms                         fast
% 15.68/2.50  --preprocessed_out                      false
% 15.68/2.50  --preprocessed_stats                    false
% 15.68/2.50  
% 15.68/2.50  ------ Abstraction refinement Options
% 15.68/2.50  
% 15.68/2.50  --abstr_ref                             []
% 15.68/2.50  --abstr_ref_prep                        false
% 15.68/2.50  --abstr_ref_until_sat                   false
% 15.68/2.50  --abstr_ref_sig_restrict                funpre
% 15.68/2.50  --abstr_ref_af_restrict_to_split_sk     false
% 15.68/2.50  --abstr_ref_under                       []
% 15.68/2.50  
% 15.68/2.50  ------ SAT Options
% 15.68/2.50  
% 15.68/2.50  --sat_mode                              false
% 15.68/2.50  --sat_fm_restart_options                ""
% 15.68/2.50  --sat_gr_def                            false
% 15.68/2.50  --sat_epr_types                         true
% 15.68/2.50  --sat_non_cyclic_types                  false
% 15.68/2.50  --sat_finite_models                     false
% 15.68/2.50  --sat_fm_lemmas                         false
% 15.68/2.50  --sat_fm_prep                           false
% 15.68/2.50  --sat_fm_uc_incr                        true
% 15.68/2.50  --sat_out_model                         small
% 15.68/2.50  --sat_out_clauses                       false
% 15.68/2.50  
% 15.68/2.50  ------ QBF Options
% 15.68/2.50  
% 15.68/2.50  --qbf_mode                              false
% 15.68/2.50  --qbf_elim_univ                         false
% 15.68/2.50  --qbf_dom_inst                          none
% 15.68/2.50  --qbf_dom_pre_inst                      false
% 15.68/2.50  --qbf_sk_in                             false
% 15.68/2.50  --qbf_pred_elim                         true
% 15.68/2.50  --qbf_split                             512
% 15.68/2.50  
% 15.68/2.50  ------ BMC1 Options
% 15.68/2.50  
% 15.68/2.50  --bmc1_incremental                      false
% 15.68/2.50  --bmc1_axioms                           reachable_all
% 15.68/2.50  --bmc1_min_bound                        0
% 15.68/2.50  --bmc1_max_bound                        -1
% 15.68/2.50  --bmc1_max_bound_default                -1
% 15.68/2.50  --bmc1_symbol_reachability              true
% 15.68/2.50  --bmc1_property_lemmas                  false
% 15.68/2.50  --bmc1_k_induction                      false
% 15.68/2.50  --bmc1_non_equiv_states                 false
% 15.68/2.50  --bmc1_deadlock                         false
% 15.68/2.50  --bmc1_ucm                              false
% 15.68/2.50  --bmc1_add_unsat_core                   none
% 15.68/2.50  --bmc1_unsat_core_children              false
% 15.68/2.50  --bmc1_unsat_core_extrapolate_axioms    false
% 15.68/2.50  --bmc1_out_stat                         full
% 15.68/2.50  --bmc1_ground_init                      false
% 15.68/2.50  --bmc1_pre_inst_next_state              false
% 15.68/2.50  --bmc1_pre_inst_state                   false
% 15.68/2.50  --bmc1_pre_inst_reach_state             false
% 15.68/2.50  --bmc1_out_unsat_core                   false
% 15.68/2.50  --bmc1_aig_witness_out                  false
% 15.68/2.50  --bmc1_verbose                          false
% 15.68/2.50  --bmc1_dump_clauses_tptp                false
% 15.68/2.50  --bmc1_dump_unsat_core_tptp             false
% 15.68/2.50  --bmc1_dump_file                        -
% 15.68/2.50  --bmc1_ucm_expand_uc_limit              128
% 15.68/2.50  --bmc1_ucm_n_expand_iterations          6
% 15.68/2.50  --bmc1_ucm_extend_mode                  1
% 15.68/2.50  --bmc1_ucm_init_mode                    2
% 15.68/2.50  --bmc1_ucm_cone_mode                    none
% 15.68/2.50  --bmc1_ucm_reduced_relation_type        0
% 15.68/2.50  --bmc1_ucm_relax_model                  4
% 15.68/2.50  --bmc1_ucm_full_tr_after_sat            true
% 15.68/2.50  --bmc1_ucm_expand_neg_assumptions       false
% 15.68/2.50  --bmc1_ucm_layered_model                none
% 15.68/2.50  --bmc1_ucm_max_lemma_size               10
% 15.68/2.50  
% 15.68/2.50  ------ AIG Options
% 15.68/2.50  
% 15.68/2.50  --aig_mode                              false
% 15.68/2.50  
% 15.68/2.50  ------ Instantiation Options
% 15.68/2.50  
% 15.68/2.50  --instantiation_flag                    true
% 15.68/2.50  --inst_sos_flag                         true
% 15.68/2.50  --inst_sos_phase                        true
% 15.68/2.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.68/2.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.68/2.50  --inst_lit_sel_side                     none
% 15.68/2.50  --inst_solver_per_active                1400
% 15.68/2.50  --inst_solver_calls_frac                1.
% 15.68/2.50  --inst_passive_queue_type               priority_queues
% 15.68/2.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.68/2.50  --inst_passive_queues_freq              [25;2]
% 15.68/2.50  --inst_dismatching                      true
% 15.68/2.50  --inst_eager_unprocessed_to_passive     true
% 15.68/2.50  --inst_prop_sim_given                   true
% 15.68/2.50  --inst_prop_sim_new                     false
% 15.68/2.50  --inst_subs_new                         false
% 15.68/2.50  --inst_eq_res_simp                      false
% 15.68/2.50  --inst_subs_given                       false
% 15.68/2.50  --inst_orphan_elimination               true
% 15.68/2.50  --inst_learning_loop_flag               true
% 15.68/2.50  --inst_learning_start                   3000
% 15.68/2.50  --inst_learning_factor                  2
% 15.68/2.50  --inst_start_prop_sim_after_learn       3
% 15.68/2.50  --inst_sel_renew                        solver
% 15.68/2.50  --inst_lit_activity_flag                true
% 15.68/2.50  --inst_restr_to_given                   false
% 15.68/2.50  --inst_activity_threshold               500
% 15.68/2.50  --inst_out_proof                        true
% 15.68/2.50  
% 15.68/2.50  ------ Resolution Options
% 15.68/2.50  
% 15.68/2.50  --resolution_flag                       false
% 15.68/2.50  --res_lit_sel                           adaptive
% 15.68/2.50  --res_lit_sel_side                      none
% 15.68/2.50  --res_ordering                          kbo
% 15.68/2.50  --res_to_prop_solver                    active
% 15.68/2.50  --res_prop_simpl_new                    false
% 15.68/2.50  --res_prop_simpl_given                  true
% 15.68/2.50  --res_passive_queue_type                priority_queues
% 15.68/2.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.68/2.50  --res_passive_queues_freq               [15;5]
% 15.68/2.50  --res_forward_subs                      full
% 15.68/2.50  --res_backward_subs                     full
% 15.68/2.50  --res_forward_subs_resolution           true
% 15.68/2.50  --res_backward_subs_resolution          true
% 15.68/2.50  --res_orphan_elimination                true
% 15.68/2.50  --res_time_limit                        2.
% 15.68/2.50  --res_out_proof                         true
% 15.68/2.50  
% 15.68/2.50  ------ Superposition Options
% 15.68/2.50  
% 15.68/2.50  --superposition_flag                    true
% 15.68/2.50  --sup_passive_queue_type                priority_queues
% 15.68/2.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.68/2.50  --sup_passive_queues_freq               [8;1;4]
% 15.68/2.50  --demod_completeness_check              fast
% 15.68/2.50  --demod_use_ground                      true
% 15.68/2.50  --sup_to_prop_solver                    passive
% 15.68/2.50  --sup_prop_simpl_new                    true
% 15.68/2.50  --sup_prop_simpl_given                  true
% 15.68/2.50  --sup_fun_splitting                     true
% 15.68/2.50  --sup_smt_interval                      50000
% 15.68/2.50  
% 15.68/2.50  ------ Superposition Simplification Setup
% 15.68/2.50  
% 15.68/2.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.68/2.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.68/2.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.68/2.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.68/2.50  --sup_full_triv                         [TrivRules;PropSubs]
% 15.68/2.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.68/2.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.68/2.50  --sup_immed_triv                        [TrivRules]
% 15.68/2.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.68/2.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.68/2.50  --sup_immed_bw_main                     []
% 15.68/2.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.68/2.50  --sup_input_triv                        [Unflattening;TrivRules]
% 15.68/2.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.68/2.50  --sup_input_bw                          []
% 15.68/2.50  
% 15.68/2.50  ------ Combination Options
% 15.68/2.50  
% 15.68/2.50  --comb_res_mult                         3
% 15.68/2.50  --comb_sup_mult                         2
% 15.68/2.50  --comb_inst_mult                        10
% 15.68/2.50  
% 15.68/2.50  ------ Debug Options
% 15.68/2.50  
% 15.68/2.50  --dbg_backtrace                         false
% 15.68/2.50  --dbg_dump_prop_clauses                 false
% 15.68/2.50  --dbg_dump_prop_clauses_file            -
% 15.68/2.50  --dbg_out_stat                          false
% 15.68/2.50  
% 15.68/2.50  
% 15.68/2.50  
% 15.68/2.50  
% 15.68/2.50  ------ Proving...
% 15.68/2.50  
% 15.68/2.50  
% 15.68/2.50  % SZS status Theorem for theBenchmark.p
% 15.68/2.50  
% 15.68/2.50  % SZS output start CNFRefutation for theBenchmark.p
% 15.68/2.50  
% 15.68/2.50  fof(f19,conjecture,(
% 15.68/2.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 15.68/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.68/2.50  
% 15.68/2.50  fof(f20,negated_conjecture,(
% 15.68/2.50    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 15.68/2.50    inference(negated_conjecture,[],[f19])).
% 15.68/2.50  
% 15.68/2.50  fof(f45,plain,(
% 15.68/2.50    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 15.68/2.50    inference(ennf_transformation,[],[f20])).
% 15.68/2.50  
% 15.68/2.50  fof(f46,plain,(
% 15.68/2.50    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 15.68/2.50    inference(flattening,[],[f45])).
% 15.68/2.50  
% 15.68/2.50  fof(f51,plain,(
% 15.68/2.50    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 15.68/2.50    introduced(choice_axiom,[])).
% 15.68/2.50  
% 15.68/2.50  fof(f52,plain,(
% 15.68/2.50    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 15.68/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f46,f51])).
% 15.68/2.50  
% 15.68/2.50  fof(f84,plain,(
% 15.68/2.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 15.68/2.50    inference(cnf_transformation,[],[f52])).
% 15.68/2.50  
% 15.68/2.50  fof(f17,axiom,(
% 15.68/2.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 15.68/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.68/2.50  
% 15.68/2.50  fof(f41,plain,(
% 15.68/2.50    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 15.68/2.50    inference(ennf_transformation,[],[f17])).
% 15.68/2.50  
% 15.68/2.50  fof(f42,plain,(
% 15.68/2.50    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 15.68/2.50    inference(flattening,[],[f41])).
% 15.68/2.50  
% 15.68/2.50  fof(f79,plain,(
% 15.68/2.50    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 15.68/2.50    inference(cnf_transformation,[],[f42])).
% 15.68/2.50  
% 15.68/2.50  fof(f18,axiom,(
% 15.68/2.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 15.68/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.68/2.50  
% 15.68/2.50  fof(f43,plain,(
% 15.68/2.50    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 15.68/2.50    inference(ennf_transformation,[],[f18])).
% 15.68/2.50  
% 15.68/2.50  fof(f44,plain,(
% 15.68/2.50    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 15.68/2.50    inference(flattening,[],[f43])).
% 15.68/2.50  
% 15.68/2.50  fof(f81,plain,(
% 15.68/2.50    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 15.68/2.50    inference(cnf_transformation,[],[f44])).
% 15.68/2.50  
% 15.68/2.50  fof(f82,plain,(
% 15.68/2.50    v1_funct_1(sK3)),
% 15.68/2.50    inference(cnf_transformation,[],[f52])).
% 15.68/2.50  
% 15.68/2.50  fof(f85,plain,(
% 15.68/2.50    r1_tarski(sK2,sK0)),
% 15.68/2.50    inference(cnf_transformation,[],[f52])).
% 15.68/2.50  
% 15.68/2.50  fof(f16,axiom,(
% 15.68/2.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 15.68/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.68/2.50  
% 15.68/2.50  fof(f39,plain,(
% 15.68/2.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.68/2.50    inference(ennf_transformation,[],[f16])).
% 15.68/2.50  
% 15.68/2.50  fof(f40,plain,(
% 15.68/2.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.68/2.50    inference(flattening,[],[f39])).
% 15.68/2.50  
% 15.68/2.50  fof(f50,plain,(
% 15.68/2.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.68/2.50    inference(nnf_transformation,[],[f40])).
% 15.68/2.50  
% 15.68/2.50  fof(f73,plain,(
% 15.68/2.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.68/2.50    inference(cnf_transformation,[],[f50])).
% 15.68/2.50  
% 15.68/2.50  fof(f83,plain,(
% 15.68/2.50    v1_funct_2(sK3,sK0,sK1)),
% 15.68/2.50    inference(cnf_transformation,[],[f52])).
% 15.68/2.50  
% 15.68/2.50  fof(f14,axiom,(
% 15.68/2.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 15.68/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.68/2.50  
% 15.68/2.50  fof(f36,plain,(
% 15.68/2.50    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.68/2.50    inference(ennf_transformation,[],[f14])).
% 15.68/2.50  
% 15.68/2.50  fof(f71,plain,(
% 15.68/2.50    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.68/2.50    inference(cnf_transformation,[],[f36])).
% 15.68/2.50  
% 15.68/2.50  fof(f12,axiom,(
% 15.68/2.50    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 15.68/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.68/2.50  
% 15.68/2.50  fof(f33,plain,(
% 15.68/2.50    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 15.68/2.50    inference(ennf_transformation,[],[f12])).
% 15.68/2.50  
% 15.68/2.50  fof(f34,plain,(
% 15.68/2.50    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 15.68/2.50    inference(flattening,[],[f33])).
% 15.68/2.50  
% 15.68/2.50  fof(f69,plain,(
% 15.68/2.50    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 15.68/2.50    inference(cnf_transformation,[],[f34])).
% 15.68/2.50  
% 15.68/2.50  fof(f8,axiom,(
% 15.68/2.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 15.68/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.68/2.50  
% 15.68/2.50  fof(f65,plain,(
% 15.68/2.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 15.68/2.50    inference(cnf_transformation,[],[f8])).
% 15.68/2.50  
% 15.68/2.50  fof(f4,axiom,(
% 15.68/2.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 15.68/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.68/2.50  
% 15.68/2.50  fof(f49,plain,(
% 15.68/2.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 15.68/2.50    inference(nnf_transformation,[],[f4])).
% 15.68/2.50  
% 15.68/2.50  fof(f58,plain,(
% 15.68/2.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 15.68/2.50    inference(cnf_transformation,[],[f49])).
% 15.68/2.50  
% 15.68/2.50  fof(f5,axiom,(
% 15.68/2.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 15.68/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.68/2.50  
% 15.68/2.50  fof(f25,plain,(
% 15.68/2.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 15.68/2.50    inference(ennf_transformation,[],[f5])).
% 15.68/2.50  
% 15.68/2.50  fof(f60,plain,(
% 15.68/2.50    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 15.68/2.50    inference(cnf_transformation,[],[f25])).
% 15.68/2.50  
% 15.68/2.50  fof(f59,plain,(
% 15.68/2.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 15.68/2.50    inference(cnf_transformation,[],[f49])).
% 15.68/2.50  
% 15.68/2.50  fof(f80,plain,(
% 15.68/2.50    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 15.68/2.50    inference(cnf_transformation,[],[f42])).
% 15.68/2.50  
% 15.68/2.50  fof(f15,axiom,(
% 15.68/2.50    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 15.68/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.68/2.50  
% 15.68/2.50  fof(f37,plain,(
% 15.68/2.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 15.68/2.50    inference(ennf_transformation,[],[f15])).
% 15.68/2.50  
% 15.68/2.50  fof(f38,plain,(
% 15.68/2.50    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 15.68/2.50    inference(flattening,[],[f37])).
% 15.68/2.50  
% 15.68/2.50  fof(f72,plain,(
% 15.68/2.50    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 15.68/2.50    inference(cnf_transformation,[],[f38])).
% 15.68/2.50  
% 15.68/2.50  fof(f10,axiom,(
% 15.68/2.50    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 15.68/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.68/2.50  
% 15.68/2.50  fof(f31,plain,(
% 15.68/2.50    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 15.68/2.50    inference(ennf_transformation,[],[f10])).
% 15.68/2.50  
% 15.68/2.50  fof(f67,plain,(
% 15.68/2.50    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 15.68/2.50    inference(cnf_transformation,[],[f31])).
% 15.68/2.50  
% 15.68/2.50  fof(f75,plain,(
% 15.68/2.50    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.68/2.50    inference(cnf_transformation,[],[f50])).
% 15.68/2.50  
% 15.68/2.50  fof(f87,plain,(
% 15.68/2.50    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 15.68/2.50    inference(cnf_transformation,[],[f52])).
% 15.68/2.50  
% 15.68/2.50  fof(f76,plain,(
% 15.68/2.50    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.68/2.50    inference(cnf_transformation,[],[f50])).
% 15.68/2.50  
% 15.68/2.50  fof(f93,plain,(
% 15.68/2.50    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 15.68/2.50    inference(equality_resolution,[],[f76])).
% 15.68/2.50  
% 15.68/2.50  fof(f3,axiom,(
% 15.68/2.50    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 15.68/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.68/2.50  
% 15.68/2.50  fof(f47,plain,(
% 15.68/2.50    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 15.68/2.50    inference(nnf_transformation,[],[f3])).
% 15.68/2.50  
% 15.68/2.50  fof(f48,plain,(
% 15.68/2.50    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 15.68/2.50    inference(flattening,[],[f47])).
% 15.68/2.50  
% 15.68/2.50  fof(f56,plain,(
% 15.68/2.50    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 15.68/2.50    inference(cnf_transformation,[],[f48])).
% 15.68/2.50  
% 15.68/2.50  fof(f89,plain,(
% 15.68/2.50    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 15.68/2.50    inference(equality_resolution,[],[f56])).
% 15.68/2.50  
% 15.68/2.50  fof(f78,plain,(
% 15.68/2.50    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.68/2.50    inference(cnf_transformation,[],[f50])).
% 15.68/2.50  
% 15.68/2.50  fof(f90,plain,(
% 15.68/2.50    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.68/2.50    inference(equality_resolution,[],[f78])).
% 15.68/2.50  
% 15.68/2.50  fof(f91,plain,(
% 15.68/2.50    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 15.68/2.50    inference(equality_resolution,[],[f90])).
% 15.68/2.50  
% 15.68/2.50  fof(f57,plain,(
% 15.68/2.50    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 15.68/2.50    inference(cnf_transformation,[],[f48])).
% 15.68/2.50  
% 15.68/2.50  fof(f88,plain,(
% 15.68/2.50    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 15.68/2.50    inference(equality_resolution,[],[f57])).
% 15.68/2.50  
% 15.68/2.50  fof(f86,plain,(
% 15.68/2.50    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 15.68/2.50    inference(cnf_transformation,[],[f52])).
% 15.68/2.50  
% 15.68/2.50  fof(f55,plain,(
% 15.68/2.50    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 15.68/2.50    inference(cnf_transformation,[],[f48])).
% 15.68/2.50  
% 15.68/2.50  fof(f2,axiom,(
% 15.68/2.50    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 15.68/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.68/2.50  
% 15.68/2.50  fof(f24,plain,(
% 15.68/2.50    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 15.68/2.50    inference(ennf_transformation,[],[f2])).
% 15.68/2.50  
% 15.68/2.50  fof(f54,plain,(
% 15.68/2.50    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 15.68/2.50    inference(cnf_transformation,[],[f24])).
% 15.68/2.50  
% 15.68/2.50  fof(f11,axiom,(
% 15.68/2.50    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 15.68/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.68/2.50  
% 15.68/2.50  fof(f32,plain,(
% 15.68/2.50    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 15.68/2.50    inference(ennf_transformation,[],[f11])).
% 15.68/2.50  
% 15.68/2.50  fof(f68,plain,(
% 15.68/2.50    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 15.68/2.50    inference(cnf_transformation,[],[f32])).
% 15.68/2.50  
% 15.68/2.50  cnf(c_32,negated_conjecture,
% 15.68/2.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 15.68/2.50      inference(cnf_transformation,[],[f84]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_1511,plain,
% 15.68/2.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 15.68/2.50      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_27,plain,
% 15.68/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.68/2.50      | ~ v1_funct_1(X0)
% 15.68/2.50      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
% 15.68/2.50      inference(cnf_transformation,[],[f79]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_1514,plain,
% 15.68/2.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 15.68/2.50      | v1_funct_1(X0) != iProver_top
% 15.68/2.50      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
% 15.68/2.50      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_2656,plain,
% 15.68/2.50      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
% 15.68/2.50      | v1_funct_1(sK3) != iProver_top ),
% 15.68/2.50      inference(superposition,[status(thm)],[c_1511,c_1514]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_28,plain,
% 15.68/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.68/2.50      | ~ v1_funct_1(X0)
% 15.68/2.50      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 15.68/2.50      inference(cnf_transformation,[],[f81]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_1513,plain,
% 15.68/2.50      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 15.68/2.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.68/2.50      | v1_funct_1(X2) != iProver_top ),
% 15.68/2.50      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_2270,plain,
% 15.68/2.50      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
% 15.68/2.50      | v1_funct_1(sK3) != iProver_top ),
% 15.68/2.50      inference(superposition,[status(thm)],[c_1511,c_1513]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_34,negated_conjecture,
% 15.68/2.50      ( v1_funct_1(sK3) ),
% 15.68/2.50      inference(cnf_transformation,[],[f82]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_35,plain,
% 15.68/2.50      ( v1_funct_1(sK3) = iProver_top ),
% 15.68/2.50      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_2517,plain,
% 15.68/2.50      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 15.68/2.50      inference(global_propositional_subsumption,
% 15.68/2.50                [status(thm)],
% 15.68/2.50                [c_2270,c_35]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_2659,plain,
% 15.68/2.50      ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top
% 15.68/2.50      | v1_funct_1(sK3) != iProver_top ),
% 15.68/2.50      inference(light_normalisation,[status(thm)],[c_2656,c_2517]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_2936,plain,
% 15.68/2.50      ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 15.68/2.50      inference(global_propositional_subsumption,
% 15.68/2.50                [status(thm)],
% 15.68/2.50                [c_2659,c_35]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_31,negated_conjecture,
% 15.68/2.50      ( r1_tarski(sK2,sK0) ),
% 15.68/2.50      inference(cnf_transformation,[],[f85]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_1512,plain,
% 15.68/2.50      ( r1_tarski(sK2,sK0) = iProver_top ),
% 15.68/2.50      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_25,plain,
% 15.68/2.50      ( ~ v1_funct_2(X0,X1,X2)
% 15.68/2.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.68/2.50      | k1_relset_1(X1,X2,X0) = X1
% 15.68/2.50      | k1_xboole_0 = X2 ),
% 15.68/2.50      inference(cnf_transformation,[],[f73]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_33,negated_conjecture,
% 15.68/2.50      ( v1_funct_2(sK3,sK0,sK1) ),
% 15.68/2.50      inference(cnf_transformation,[],[f83]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_518,plain,
% 15.68/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.68/2.50      | k1_relset_1(X1,X2,X0) = X1
% 15.68/2.50      | sK3 != X0
% 15.68/2.50      | sK1 != X2
% 15.68/2.50      | sK0 != X1
% 15.68/2.50      | k1_xboole_0 = X2 ),
% 15.68/2.50      inference(resolution_lifted,[status(thm)],[c_25,c_33]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_519,plain,
% 15.68/2.50      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 15.68/2.50      | k1_relset_1(sK0,sK1,sK3) = sK0
% 15.68/2.50      | k1_xboole_0 = sK1 ),
% 15.68/2.50      inference(unflattening,[status(thm)],[c_518]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_521,plain,
% 15.68/2.50      ( k1_relset_1(sK0,sK1,sK3) = sK0 | k1_xboole_0 = sK1 ),
% 15.68/2.50      inference(global_propositional_subsumption,
% 15.68/2.50                [status(thm)],
% 15.68/2.50                [c_519,c_32]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_18,plain,
% 15.68/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.68/2.50      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 15.68/2.50      inference(cnf_transformation,[],[f71]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_1517,plain,
% 15.68/2.50      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 15.68/2.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 15.68/2.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_2810,plain,
% 15.68/2.50      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 15.68/2.50      inference(superposition,[status(thm)],[c_1511,c_1517]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_2870,plain,
% 15.68/2.50      ( k1_relat_1(sK3) = sK0 | sK1 = k1_xboole_0 ),
% 15.68/2.50      inference(superposition,[status(thm)],[c_521,c_2810]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_16,plain,
% 15.68/2.50      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 15.68/2.50      | ~ v1_relat_1(X1)
% 15.68/2.50      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 15.68/2.50      inference(cnf_transformation,[],[f69]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_1519,plain,
% 15.68/2.50      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 15.68/2.50      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 15.68/2.50      | v1_relat_1(X0) != iProver_top ),
% 15.68/2.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_3439,plain,
% 15.68/2.50      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 15.68/2.50      | sK1 = k1_xboole_0
% 15.68/2.50      | r1_tarski(X0,sK0) != iProver_top
% 15.68/2.50      | v1_relat_1(sK3) != iProver_top ),
% 15.68/2.50      inference(superposition,[status(thm)],[c_2870,c_1519]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_12,plain,
% 15.68/2.50      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 15.68/2.50      inference(cnf_transformation,[],[f65]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_1523,plain,
% 15.68/2.50      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 15.68/2.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_6,plain,
% 15.68/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 15.68/2.50      inference(cnf_transformation,[],[f58]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_1528,plain,
% 15.68/2.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 15.68/2.50      | r1_tarski(X0,X1) = iProver_top ),
% 15.68/2.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_2357,plain,
% 15.68/2.50      ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 15.68/2.50      inference(superposition,[status(thm)],[c_1511,c_1528]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_7,plain,
% 15.68/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.68/2.50      | ~ v1_relat_1(X1)
% 15.68/2.50      | v1_relat_1(X0) ),
% 15.68/2.50      inference(cnf_transformation,[],[f60]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_5,plain,
% 15.68/2.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 15.68/2.50      inference(cnf_transformation,[],[f59]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_246,plain,
% 15.68/2.50      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 15.68/2.50      inference(prop_impl,[status(thm)],[c_5]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_247,plain,
% 15.68/2.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 15.68/2.50      inference(renaming,[status(thm)],[c_246]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_308,plain,
% 15.68/2.50      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 15.68/2.50      inference(bin_hyper_res,[status(thm)],[c_7,c_247]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_1509,plain,
% 15.68/2.50      ( r1_tarski(X0,X1) != iProver_top
% 15.68/2.50      | v1_relat_1(X1) != iProver_top
% 15.68/2.50      | v1_relat_1(X0) = iProver_top ),
% 15.68/2.50      inference(predicate_to_equality,[status(thm)],[c_308]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_2426,plain,
% 15.68/2.50      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 15.68/2.50      | v1_relat_1(sK3) = iProver_top ),
% 15.68/2.50      inference(superposition,[status(thm)],[c_2357,c_1509]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_2529,plain,
% 15.68/2.50      ( v1_relat_1(sK3) = iProver_top ),
% 15.68/2.50      inference(superposition,[status(thm)],[c_1523,c_2426]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_3971,plain,
% 15.68/2.50      ( r1_tarski(X0,sK0) != iProver_top
% 15.68/2.50      | sK1 = k1_xboole_0
% 15.68/2.50      | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
% 15.68/2.50      inference(global_propositional_subsumption,
% 15.68/2.50                [status(thm)],
% 15.68/2.50                [c_3439,c_2529]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_3972,plain,
% 15.68/2.50      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 15.68/2.50      | sK1 = k1_xboole_0
% 15.68/2.50      | r1_tarski(X0,sK0) != iProver_top ),
% 15.68/2.50      inference(renaming,[status(thm)],[c_3971]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_3977,plain,
% 15.68/2.50      ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2 | sK1 = k1_xboole_0 ),
% 15.68/2.50      inference(superposition,[status(thm)],[c_1512,c_3972]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_26,plain,
% 15.68/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.68/2.50      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.68/2.50      | ~ v1_funct_1(X0) ),
% 15.68/2.50      inference(cnf_transformation,[],[f80]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_1515,plain,
% 15.68/2.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 15.68/2.50      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 15.68/2.50      | v1_funct_1(X0) != iProver_top ),
% 15.68/2.50      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_3215,plain,
% 15.68/2.50      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 15.68/2.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 15.68/2.50      | v1_funct_1(sK3) != iProver_top ),
% 15.68/2.50      inference(superposition,[status(thm)],[c_2517,c_1515]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_37,plain,
% 15.68/2.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 15.68/2.50      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_3945,plain,
% 15.68/2.50      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 15.68/2.50      inference(global_propositional_subsumption,
% 15.68/2.50                [status(thm)],
% 15.68/2.50                [c_3215,c_35,c_37]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_19,plain,
% 15.68/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.68/2.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 15.68/2.50      | ~ r1_tarski(k1_relat_1(X0),X3) ),
% 15.68/2.50      inference(cnf_transformation,[],[f72]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_1516,plain,
% 15.68/2.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 15.68/2.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) = iProver_top
% 15.68/2.50      | r1_tarski(k1_relat_1(X0),X3) != iProver_top ),
% 15.68/2.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_4043,plain,
% 15.68/2.50      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
% 15.68/2.50      | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X1) != iProver_top ),
% 15.68/2.50      inference(superposition,[status(thm)],[c_3945,c_1516]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_7265,plain,
% 15.68/2.50      ( k2_partfun1(X0,sK1,k7_relat_1(sK3,X1),X2) = k7_relat_1(k7_relat_1(sK3,X1),X2)
% 15.68/2.50      | r1_tarski(k1_relat_1(k7_relat_1(sK3,X1)),X0) != iProver_top
% 15.68/2.50      | v1_funct_1(k7_relat_1(sK3,X1)) != iProver_top ),
% 15.68/2.50      inference(superposition,[status(thm)],[c_4043,c_1513]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_49839,plain,
% 15.68/2.50      ( k2_partfun1(X0,sK1,k7_relat_1(sK3,sK2),X1) = k7_relat_1(k7_relat_1(sK3,sK2),X1)
% 15.68/2.50      | sK1 = k1_xboole_0
% 15.68/2.50      | r1_tarski(sK2,X0) != iProver_top
% 15.68/2.50      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 15.68/2.50      inference(superposition,[status(thm)],[c_3977,c_7265]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_14,plain,
% 15.68/2.50      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 15.68/2.50      inference(cnf_transformation,[],[f67]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_1521,plain,
% 15.68/2.50      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
% 15.68/2.50      | v1_relat_1(X0) != iProver_top ),
% 15.68/2.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_7264,plain,
% 15.68/2.50      ( k1_relset_1(X0,sK1,k7_relat_1(sK3,X1)) = k1_relat_1(k7_relat_1(sK3,X1))
% 15.68/2.50      | r1_tarski(k1_relat_1(k7_relat_1(sK3,X1)),X0) != iProver_top ),
% 15.68/2.50      inference(superposition,[status(thm)],[c_4043,c_1517]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_21102,plain,
% 15.68/2.50      ( k1_relset_1(X0,sK1,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0))
% 15.68/2.50      | v1_relat_1(sK3) != iProver_top ),
% 15.68/2.50      inference(superposition,[status(thm)],[c_1521,c_7264]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_21912,plain,
% 15.68/2.50      ( k1_relset_1(X0,sK1,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
% 15.68/2.50      inference(global_propositional_subsumption,
% 15.68/2.50                [status(thm)],
% 15.68/2.50                [c_21102,c_2529]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_23,plain,
% 15.68/2.50      ( v1_funct_2(X0,X1,X2)
% 15.68/2.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.68/2.50      | k1_relset_1(X1,X2,X0) != X1
% 15.68/2.50      | k1_xboole_0 = X2 ),
% 15.68/2.50      inference(cnf_transformation,[],[f75]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_29,negated_conjecture,
% 15.68/2.50      ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
% 15.68/2.50      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 15.68/2.50      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
% 15.68/2.50      inference(cnf_transformation,[],[f87]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_502,plain,
% 15.68/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.68/2.50      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 15.68/2.50      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 15.68/2.50      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 15.68/2.50      | k1_relset_1(X1,X2,X0) != X1
% 15.68/2.50      | sK2 != X1
% 15.68/2.50      | sK1 != X2
% 15.68/2.50      | k1_xboole_0 = X2 ),
% 15.68/2.50      inference(resolution_lifted,[status(thm)],[c_23,c_29]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_503,plain,
% 15.68/2.50      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 15.68/2.50      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 15.68/2.50      | k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 15.68/2.50      | k1_xboole_0 = sK1 ),
% 15.68/2.50      inference(unflattening,[status(thm)],[c_502]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_1504,plain,
% 15.68/2.50      ( k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 15.68/2.50      | k1_xboole_0 = sK1
% 15.68/2.50      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 15.68/2.50      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 15.68/2.50      inference(predicate_to_equality,[status(thm)],[c_503]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_2523,plain,
% 15.68/2.50      ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) != sK2
% 15.68/2.50      | sK1 = k1_xboole_0
% 15.68/2.50      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 15.68/2.50      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 15.68/2.50      inference(demodulation,[status(thm)],[c_2517,c_1504]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_21915,plain,
% 15.68/2.50      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 15.68/2.50      | sK1 = k1_xboole_0
% 15.68/2.50      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 15.68/2.50      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 15.68/2.50      inference(demodulation,[status(thm)],[c_21912,c_2523]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_22164,plain,
% 15.68/2.50      ( sK1 = k1_xboole_0
% 15.68/2.50      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 15.68/2.50      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 15.68/2.50      inference(global_propositional_subsumption,
% 15.68/2.50                [status(thm)],
% 15.68/2.50                [c_21915,c_3977]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_22171,plain,
% 15.68/2.50      ( sK1 = k1_xboole_0
% 15.68/2.50      | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) != iProver_top
% 15.68/2.50      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 15.68/2.50      inference(superposition,[status(thm)],[c_4043,c_22164]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_47544,plain,
% 15.68/2.50      ( r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)
% 15.68/2.50      | ~ v1_relat_1(sK3) ),
% 15.68/2.50      inference(instantiation,[status(thm)],[c_14]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_47546,plain,
% 15.68/2.50      ( r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) = iProver_top
% 15.68/2.50      | v1_relat_1(sK3) != iProver_top ),
% 15.68/2.50      inference(predicate_to_equality,[status(thm)],[c_47544]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_50215,plain,
% 15.68/2.50      ( sK1 = k1_xboole_0
% 15.68/2.50      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 15.68/2.50      inference(global_propositional_subsumption,
% 15.68/2.50                [status(thm)],
% 15.68/2.50                [c_49839,c_2529,c_22171,c_47546]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_50219,plain,
% 15.68/2.50      ( sK1 = k1_xboole_0 ),
% 15.68/2.50      inference(superposition,[status(thm)],[c_2936,c_50215]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_22,plain,
% 15.68/2.50      ( v1_funct_2(X0,k1_xboole_0,X1)
% 15.68/2.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 15.68/2.50      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 15.68/2.50      inference(cnf_transformation,[],[f93]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_470,plain,
% 15.68/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 15.68/2.50      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 15.68/2.50      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 15.68/2.50      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 15.68/2.50      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 15.68/2.50      | sK2 != k1_xboole_0
% 15.68/2.50      | sK1 != X1 ),
% 15.68/2.50      inference(resolution_lifted,[status(thm)],[c_22,c_29]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_471,plain,
% 15.68/2.50      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 15.68/2.50      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 15.68/2.50      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 15.68/2.50      | k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
% 15.68/2.50      | sK2 != k1_xboole_0 ),
% 15.68/2.50      inference(unflattening,[status(thm)],[c_470]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_1506,plain,
% 15.68/2.50      ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
% 15.68/2.50      | sK2 != k1_xboole_0
% 15.68/2.50      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 15.68/2.50      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
% 15.68/2.50      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 15.68/2.50      inference(predicate_to_equality,[status(thm)],[c_471]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_3,plain,
% 15.68/2.50      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 15.68/2.50      inference(cnf_transformation,[],[f89]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_1535,plain,
% 15.68/2.50      ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
% 15.68/2.50      | sK2 != k1_xboole_0
% 15.68/2.50      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 15.68/2.50      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 15.68/2.50      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 15.68/2.50      inference(demodulation,[status(thm)],[c_1506,c_3]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_2520,plain,
% 15.68/2.50      ( k1_relset_1(k1_xboole_0,sK1,k7_relat_1(sK3,sK2)) != k1_xboole_0
% 15.68/2.50      | sK2 != k1_xboole_0
% 15.68/2.50      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 15.68/2.50      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 15.68/2.50      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 15.68/2.50      inference(demodulation,[status(thm)],[c_2517,c_1535]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_50606,plain,
% 15.68/2.50      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,sK2)) != k1_xboole_0
% 15.68/2.50      | sK2 != k1_xboole_0
% 15.68/2.50      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
% 15.68/2.50      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 15.68/2.50      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 15.68/2.50      inference(demodulation,[status(thm)],[c_50219,c_2520]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_20,plain,
% 15.68/2.50      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
% 15.68/2.50      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 15.68/2.50      | k1_xboole_0 = X0 ),
% 15.68/2.50      inference(cnf_transformation,[],[f91]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_424,plain,
% 15.68/2.50      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 15.68/2.50      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 15.68/2.50      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 15.68/2.50      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 15.68/2.50      | sK2 != X0
% 15.68/2.50      | sK1 != k1_xboole_0
% 15.68/2.50      | k1_xboole_0 = X0 ),
% 15.68/2.50      inference(resolution_lifted,[status(thm)],[c_20,c_29]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_425,plain,
% 15.68/2.50      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 15.68/2.50      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
% 15.68/2.50      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 15.68/2.50      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 15.68/2.50      | sK1 != k1_xboole_0
% 15.68/2.50      | k1_xboole_0 = sK2 ),
% 15.68/2.50      inference(unflattening,[status(thm)],[c_424]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_1508,plain,
% 15.68/2.50      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 15.68/2.50      | sK1 != k1_xboole_0
% 15.68/2.50      | k1_xboole_0 = sK2
% 15.68/2.50      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 15.68/2.50      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
% 15.68/2.50      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 15.68/2.50      inference(predicate_to_equality,[status(thm)],[c_425]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_2,plain,
% 15.68/2.50      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 15.68/2.50      inference(cnf_transformation,[],[f88]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_1534,plain,
% 15.68/2.50      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 15.68/2.50      | sK2 = k1_xboole_0
% 15.68/2.50      | sK1 != k1_xboole_0
% 15.68/2.50      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 15.68/2.50      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 15.68/2.50      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 15.68/2.50      inference(demodulation,[status(thm)],[c_1508,c_2]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_2521,plain,
% 15.68/2.50      ( k7_relat_1(sK3,sK2) != k1_xboole_0
% 15.68/2.50      | sK2 = k1_xboole_0
% 15.68/2.50      | sK1 != k1_xboole_0
% 15.68/2.50      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 15.68/2.50      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 15.68/2.50      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 15.68/2.50      inference(demodulation,[status(thm)],[c_2517,c_1534]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_30,negated_conjecture,
% 15.68/2.50      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 15.68/2.50      inference(cnf_transformation,[],[f86]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_4,plain,
% 15.68/2.50      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 15.68/2.50      | k1_xboole_0 = X0
% 15.68/2.50      | k1_xboole_0 = X1 ),
% 15.68/2.50      inference(cnf_transformation,[],[f55]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_106,plain,
% 15.68/2.50      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 15.68/2.50      | k1_xboole_0 = k1_xboole_0 ),
% 15.68/2.50      inference(instantiation,[status(thm)],[c_4]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_107,plain,
% 15.68/2.50      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 15.68/2.50      inference(instantiation,[status(thm)],[c_3]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_845,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_1574,plain,
% 15.68/2.50      ( sK2 != X0 | sK2 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 15.68/2.50      inference(instantiation,[status(thm)],[c_845]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_1581,plain,
% 15.68/2.50      ( sK2 != sK2 | sK2 = k1_xboole_0 | k1_xboole_0 != sK2 ),
% 15.68/2.50      inference(instantiation,[status(thm)],[c_1574]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_1,plain,
% 15.68/2.50      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 15.68/2.50      inference(cnf_transformation,[],[f54]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_1590,plain,
% 15.68/2.50      ( ~ r1_tarski(sK2,k1_xboole_0) | k1_xboole_0 = sK2 ),
% 15.68/2.50      inference(instantiation,[status(thm)],[c_1]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_844,plain,( X0 = X0 ),theory(equality) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_1617,plain,
% 15.68/2.50      ( sK2 = sK2 ),
% 15.68/2.50      inference(instantiation,[status(thm)],[c_844]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_846,plain,
% 15.68/2.50      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 15.68/2.50      theory(equality) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_1625,plain,
% 15.68/2.50      ( ~ r1_tarski(X0,X1)
% 15.68/2.50      | r1_tarski(sK2,k1_xboole_0)
% 15.68/2.50      | sK2 != X0
% 15.68/2.50      | k1_xboole_0 != X1 ),
% 15.68/2.50      inference(instantiation,[status(thm)],[c_846]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_1872,plain,
% 15.68/2.50      ( ~ r1_tarski(sK2,X0)
% 15.68/2.50      | r1_tarski(sK2,k1_xboole_0)
% 15.68/2.50      | sK2 != sK2
% 15.68/2.50      | k1_xboole_0 != X0 ),
% 15.68/2.50      inference(instantiation,[status(thm)],[c_1625]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_2371,plain,
% 15.68/2.50      ( ~ r1_tarski(sK2,sK0)
% 15.68/2.50      | r1_tarski(sK2,k1_xboole_0)
% 15.68/2.50      | sK2 != sK2
% 15.68/2.50      | k1_xboole_0 != sK0 ),
% 15.68/2.50      inference(instantiation,[status(thm)],[c_1872]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_2465,plain,
% 15.68/2.50      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 15.68/2.50      inference(instantiation,[status(thm)],[c_845]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_2466,plain,
% 15.68/2.50      ( sK1 != k1_xboole_0
% 15.68/2.50      | k1_xboole_0 = sK1
% 15.68/2.50      | k1_xboole_0 != k1_xboole_0 ),
% 15.68/2.50      inference(instantiation,[status(thm)],[c_2465]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_2608,plain,
% 15.68/2.50      ( sK1 != k1_xboole_0 | sK2 = k1_xboole_0 ),
% 15.68/2.50      inference(global_propositional_subsumption,
% 15.68/2.50                [status(thm)],
% 15.68/2.50                [c_2521,c_31,c_30,c_106,c_107,c_1581,c_1590,c_1617,
% 15.68/2.50                 c_2371,c_2466]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_2609,plain,
% 15.68/2.50      ( sK2 = k1_xboole_0 | sK1 != k1_xboole_0 ),
% 15.68/2.50      inference(renaming,[status(thm)],[c_2608]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_50607,plain,
% 15.68/2.50      ( sK2 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 15.68/2.50      inference(demodulation,[status(thm)],[c_50219,c_2609]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_50627,plain,
% 15.68/2.50      ( sK2 = k1_xboole_0 ),
% 15.68/2.50      inference(equality_resolution_simp,[status(thm)],[c_50607]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_50631,plain,
% 15.68/2.50      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0
% 15.68/2.50      | k1_xboole_0 != k1_xboole_0
% 15.68/2.50      | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 15.68/2.50      | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 15.68/2.50      | v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
% 15.68/2.50      inference(demodulation,[status(thm)],[c_50606,c_50627]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_50632,plain,
% 15.68/2.50      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0
% 15.68/2.50      | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 15.68/2.50      | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 15.68/2.50      | v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
% 15.68/2.50      inference(equality_resolution_simp,[status(thm)],[c_50631]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_7259,plain,
% 15.68/2.50      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 15.68/2.50      | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),k1_xboole_0) != iProver_top ),
% 15.68/2.50      inference(superposition,[status(thm)],[c_3,c_4043]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_7424,plain,
% 15.68/2.50      ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 15.68/2.50      | v1_relat_1(sK3) != iProver_top ),
% 15.68/2.50      inference(superposition,[status(thm)],[c_1521,c_7259]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_9153,plain,
% 15.68/2.50      ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 15.68/2.50      inference(global_propositional_subsumption,
% 15.68/2.50                [status(thm)],
% 15.68/2.50                [c_7424,c_2529]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_9157,plain,
% 15.68/2.50      ( r1_tarski(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 15.68/2.50      inference(superposition,[status(thm)],[c_9153,c_1528]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_1530,plain,
% 15.68/2.50      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 15.68/2.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_9641,plain,
% 15.68/2.50      ( k7_relat_1(sK3,k1_xboole_0) = k1_xboole_0 ),
% 15.68/2.50      inference(superposition,[status(thm)],[c_9157,c_1530]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_50633,plain,
% 15.68/2.50      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 15.68/2.50      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 15.68/2.50      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 15.68/2.50      | v1_funct_1(k1_xboole_0) != iProver_top ),
% 15.68/2.50      inference(light_normalisation,[status(thm)],[c_50632,c_9641]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_15,plain,
% 15.68/2.50      ( r1_tarski(k7_relat_1(X0,X1),X0) | ~ v1_relat_1(X0) ),
% 15.68/2.50      inference(cnf_transformation,[],[f68]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_1520,plain,
% 15.68/2.50      ( r1_tarski(k7_relat_1(X0,X1),X0) = iProver_top
% 15.68/2.50      | v1_relat_1(X0) != iProver_top ),
% 15.68/2.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_2265,plain,
% 15.68/2.50      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0
% 15.68/2.50      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 15.68/2.50      inference(superposition,[status(thm)],[c_1520,c_1530]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_1905,plain,
% 15.68/2.50      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 15.68/2.50      inference(superposition,[status(thm)],[c_2,c_1523]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_3011,plain,
% 15.68/2.50      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 15.68/2.50      inference(global_propositional_subsumption,
% 15.68/2.50                [status(thm)],
% 15.68/2.50                [c_2265,c_1905]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_3014,plain,
% 15.68/2.50      ( r1_tarski(k1_relat_1(k1_xboole_0),X0) = iProver_top
% 15.68/2.50      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 15.68/2.50      inference(superposition,[status(thm)],[c_3011,c_1521]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_6963,plain,
% 15.68/2.50      ( r1_tarski(k1_relat_1(k1_xboole_0),X0) = iProver_top ),
% 15.68/2.50      inference(global_propositional_subsumption,
% 15.68/2.50                [status(thm)],
% 15.68/2.50                [c_3014,c_1905]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_2418,plain,
% 15.68/2.50      ( k1_relat_1(k7_relat_1(X0,k1_xboole_0)) = k1_xboole_0
% 15.68/2.50      | v1_relat_1(X0) != iProver_top ),
% 15.68/2.50      inference(superposition,[status(thm)],[c_1521,c_1530]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_3087,plain,
% 15.68/2.50      ( k1_relat_1(k7_relat_1(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
% 15.68/2.50      inference(superposition,[status(thm)],[c_1905,c_2418]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_3089,plain,
% 15.68/2.50      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 15.68/2.50      inference(demodulation,[status(thm)],[c_3087,c_3011]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_6969,plain,
% 15.68/2.50      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 15.68/2.50      inference(light_normalisation,[status(thm)],[c_6963,c_3089]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_1529,plain,
% 15.68/2.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 15.68/2.50      | r1_tarski(X0,X1) != iProver_top ),
% 15.68/2.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_2812,plain,
% 15.68/2.50      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
% 15.68/2.50      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 15.68/2.50      inference(superposition,[status(thm)],[c_3,c_1517]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_3248,plain,
% 15.68/2.50      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
% 15.68/2.50      | r1_tarski(X1,k1_xboole_0) != iProver_top ),
% 15.68/2.50      inference(superposition,[status(thm)],[c_1529,c_2812]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_8219,plain,
% 15.68/2.50      ( k1_relset_1(k1_xboole_0,X0,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
% 15.68/2.50      inference(superposition,[status(thm)],[c_6969,c_3248]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_8220,plain,
% 15.68/2.50      ( k1_relset_1(k1_xboole_0,X0,k1_xboole_0) = k1_xboole_0 ),
% 15.68/2.50      inference(light_normalisation,[status(thm)],[c_8219,c_3089]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_50634,plain,
% 15.68/2.50      ( k1_xboole_0 != k1_xboole_0
% 15.68/2.50      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 15.68/2.50      | v1_funct_1(k1_xboole_0) != iProver_top ),
% 15.68/2.50      inference(demodulation,[status(thm)],[c_50633,c_3,c_8220]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_50635,plain,
% 15.68/2.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 15.68/2.50      | v1_funct_1(k1_xboole_0) != iProver_top ),
% 15.68/2.50      inference(equality_resolution_simp,[status(thm)],[c_50634]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_9849,plain,
% 15.68/2.50      ( v1_funct_1(k1_xboole_0) = iProver_top ),
% 15.68/2.50      inference(superposition,[status(thm)],[c_9641,c_2936]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_3015,plain,
% 15.68/2.50      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top
% 15.68/2.50      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 15.68/2.50      inference(superposition,[status(thm)],[c_3011,c_1520]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_103,plain,
% 15.68/2.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 15.68/2.50      | r1_tarski(X0,X1) != iProver_top ),
% 15.68/2.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(c_105,plain,
% 15.68/2.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 15.68/2.50      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 15.68/2.50      inference(instantiation,[status(thm)],[c_103]) ).
% 15.68/2.50  
% 15.68/2.50  cnf(contradiction,plain,
% 15.68/2.50      ( $false ),
% 15.68/2.50      inference(minisat,
% 15.68/2.50                [status(thm)],
% 15.68/2.50                [c_50635,c_9849,c_3015,c_1905,c_105]) ).
% 15.68/2.50  
% 15.68/2.50  
% 15.68/2.50  % SZS output end CNFRefutation for theBenchmark.p
% 15.68/2.50  
% 15.68/2.50  ------                               Statistics
% 15.68/2.50  
% 15.68/2.50  ------ General
% 15.68/2.50  
% 15.68/2.50  abstr_ref_over_cycles:                  0
% 15.68/2.50  abstr_ref_under_cycles:                 0
% 15.68/2.50  gc_basic_clause_elim:                   0
% 15.68/2.50  forced_gc_time:                         0
% 15.68/2.50  parsing_time:                           0.011
% 15.68/2.50  unif_index_cands_time:                  0.
% 15.68/2.50  unif_index_add_time:                    0.
% 15.68/2.50  orderings_time:                         0.
% 15.68/2.50  out_proof_time:                         0.018
% 15.68/2.50  total_time:                             1.65
% 15.68/2.50  num_of_symbols:                         48
% 15.68/2.50  num_of_terms:                           45695
% 15.68/2.50  
% 15.68/2.50  ------ Preprocessing
% 15.68/2.50  
% 15.68/2.50  num_of_splits:                          0
% 15.68/2.50  num_of_split_atoms:                     0
% 15.68/2.50  num_of_reused_defs:                     0
% 15.68/2.50  num_eq_ax_congr_red:                    11
% 15.68/2.50  num_of_sem_filtered_clauses:            1
% 15.68/2.50  num_of_subtypes:                        0
% 15.68/2.50  monotx_restored_types:                  0
% 15.68/2.50  sat_num_of_epr_types:                   0
% 15.68/2.50  sat_num_of_non_cyclic_types:            0
% 15.68/2.50  sat_guarded_non_collapsed_types:        0
% 15.68/2.50  num_pure_diseq_elim:                    0
% 15.68/2.50  simp_replaced_by:                       0
% 15.68/2.50  res_preprocessed:                       162
% 15.68/2.50  prep_upred:                             0
% 15.68/2.50  prep_unflattend:                        33
% 15.68/2.50  smt_new_axioms:                         0
% 15.68/2.50  pred_elim_cands:                        5
% 15.68/2.50  pred_elim:                              1
% 15.68/2.50  pred_elim_cl:                           1
% 15.68/2.50  pred_elim_cycles:                       3
% 15.68/2.50  merged_defs:                            8
% 15.68/2.50  merged_defs_ncl:                        0
% 15.68/2.50  bin_hyper_res:                          9
% 15.68/2.50  prep_cycles:                            4
% 15.68/2.50  pred_elim_time:                         0.005
% 15.68/2.50  splitting_time:                         0.
% 15.68/2.50  sem_filter_time:                        0.
% 15.68/2.50  monotx_time:                            0.001
% 15.68/2.50  subtype_inf_time:                       0.
% 15.68/2.50  
% 15.68/2.50  ------ Problem properties
% 15.68/2.50  
% 15.68/2.50  clauses:                                34
% 15.68/2.50  conjectures:                            4
% 15.68/2.50  epr:                                    6
% 15.68/2.50  horn:                                   31
% 15.68/2.50  ground:                                 11
% 15.68/2.50  unary:                                  6
% 15.68/2.50  binary:                                 10
% 15.68/2.50  lits:                                   88
% 15.68/2.50  lits_eq:                                28
% 15.68/2.50  fd_pure:                                0
% 15.68/2.50  fd_pseudo:                              0
% 15.68/2.50  fd_cond:                                2
% 15.68/2.50  fd_pseudo_cond:                         0
% 15.68/2.50  ac_symbols:                             0
% 15.68/2.50  
% 15.68/2.50  ------ Propositional Solver
% 15.68/2.50  
% 15.68/2.50  prop_solver_calls:                      46
% 15.68/2.50  prop_fast_solver_calls:                 3374
% 15.68/2.50  smt_solver_calls:                       0
% 15.68/2.50  smt_fast_solver_calls:                  0
% 15.68/2.50  prop_num_of_clauses:                    23413
% 15.68/2.50  prop_preprocess_simplified:             34915
% 15.68/2.50  prop_fo_subsumed:                       183
% 15.68/2.50  prop_solver_time:                       0.
% 15.68/2.50  smt_solver_time:                        0.
% 15.68/2.50  smt_fast_solver_time:                   0.
% 15.68/2.50  prop_fast_solver_time:                  0.
% 15.68/2.50  prop_unsat_core_time:                   0.002
% 15.68/2.50  
% 15.68/2.50  ------ QBF
% 15.68/2.50  
% 15.68/2.50  qbf_q_res:                              0
% 15.68/2.50  qbf_num_tautologies:                    0
% 15.68/2.50  qbf_prep_cycles:                        0
% 15.68/2.50  
% 15.68/2.50  ------ BMC1
% 15.68/2.50  
% 15.68/2.50  bmc1_current_bound:                     -1
% 15.68/2.50  bmc1_last_solved_bound:                 -1
% 15.68/2.50  bmc1_unsat_core_size:                   -1
% 15.68/2.50  bmc1_unsat_core_parents_size:           -1
% 15.68/2.50  bmc1_merge_next_fun:                    0
% 15.68/2.50  bmc1_unsat_core_clauses_time:           0.
% 15.68/2.50  
% 15.68/2.50  ------ Instantiation
% 15.68/2.50  
% 15.68/2.50  inst_num_of_clauses:                    521
% 15.68/2.50  inst_num_in_passive:                    188
% 15.68/2.50  inst_num_in_active:                     2858
% 15.68/2.50  inst_num_in_unprocessed:                82
% 15.68/2.50  inst_num_of_loops:                      3329
% 15.68/2.50  inst_num_of_learning_restarts:          1
% 15.68/2.50  inst_num_moves_active_passive:          461
% 15.68/2.50  inst_lit_activity:                      0
% 15.68/2.50  inst_lit_activity_moves:                0
% 15.68/2.50  inst_num_tautologies:                   0
% 15.68/2.50  inst_num_prop_implied:                  0
% 15.68/2.50  inst_num_existing_simplified:           0
% 15.68/2.50  inst_num_eq_res_simplified:             0
% 15.68/2.50  inst_num_child_elim:                    0
% 15.68/2.50  inst_num_of_dismatching_blockings:      3753
% 15.68/2.50  inst_num_of_non_proper_insts:           7019
% 15.68/2.50  inst_num_of_duplicates:                 0
% 15.68/2.50  inst_inst_num_from_inst_to_res:         0
% 15.68/2.50  inst_dismatching_checking_time:         0.
% 15.68/2.50  
% 15.68/2.50  ------ Resolution
% 15.68/2.50  
% 15.68/2.50  res_num_of_clauses:                     46
% 15.68/2.50  res_num_in_passive:                     46
% 15.68/2.50  res_num_in_active:                      0
% 15.68/2.50  res_num_of_loops:                       166
% 15.68/2.50  res_forward_subset_subsumed:            153
% 15.68/2.50  res_backward_subset_subsumed:           0
% 15.68/2.50  res_forward_subsumed:                   0
% 15.68/2.50  res_backward_subsumed:                  0
% 15.68/2.50  res_forward_subsumption_resolution:     0
% 15.68/2.50  res_backward_subsumption_resolution:    0
% 15.68/2.50  res_clause_to_clause_subsumption:       15213
% 15.68/2.50  res_orphan_elimination:                 0
% 15.68/2.50  res_tautology_del:                      611
% 15.68/2.50  res_num_eq_res_simplified:              1
% 15.68/2.50  res_num_sel_changes:                    0
% 15.68/2.50  res_moves_from_active_to_pass:          0
% 15.68/2.50  
% 15.68/2.50  ------ Superposition
% 15.68/2.50  
% 15.68/2.50  sup_time_total:                         0.
% 15.68/2.50  sup_time_generating:                    0.
% 15.68/2.50  sup_time_sim_full:                      0.
% 15.68/2.50  sup_time_sim_immed:                     0.
% 15.68/2.50  
% 15.68/2.50  sup_num_of_clauses:                     2125
% 15.68/2.50  sup_num_in_active:                      257
% 15.68/2.50  sup_num_in_passive:                     1868
% 15.68/2.50  sup_num_of_loops:                       664
% 15.68/2.50  sup_fw_superposition:                   2450
% 15.68/2.50  sup_bw_superposition:                   2213
% 15.68/2.50  sup_immediate_simplified:               1644
% 15.68/2.50  sup_given_eliminated:                   7
% 15.68/2.50  comparisons_done:                       0
% 15.68/2.50  comparisons_avoided:                    258
% 15.68/2.50  
% 15.68/2.50  ------ Simplifications
% 15.68/2.50  
% 15.68/2.50  
% 15.68/2.50  sim_fw_subset_subsumed:                 297
% 15.68/2.50  sim_bw_subset_subsumed:                 242
% 15.68/2.50  sim_fw_subsumed:                        552
% 15.68/2.50  sim_bw_subsumed:                        60
% 15.68/2.50  sim_fw_subsumption_res:                 0
% 15.68/2.50  sim_bw_subsumption_res:                 0
% 15.68/2.50  sim_tautology_del:                      136
% 15.68/2.50  sim_eq_tautology_del:                   271
% 15.68/2.50  sim_eq_res_simp:                        7
% 15.68/2.50  sim_fw_demodulated:                     740
% 15.68/2.50  sim_bw_demodulated:                     349
% 15.68/2.50  sim_light_normalised:                   520
% 15.68/2.50  sim_joinable_taut:                      0
% 15.68/2.50  sim_joinable_simp:                      0
% 15.68/2.50  sim_ac_normalised:                      0
% 15.68/2.50  sim_smt_subsumption:                    0
% 15.68/2.50  
%------------------------------------------------------------------------------
