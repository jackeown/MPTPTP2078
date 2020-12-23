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
% DateTime   : Thu Dec  3 12:03:56 EST 2020

% Result     : Theorem 15.96s
% Output     : CNFRefutation 15.96s
% Verified   : 
% Statistics : Number of formulae       :  254 (6288 expanded)
%              Number of clauses        :  178 (2434 expanded)
%              Number of leaves         :   19 (1190 expanded)
%              Depth                    :   35
%              Number of atoms          :  766 (30799 expanded)
%              Number of equality atoms :  445 (11294 expanded)
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

fof(f48,plain,(
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

fof(f49,plain,(
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
    inference(flattening,[],[f48])).

fof(f53,plain,
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

fof(f54,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f49,f53])).

fof(f83,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f54])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f46])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f81,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f44])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( r1_tarski(X0,X3)
       => m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(flattening,[],[f40])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f38])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f84,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f54])).

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

fof(f52,plain,(
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

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f82,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f50])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f88,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f58])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

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

fof(f56,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f91,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f76])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f87,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f59])).

fof(f85,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f54])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f86,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f54])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f92,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f75])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f89,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f77])).

fof(f90,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f89])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1154,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1156,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2161,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1154,c_1156])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1535,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_1721,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_1535])).

cnf(c_2489,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2161,c_31,c_29,c_1721])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1158,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_4054,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2489,c_1158])).

cnf(c_34,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1417,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1418,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1417])).

cnf(c_8,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1561,plain,
    ( r1_tarski(k7_relat_1(sK3,X0),sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1567,plain,
    ( r1_tarski(k7_relat_1(sK3,X0),sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1561])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X3,X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2605,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ r1_tarski(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_3687,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ r1_tarski(k7_relat_1(sK3,X0),sK3) ),
    inference(instantiation,[status(thm)],[c_2605])).

cnf(c_3688,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | r1_tarski(k7_relat_1(sK3,X0),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3687])).

cnf(c_5035,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4054,c_34,c_1418,c_1567,c_3688])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1160,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) = iProver_top
    | r1_tarski(k1_relat_1(X0),X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_7155,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5035,c_1160])).

cnf(c_28,negated_conjecture,
    ( r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1155,plain,
    ( r1_tarski(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_441,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X0
    | sK1 != X2
    | sK0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_30])).

cnf(c_442,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_441])).

cnf(c_444,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_442,c_29])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1161,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3094,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1154,c_1161])).

cnf(c_3309,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_444,c_3094])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1164,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4640,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3309,c_1164])).

cnf(c_5201,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | sK1 = k1_xboole_0
    | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4640,c_34,c_1418])).

cnf(c_5202,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5201])).

cnf(c_5210,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1155,c_5202])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_96,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_97,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1463,plain,
    ( r1_tarski(sK2,X0)
    | ~ r1_tarski(sK2,sK0)
    | ~ r1_tarski(sK0,X0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1465,plain,
    ( ~ r1_tarski(sK2,sK0)
    | r1_tarski(sK2,k1_xboole_0)
    | ~ r1_tarski(sK0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1463])).

cnf(c_7,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1562,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X0)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1564,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,k1_xboole_0)),k1_xboole_0)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1562])).

cnf(c_9,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1560,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1572,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,k1_xboole_0)),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1560])).

cnf(c_679,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1870,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,X2)),X2)
    | X1 != X2
    | X0 != k1_relat_1(k7_relat_1(sK3,X2)) ),
    inference(instantiation,[status(thm)],[c_679])).

cnf(c_1872,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,k1_xboole_0)),k1_xboole_0)
    | r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k7_relat_1(sK3,k1_xboole_0))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1870])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1879,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,k1_xboole_0)),k1_xboole_0)
    | k1_xboole_0 = k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_373,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK3 != X0
    | sK1 != k1_xboole_0
    | sK0 != X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_30])).

cnf(c_374,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0 ),
    inference(unflattening,[status(thm)],[c_373])).

cnf(c_1150,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_374])).

cnf(c_2,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1252,plain,
    ( sK3 = k1_xboole_0
    | sK1 != k1_xboole_0
    | sK0 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1150,c_2])).

cnf(c_27,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_678,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1473,plain,
    ( sK0 != X0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_678])).

cnf(c_1859,plain,
    ( sK0 != sK0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1473])).

cnf(c_677,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1860,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_677])).

cnf(c_1934,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_678])).

cnf(c_1935,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1934])).

cnf(c_1975,plain,
    ( sK0 = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1252,c_27,c_96,c_97,c_1859,c_1860,c_1935])).

cnf(c_1976,plain,
    ( sK1 != k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_1975])).

cnf(c_1587,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2226,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | k1_relat_1(k7_relat_1(sK3,sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_1587])).

cnf(c_2620,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK0,X2)
    | X2 != X1
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_679])).

cnf(c_2622,plain,
    ( r1_tarski(sK0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | sK0 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2620])).

cnf(c_1607,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(sK2,X0)
    | r1_tarski(sK2,X1) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2771,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK3))
    | ~ r1_tarski(sK2,X0)
    | r1_tarski(sK2,k1_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_1607])).

cnf(c_2773,plain,
    ( r1_tarski(sK2,k1_relat_1(sK3))
    | ~ r1_tarski(sK2,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_2771])).

cnf(c_1817,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,X2)),k1_relat_1(sK3))
    | X0 != k1_relat_1(k7_relat_1(sK3,X2))
    | X1 != k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_679])).

cnf(c_3484,plain,
    ( r1_tarski(X0,k1_relat_1(sK3))
    | ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,X1)),k1_relat_1(sK3))
    | X0 != k1_relat_1(k7_relat_1(sK3,X1))
    | k1_relat_1(sK3) != k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1817])).

cnf(c_3487,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,k1_xboole_0)),k1_relat_1(sK3))
    | r1_tarski(k1_xboole_0,k1_relat_1(sK3))
    | k1_relat_1(sK3) != k1_relat_1(sK3)
    | k1_xboole_0 != k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_3484])).

cnf(c_3485,plain,
    ( k1_relat_1(sK3) = k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_677])).

cnf(c_5540,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5210,c_29,c_28,c_96,c_97,c_1417,c_1465,c_1564,c_1572,c_1872,c_1879,c_1976,c_2226,c_2622,c_2773,c_3487,c_3485])).

cnf(c_1167,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5544,plain,
    ( r1_tarski(sK2,sK2) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5540,c_1167])).

cnf(c_6365,plain,
    ( r1_tarski(sK2,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5544,c_34,c_1418])).

cnf(c_1166,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1159,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(X3,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_5590,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1154,c_1159])).

cnf(c_7154,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5590,c_1160])).

cnf(c_10980,plain,
    ( k1_relset_1(X0,sK1,X1) = k1_relat_1(X1)
    | r1_tarski(X1,sK3) != iProver_top
    | r1_tarski(k1_relat_1(X1),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7154,c_1161])).

cnf(c_42769,plain,
    ( k1_relset_1(X0,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
    | r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5540,c_10980])).

cnf(c_42789,plain,
    ( k1_relset_1(X0,sK1,k7_relat_1(sK3,sK2)) = sK2
    | r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_42769,c_5540])).

cnf(c_42908,plain,
    ( k1_relset_1(X0,sK1,k7_relat_1(sK3,sK2)) = sK2
    | r1_tarski(sK2,X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1166,c_42789])).

cnf(c_43220,plain,
    ( r1_tarski(sK2,X0) != iProver_top
    | k1_relset_1(X0,sK1,k7_relat_1(sK3,sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_42908,c_34,c_1418])).

cnf(c_43221,plain,
    ( k1_relset_1(X0,sK1,k7_relat_1(sK3,sK2)) = sK2
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_43220])).

cnf(c_43233,plain,
    ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_6365,c_43221])).

cnf(c_20,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_26,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_425,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_relset_1(X1,X2,X0) != X1
    | sK2 != X1
    | sK1 != X2
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_26])).

cnf(c_426,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_425])).

cnf(c_1147,plain,
    ( k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | k1_xboole_0 = sK1
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_426])).

cnf(c_2496,plain,
    ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) != sK2
    | sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2489,c_1147])).

cnf(c_43484,plain,
    ( sK2 != sK2
    | sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_43233,c_2496])).

cnf(c_72495,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_43484])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1157,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2784,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1154,c_1157])).

cnf(c_2801,plain,
    ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2784,c_2489])).

cnf(c_32,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_3731,plain,
    ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2801,c_32])).

cnf(c_72500,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_72495,c_3731])).

cnf(c_72505,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_7155,c_72500])).

cnf(c_72508,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(sK2,sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_72505,c_5540])).

cnf(c_72909,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_72508,c_34,c_1418,c_5544])).

cnf(c_73045,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_72909,c_5035])).

cnf(c_73055,plain,
    ( sK0 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_72909,c_27])).

cnf(c_73056,plain,
    ( sK0 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_73055])).

cnf(c_73107,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_73045,c_73056])).

cnf(c_73109,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_73107,c_3])).

cnf(c_19,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_393,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | sK2 != k1_xboole_0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_26])).

cnf(c_394,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_393])).

cnf(c_1149,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_394])).

cnf(c_1320,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1149,c_3])).

cnf(c_2493,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k7_relat_1(sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2489,c_1320])).

cnf(c_73047,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_72909,c_2493])).

cnf(c_17,plain,
    ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_347,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK2 != X0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_26])).

cnf(c_348,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_347])).

cnf(c_1151,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_348])).

cnf(c_1307,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1151,c_2])).

cnf(c_2494,plain,
    ( k7_relat_1(sK3,sK2) != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2489,c_1307])).

cnf(c_1611,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1520,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(sK2,sK0)
    | X0 != sK2
    | X1 != sK0 ),
    inference(instantiation,[status(thm)],[c_679])).

cnf(c_1645,plain,
    ( r1_tarski(sK2,X0)
    | ~ r1_tarski(sK2,sK0)
    | X0 != sK0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1520])).

cnf(c_1648,plain,
    ( ~ r1_tarski(sK2,sK0)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != sK2
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1645])).

cnf(c_1646,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_677])).

cnf(c_1472,plain,
    ( sK2 != X0
    | sK2 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_678])).

cnf(c_1858,plain,
    ( sK2 != sK2
    | sK2 = k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_1472])).

cnf(c_1931,plain,
    ( X0 != X1
    | X0 = sK0
    | sK0 != X1 ),
    inference(instantiation,[status(thm)],[c_678])).

cnf(c_1932,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1931])).

cnf(c_2689,plain,
    ( sK1 != k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2494,c_28,c_96,c_97,c_1611,c_1648,c_1646,c_1858,c_1932,c_1976])).

cnf(c_2690,plain,
    ( sK2 = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_2689])).

cnf(c_73048,plain,
    ( sK2 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_72909,c_2690])).

cnf(c_73083,plain,
    ( sK2 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_73048])).

cnf(c_73094,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_73047,c_73083])).

cnf(c_73095,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_73094])).

cnf(c_1162,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2282,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1154,c_1162])).

cnf(c_1169,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2926,plain,
    ( k1_relat_1(k7_relat_1(X0,k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1167,c_1169])).

cnf(c_3927,plain,
    ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2282,c_2926])).

cnf(c_34877,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_7155])).

cnf(c_37815,plain,
    ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3927,c_34877])).

cnf(c_1563,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1562])).

cnf(c_1565,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK3,k1_xboole_0)),k1_xboole_0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1563])).

cnf(c_1569,plain,
    ( r1_tarski(k7_relat_1(sK3,k1_xboole_0),sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1567])).

cnf(c_1871,plain,
    ( X0 != X1
    | X2 != k1_relat_1(k7_relat_1(sK3,X1))
    | r1_tarski(X2,X0) = iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,X1)),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1870])).

cnf(c_1873,plain,
    ( k1_xboole_0 != k1_relat_1(k7_relat_1(sK3,k1_xboole_0))
    | k1_xboole_0 != k1_xboole_0
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,k1_xboole_0)),k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1871])).

cnf(c_10974,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_7154])).

cnf(c_12227,plain,
    ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k7_relat_1(sK3,k1_xboole_0),sK3) != iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3927,c_10974])).

cnf(c_38842,plain,
    ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_37815,c_29,c_34,c_96,c_97,c_1417,c_1418,c_1564,c_1565,c_1569,c_1873,c_1879,c_12227])).

cnf(c_3096,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_1161])).

cnf(c_38858,plain,
    ( k1_relset_1(k1_xboole_0,X0,k7_relat_1(sK3,k1_xboole_0)) = k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_38842,c_3096])).

cnf(c_38864,plain,
    ( k1_relset_1(k1_xboole_0,X0,k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_38858,c_3927])).

cnf(c_73100,plain,
    ( k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_73095,c_3,c_38864])).

cnf(c_73101,plain,
    ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_73100])).

cnf(c_73111,plain,
    ( v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
    inference(backward_subsumption_resolution,[status(thm)],[c_73109,c_73101])).

cnf(c_2809,plain,
    ( v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2801])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_73111,c_2809,c_32])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:55:12 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 15.96/2.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.96/2.49  
% 15.96/2.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.96/2.49  
% 15.96/2.49  ------  iProver source info
% 15.96/2.49  
% 15.96/2.49  git: date: 2020-06-30 10:37:57 +0100
% 15.96/2.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.96/2.49  git: non_committed_changes: false
% 15.96/2.49  git: last_make_outside_of_git: false
% 15.96/2.49  
% 15.96/2.49  ------ 
% 15.96/2.49  ------ Parsing...
% 15.96/2.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.96/2.49  
% 15.96/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 15.96/2.49  
% 15.96/2.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.96/2.49  
% 15.96/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.96/2.49  ------ Proving...
% 15.96/2.49  ------ Problem Properties 
% 15.96/2.49  
% 15.96/2.49  
% 15.96/2.49  clauses                                 30
% 15.96/2.49  conjectures                             4
% 15.96/2.49  EPR                                     5
% 15.96/2.49  Horn                                    27
% 15.96/2.49  unary                                   5
% 15.96/2.49  binary                                  10
% 15.96/2.49  lits                                    78
% 15.96/2.49  lits eq                                 29
% 15.96/2.49  fd_pure                                 0
% 15.96/2.49  fd_pseudo                               0
% 15.96/2.49  fd_cond                                 2
% 15.96/2.49  fd_pseudo_cond                          0
% 15.96/2.49  AC symbols                              0
% 15.96/2.49  
% 15.96/2.49  ------ Input Options Time Limit: Unbounded
% 15.96/2.49  
% 15.96/2.49  
% 15.96/2.49  ------ 
% 15.96/2.49  Current options:
% 15.96/2.49  ------ 
% 15.96/2.49  
% 15.96/2.49  
% 15.96/2.49  
% 15.96/2.49  
% 15.96/2.49  ------ Proving...
% 15.96/2.49  
% 15.96/2.49  
% 15.96/2.49  % SZS status Theorem for theBenchmark.p
% 15.96/2.49  
% 15.96/2.49  % SZS output start CNFRefutation for theBenchmark.p
% 15.96/2.49  
% 15.96/2.49  fof(f19,conjecture,(
% 15.96/2.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 15.96/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.96/2.49  
% 15.96/2.49  fof(f20,negated_conjecture,(
% 15.96/2.49    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 15.96/2.49    inference(negated_conjecture,[],[f19])).
% 15.96/2.49  
% 15.96/2.49  fof(f48,plain,(
% 15.96/2.49    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 15.96/2.49    inference(ennf_transformation,[],[f20])).
% 15.96/2.49  
% 15.96/2.49  fof(f49,plain,(
% 15.96/2.49    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 15.96/2.49    inference(flattening,[],[f48])).
% 15.96/2.49  
% 15.96/2.49  fof(f53,plain,(
% 15.96/2.49    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 15.96/2.49    introduced(choice_axiom,[])).
% 15.96/2.49  
% 15.96/2.49  fof(f54,plain,(
% 15.96/2.49    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 15.96/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f49,f53])).
% 15.96/2.49  
% 15.96/2.49  fof(f83,plain,(
% 15.96/2.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 15.96/2.49    inference(cnf_transformation,[],[f54])).
% 15.96/2.49  
% 15.96/2.49  fof(f18,axiom,(
% 15.96/2.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 15.96/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.96/2.49  
% 15.96/2.49  fof(f46,plain,(
% 15.96/2.49    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 15.96/2.49    inference(ennf_transformation,[],[f18])).
% 15.96/2.49  
% 15.96/2.49  fof(f47,plain,(
% 15.96/2.49    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 15.96/2.49    inference(flattening,[],[f46])).
% 15.96/2.49  
% 15.96/2.49  fof(f80,plain,(
% 15.96/2.49    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 15.96/2.49    inference(cnf_transformation,[],[f47])).
% 15.96/2.49  
% 15.96/2.49  fof(f81,plain,(
% 15.96/2.49    v1_funct_1(sK3)),
% 15.96/2.49    inference(cnf_transformation,[],[f54])).
% 15.96/2.49  
% 15.96/2.49  fof(f17,axiom,(
% 15.96/2.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 15.96/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.96/2.49  
% 15.96/2.49  fof(f44,plain,(
% 15.96/2.49    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 15.96/2.49    inference(ennf_transformation,[],[f17])).
% 15.96/2.49  
% 15.96/2.49  fof(f45,plain,(
% 15.96/2.49    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 15.96/2.49    inference(flattening,[],[f44])).
% 15.96/2.49  
% 15.96/2.49  fof(f79,plain,(
% 15.96/2.49    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 15.96/2.49    inference(cnf_transformation,[],[f45])).
% 15.96/2.49  
% 15.96/2.49  fof(f11,axiom,(
% 15.96/2.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 15.96/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.96/2.49  
% 15.96/2.49  fof(f35,plain,(
% 15.96/2.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.96/2.49    inference(ennf_transformation,[],[f11])).
% 15.96/2.49  
% 15.96/2.49  fof(f67,plain,(
% 15.96/2.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.96/2.49    inference(cnf_transformation,[],[f35])).
% 15.96/2.49  
% 15.96/2.49  fof(f7,axiom,(
% 15.96/2.49    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 15.96/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.96/2.49  
% 15.96/2.49  fof(f29,plain,(
% 15.96/2.49    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 15.96/2.49    inference(ennf_transformation,[],[f7])).
% 15.96/2.49  
% 15.96/2.49  fof(f63,plain,(
% 15.96/2.49    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 15.96/2.49    inference(cnf_transformation,[],[f29])).
% 15.96/2.49  
% 15.96/2.49  fof(f15,axiom,(
% 15.96/2.49    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => (r1_tarski(X0,X3) => m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 15.96/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.96/2.49  
% 15.96/2.49  fof(f40,plain,(
% 15.96/2.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 15.96/2.49    inference(ennf_transformation,[],[f15])).
% 15.96/2.49  
% 15.96/2.49  fof(f41,plain,(
% 15.96/2.49    ! [X0,X1,X2,X3] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 15.96/2.49    inference(flattening,[],[f40])).
% 15.96/2.49  
% 15.96/2.49  fof(f71,plain,(
% 15.96/2.49    ( ! [X2,X0,X3,X1] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 15.96/2.49    inference(cnf_transformation,[],[f41])).
% 15.96/2.49  
% 15.96/2.49  fof(f14,axiom,(
% 15.96/2.49    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 15.96/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.96/2.49  
% 15.96/2.49  fof(f38,plain,(
% 15.96/2.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 15.96/2.49    inference(ennf_transformation,[],[f14])).
% 15.96/2.49  
% 15.96/2.49  fof(f39,plain,(
% 15.96/2.49    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 15.96/2.49    inference(flattening,[],[f38])).
% 15.96/2.49  
% 15.96/2.49  fof(f70,plain,(
% 15.96/2.49    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 15.96/2.49    inference(cnf_transformation,[],[f39])).
% 15.96/2.49  
% 15.96/2.49  fof(f84,plain,(
% 15.96/2.49    r1_tarski(sK2,sK0)),
% 15.96/2.49    inference(cnf_transformation,[],[f54])).
% 15.96/2.49  
% 15.96/2.49  fof(f16,axiom,(
% 15.96/2.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 15.96/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.96/2.49  
% 15.96/2.49  fof(f42,plain,(
% 15.96/2.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.96/2.49    inference(ennf_transformation,[],[f16])).
% 15.96/2.49  
% 15.96/2.49  fof(f43,plain,(
% 15.96/2.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.96/2.49    inference(flattening,[],[f42])).
% 15.96/2.49  
% 15.96/2.49  fof(f52,plain,(
% 15.96/2.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.96/2.49    inference(nnf_transformation,[],[f43])).
% 15.96/2.49  
% 15.96/2.49  fof(f72,plain,(
% 15.96/2.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.96/2.49    inference(cnf_transformation,[],[f52])).
% 15.96/2.49  
% 15.96/2.49  fof(f82,plain,(
% 15.96/2.49    v1_funct_2(sK3,sK0,sK1)),
% 15.96/2.49    inference(cnf_transformation,[],[f54])).
% 15.96/2.49  
% 15.96/2.49  fof(f13,axiom,(
% 15.96/2.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 15.96/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.96/2.49  
% 15.96/2.49  fof(f37,plain,(
% 15.96/2.49    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.96/2.49    inference(ennf_transformation,[],[f13])).
% 15.96/2.49  
% 15.96/2.49  fof(f69,plain,(
% 15.96/2.49    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.96/2.49    inference(cnf_transformation,[],[f37])).
% 15.96/2.49  
% 15.96/2.49  fof(f9,axiom,(
% 15.96/2.49    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 15.96/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.96/2.49  
% 15.96/2.49  fof(f31,plain,(
% 15.96/2.49    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 15.96/2.49    inference(ennf_transformation,[],[f9])).
% 15.96/2.49  
% 15.96/2.49  fof(f32,plain,(
% 15.96/2.49    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 15.96/2.49    inference(flattening,[],[f31])).
% 15.96/2.49  
% 15.96/2.49  fof(f65,plain,(
% 15.96/2.49    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 15.96/2.49    inference(cnf_transformation,[],[f32])).
% 15.96/2.49  
% 15.96/2.49  fof(f3,axiom,(
% 15.96/2.49    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 15.96/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.96/2.49  
% 15.96/2.49  fof(f50,plain,(
% 15.96/2.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 15.96/2.49    inference(nnf_transformation,[],[f3])).
% 15.96/2.49  
% 15.96/2.49  fof(f51,plain,(
% 15.96/2.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 15.96/2.49    inference(flattening,[],[f50])).
% 15.96/2.49  
% 15.96/2.49  fof(f57,plain,(
% 15.96/2.49    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 15.96/2.49    inference(cnf_transformation,[],[f51])).
% 15.96/2.49  
% 15.96/2.49  fof(f58,plain,(
% 15.96/2.49    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 15.96/2.49    inference(cnf_transformation,[],[f51])).
% 15.96/2.49  
% 15.96/2.49  fof(f88,plain,(
% 15.96/2.49    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 15.96/2.49    inference(equality_resolution,[],[f58])).
% 15.96/2.49  
% 15.96/2.49  fof(f1,axiom,(
% 15.96/2.49    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 15.96/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.96/2.49  
% 15.96/2.49  fof(f22,plain,(
% 15.96/2.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 15.96/2.49    inference(ennf_transformation,[],[f1])).
% 15.96/2.49  
% 15.96/2.49  fof(f23,plain,(
% 15.96/2.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 15.96/2.49    inference(flattening,[],[f22])).
% 15.96/2.49  
% 15.96/2.49  fof(f55,plain,(
% 15.96/2.49    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 15.96/2.49    inference(cnf_transformation,[],[f23])).
% 15.96/2.49  
% 15.96/2.49  fof(f6,axiom,(
% 15.96/2.49    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 15.96/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.96/2.49  
% 15.96/2.49  fof(f28,plain,(
% 15.96/2.49    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 15.96/2.49    inference(ennf_transformation,[],[f6])).
% 15.96/2.49  
% 15.96/2.49  fof(f62,plain,(
% 15.96/2.49    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 15.96/2.49    inference(cnf_transformation,[],[f28])).
% 15.96/2.49  
% 15.96/2.49  fof(f8,axiom,(
% 15.96/2.49    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)))),
% 15.96/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.96/2.49  
% 15.96/2.49  fof(f30,plain,(
% 15.96/2.49    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 15.96/2.49    inference(ennf_transformation,[],[f8])).
% 15.96/2.49  
% 15.96/2.49  fof(f64,plain,(
% 15.96/2.49    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 15.96/2.49    inference(cnf_transformation,[],[f30])).
% 15.96/2.49  
% 15.96/2.49  fof(f2,axiom,(
% 15.96/2.49    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 15.96/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.96/2.49  
% 15.96/2.49  fof(f24,plain,(
% 15.96/2.49    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 15.96/2.49    inference(ennf_transformation,[],[f2])).
% 15.96/2.49  
% 15.96/2.49  fof(f56,plain,(
% 15.96/2.49    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 15.96/2.49    inference(cnf_transformation,[],[f24])).
% 15.96/2.49  
% 15.96/2.49  fof(f76,plain,(
% 15.96/2.49    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.96/2.49    inference(cnf_transformation,[],[f52])).
% 15.96/2.49  
% 15.96/2.49  fof(f91,plain,(
% 15.96/2.49    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 15.96/2.49    inference(equality_resolution,[],[f76])).
% 15.96/2.49  
% 15.96/2.49  fof(f59,plain,(
% 15.96/2.49    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 15.96/2.49    inference(cnf_transformation,[],[f51])).
% 15.96/2.49  
% 15.96/2.49  fof(f87,plain,(
% 15.96/2.49    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 15.96/2.49    inference(equality_resolution,[],[f59])).
% 15.96/2.49  
% 15.96/2.49  fof(f85,plain,(
% 15.96/2.49    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 15.96/2.49    inference(cnf_transformation,[],[f54])).
% 15.96/2.49  
% 15.96/2.49  fof(f74,plain,(
% 15.96/2.49    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.96/2.49    inference(cnf_transformation,[],[f52])).
% 15.96/2.49  
% 15.96/2.49  fof(f86,plain,(
% 15.96/2.49    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 15.96/2.49    inference(cnf_transformation,[],[f54])).
% 15.96/2.49  
% 15.96/2.49  fof(f78,plain,(
% 15.96/2.49    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 15.96/2.49    inference(cnf_transformation,[],[f45])).
% 15.96/2.49  
% 15.96/2.49  fof(f75,plain,(
% 15.96/2.49    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.96/2.49    inference(cnf_transformation,[],[f52])).
% 15.96/2.49  
% 15.96/2.49  fof(f92,plain,(
% 15.96/2.49    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 15.96/2.49    inference(equality_resolution,[],[f75])).
% 15.96/2.49  
% 15.96/2.49  fof(f77,plain,(
% 15.96/2.49    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.96/2.49    inference(cnf_transformation,[],[f52])).
% 15.96/2.49  
% 15.96/2.49  fof(f89,plain,(
% 15.96/2.49    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.96/2.49    inference(equality_resolution,[],[f77])).
% 15.96/2.49  
% 15.96/2.49  fof(f90,plain,(
% 15.96/2.49    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 15.96/2.49    inference(equality_resolution,[],[f89])).
% 15.96/2.49  
% 15.96/2.49  cnf(c_29,negated_conjecture,
% 15.96/2.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 15.96/2.49      inference(cnf_transformation,[],[f83]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_1154,plain,
% 15.96/2.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 15.96/2.49      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_25,plain,
% 15.96/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.96/2.49      | ~ v1_funct_1(X0)
% 15.96/2.49      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 15.96/2.49      inference(cnf_transformation,[],[f80]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_1156,plain,
% 15.96/2.49      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 15.96/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.96/2.49      | v1_funct_1(X2) != iProver_top ),
% 15.96/2.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_2161,plain,
% 15.96/2.49      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
% 15.96/2.49      | v1_funct_1(sK3) != iProver_top ),
% 15.96/2.49      inference(superposition,[status(thm)],[c_1154,c_1156]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_31,negated_conjecture,
% 15.96/2.49      ( v1_funct_1(sK3) ),
% 15.96/2.49      inference(cnf_transformation,[],[f81]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_1535,plain,
% 15.96/2.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 15.96/2.49      | ~ v1_funct_1(sK3)
% 15.96/2.49      | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
% 15.96/2.49      inference(instantiation,[status(thm)],[c_25]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_1721,plain,
% 15.96/2.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 15.96/2.49      | ~ v1_funct_1(sK3)
% 15.96/2.49      | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 15.96/2.49      inference(instantiation,[status(thm)],[c_1535]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_2489,plain,
% 15.96/2.49      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 15.96/2.49      inference(global_propositional_subsumption,
% 15.96/2.49                [status(thm)],
% 15.96/2.49                [c_2161,c_31,c_29,c_1721]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_23,plain,
% 15.96/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.96/2.49      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.96/2.49      | ~ v1_funct_1(X0) ),
% 15.96/2.49      inference(cnf_transformation,[],[f79]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_1158,plain,
% 15.96/2.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 15.96/2.49      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 15.96/2.49      | v1_funct_1(X0) != iProver_top ),
% 15.96/2.49      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_4054,plain,
% 15.96/2.49      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 15.96/2.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 15.96/2.49      | v1_funct_1(sK3) != iProver_top ),
% 15.96/2.49      inference(superposition,[status(thm)],[c_2489,c_1158]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_34,plain,
% 15.96/2.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 15.96/2.49      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_12,plain,
% 15.96/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.96/2.49      | v1_relat_1(X0) ),
% 15.96/2.49      inference(cnf_transformation,[],[f67]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_1417,plain,
% 15.96/2.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 15.96/2.49      | v1_relat_1(sK3) ),
% 15.96/2.49      inference(instantiation,[status(thm)],[c_12]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_1418,plain,
% 15.96/2.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 15.96/2.49      | v1_relat_1(sK3) = iProver_top ),
% 15.96/2.49      inference(predicate_to_equality,[status(thm)],[c_1417]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_8,plain,
% 15.96/2.49      ( r1_tarski(k7_relat_1(X0,X1),X0) | ~ v1_relat_1(X0) ),
% 15.96/2.49      inference(cnf_transformation,[],[f63]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_1561,plain,
% 15.96/2.49      ( r1_tarski(k7_relat_1(sK3,X0),sK3) | ~ v1_relat_1(sK3) ),
% 15.96/2.49      inference(instantiation,[status(thm)],[c_8]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_1567,plain,
% 15.96/2.49      ( r1_tarski(k7_relat_1(sK3,X0),sK3) = iProver_top
% 15.96/2.49      | v1_relat_1(sK3) != iProver_top ),
% 15.96/2.49      inference(predicate_to_equality,[status(thm)],[c_1561]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_16,plain,
% 15.96/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.96/2.49      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.96/2.49      | ~ r1_tarski(X3,X0) ),
% 15.96/2.49      inference(cnf_transformation,[],[f71]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_2605,plain,
% 15.96/2.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 15.96/2.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 15.96/2.49      | ~ r1_tarski(X0,sK3) ),
% 15.96/2.49      inference(instantiation,[status(thm)],[c_16]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_3687,plain,
% 15.96/2.49      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 15.96/2.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 15.96/2.49      | ~ r1_tarski(k7_relat_1(sK3,X0),sK3) ),
% 15.96/2.49      inference(instantiation,[status(thm)],[c_2605]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_3688,plain,
% 15.96/2.49      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 15.96/2.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 15.96/2.49      | r1_tarski(k7_relat_1(sK3,X0),sK3) != iProver_top ),
% 15.96/2.49      inference(predicate_to_equality,[status(thm)],[c_3687]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_5035,plain,
% 15.96/2.49      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 15.96/2.49      inference(global_propositional_subsumption,
% 15.96/2.49                [status(thm)],
% 15.96/2.49                [c_4054,c_34,c_1418,c_1567,c_3688]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_15,plain,
% 15.96/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.96/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 15.96/2.49      | ~ r1_tarski(k1_relat_1(X0),X3) ),
% 15.96/2.49      inference(cnf_transformation,[],[f70]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_1160,plain,
% 15.96/2.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 15.96/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) = iProver_top
% 15.96/2.49      | r1_tarski(k1_relat_1(X0),X3) != iProver_top ),
% 15.96/2.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_7155,plain,
% 15.96/2.49      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
% 15.96/2.49      | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X1) != iProver_top ),
% 15.96/2.49      inference(superposition,[status(thm)],[c_5035,c_1160]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_28,negated_conjecture,
% 15.96/2.49      ( r1_tarski(sK2,sK0) ),
% 15.96/2.49      inference(cnf_transformation,[],[f84]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_1155,plain,
% 15.96/2.49      ( r1_tarski(sK2,sK0) = iProver_top ),
% 15.96/2.49      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_22,plain,
% 15.96/2.49      ( ~ v1_funct_2(X0,X1,X2)
% 15.96/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.96/2.49      | k1_relset_1(X1,X2,X0) = X1
% 15.96/2.49      | k1_xboole_0 = X2 ),
% 15.96/2.49      inference(cnf_transformation,[],[f72]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_30,negated_conjecture,
% 15.96/2.49      ( v1_funct_2(sK3,sK0,sK1) ),
% 15.96/2.49      inference(cnf_transformation,[],[f82]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_441,plain,
% 15.96/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.96/2.49      | k1_relset_1(X1,X2,X0) = X1
% 15.96/2.49      | sK3 != X0
% 15.96/2.49      | sK1 != X2
% 15.96/2.49      | sK0 != X1
% 15.96/2.49      | k1_xboole_0 = X2 ),
% 15.96/2.49      inference(resolution_lifted,[status(thm)],[c_22,c_30]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_442,plain,
% 15.96/2.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 15.96/2.49      | k1_relset_1(sK0,sK1,sK3) = sK0
% 15.96/2.49      | k1_xboole_0 = sK1 ),
% 15.96/2.49      inference(unflattening,[status(thm)],[c_441]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_444,plain,
% 15.96/2.49      ( k1_relset_1(sK0,sK1,sK3) = sK0 | k1_xboole_0 = sK1 ),
% 15.96/2.49      inference(global_propositional_subsumption,
% 15.96/2.49                [status(thm)],
% 15.96/2.49                [c_442,c_29]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_14,plain,
% 15.96/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.96/2.49      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 15.96/2.49      inference(cnf_transformation,[],[f69]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_1161,plain,
% 15.96/2.49      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 15.96/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 15.96/2.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_3094,plain,
% 15.96/2.49      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 15.96/2.49      inference(superposition,[status(thm)],[c_1154,c_1161]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_3309,plain,
% 15.96/2.49      ( k1_relat_1(sK3) = sK0 | sK1 = k1_xboole_0 ),
% 15.96/2.49      inference(superposition,[status(thm)],[c_444,c_3094]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_10,plain,
% 15.96/2.49      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 15.96/2.49      | ~ v1_relat_1(X1)
% 15.96/2.49      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 15.96/2.49      inference(cnf_transformation,[],[f65]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_1164,plain,
% 15.96/2.49      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 15.96/2.49      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 15.96/2.49      | v1_relat_1(X0) != iProver_top ),
% 15.96/2.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_4640,plain,
% 15.96/2.49      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 15.96/2.49      | sK1 = k1_xboole_0
% 15.96/2.49      | r1_tarski(X0,sK0) != iProver_top
% 15.96/2.49      | v1_relat_1(sK3) != iProver_top ),
% 15.96/2.49      inference(superposition,[status(thm)],[c_3309,c_1164]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_5201,plain,
% 15.96/2.49      ( r1_tarski(X0,sK0) != iProver_top
% 15.96/2.49      | sK1 = k1_xboole_0
% 15.96/2.49      | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
% 15.96/2.49      inference(global_propositional_subsumption,
% 15.96/2.49                [status(thm)],
% 15.96/2.49                [c_4640,c_34,c_1418]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_5202,plain,
% 15.96/2.49      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 15.96/2.49      | sK1 = k1_xboole_0
% 15.96/2.49      | r1_tarski(X0,sK0) != iProver_top ),
% 15.96/2.49      inference(renaming,[status(thm)],[c_5201]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_5210,plain,
% 15.96/2.49      ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2 | sK1 = k1_xboole_0 ),
% 15.96/2.49      inference(superposition,[status(thm)],[c_1155,c_5202]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_4,plain,
% 15.96/2.49      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 15.96/2.49      | k1_xboole_0 = X0
% 15.96/2.49      | k1_xboole_0 = X1 ),
% 15.96/2.49      inference(cnf_transformation,[],[f57]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_96,plain,
% 15.96/2.49      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 15.96/2.49      | k1_xboole_0 = k1_xboole_0 ),
% 15.96/2.49      inference(instantiation,[status(thm)],[c_4]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_3,plain,
% 15.96/2.49      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 15.96/2.49      inference(cnf_transformation,[],[f88]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_97,plain,
% 15.96/2.49      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 15.96/2.49      inference(instantiation,[status(thm)],[c_3]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_0,plain,
% 15.96/2.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 15.96/2.49      inference(cnf_transformation,[],[f55]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_1463,plain,
% 15.96/2.49      ( r1_tarski(sK2,X0) | ~ r1_tarski(sK2,sK0) | ~ r1_tarski(sK0,X0) ),
% 15.96/2.49      inference(instantiation,[status(thm)],[c_0]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_1465,plain,
% 15.96/2.49      ( ~ r1_tarski(sK2,sK0)
% 15.96/2.49      | r1_tarski(sK2,k1_xboole_0)
% 15.96/2.49      | ~ r1_tarski(sK0,k1_xboole_0) ),
% 15.96/2.49      inference(instantiation,[status(thm)],[c_1463]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_7,plain,
% 15.96/2.49      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 15.96/2.49      inference(cnf_transformation,[],[f62]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_1562,plain,
% 15.96/2.49      ( r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X0)
% 15.96/2.49      | ~ v1_relat_1(sK3) ),
% 15.96/2.49      inference(instantiation,[status(thm)],[c_7]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_1564,plain,
% 15.96/2.49      ( r1_tarski(k1_relat_1(k7_relat_1(sK3,k1_xboole_0)),k1_xboole_0)
% 15.96/2.49      | ~ v1_relat_1(sK3) ),
% 15.96/2.49      inference(instantiation,[status(thm)],[c_1562]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_9,plain,
% 15.96/2.49      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),k1_relat_1(X0))
% 15.96/2.49      | ~ v1_relat_1(X0) ),
% 15.96/2.49      inference(cnf_transformation,[],[f64]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_1560,plain,
% 15.96/2.49      ( r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),k1_relat_1(sK3))
% 15.96/2.49      | ~ v1_relat_1(sK3) ),
% 15.96/2.49      inference(instantiation,[status(thm)],[c_9]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_1572,plain,
% 15.96/2.49      ( r1_tarski(k1_relat_1(k7_relat_1(sK3,k1_xboole_0)),k1_relat_1(sK3))
% 15.96/2.49      | ~ v1_relat_1(sK3) ),
% 15.96/2.49      inference(instantiation,[status(thm)],[c_1560]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_679,plain,
% 15.96/2.49      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 15.96/2.49      theory(equality) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_1870,plain,
% 15.96/2.49      ( r1_tarski(X0,X1)
% 15.96/2.49      | ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,X2)),X2)
% 15.96/2.49      | X1 != X2
% 15.96/2.49      | X0 != k1_relat_1(k7_relat_1(sK3,X2)) ),
% 15.96/2.49      inference(instantiation,[status(thm)],[c_679]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_1872,plain,
% 15.96/2.49      ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,k1_xboole_0)),k1_xboole_0)
% 15.96/2.49      | r1_tarski(k1_xboole_0,k1_xboole_0)
% 15.96/2.49      | k1_xboole_0 != k1_relat_1(k7_relat_1(sK3,k1_xboole_0))
% 15.96/2.49      | k1_xboole_0 != k1_xboole_0 ),
% 15.96/2.49      inference(instantiation,[status(thm)],[c_1870]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_1,plain,
% 15.96/2.49      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 15.96/2.49      inference(cnf_transformation,[],[f56]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_1879,plain,
% 15.96/2.49      ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,k1_xboole_0)),k1_xboole_0)
% 15.96/2.49      | k1_xboole_0 = k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) ),
% 15.96/2.49      inference(instantiation,[status(thm)],[c_1]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_18,plain,
% 15.96/2.49      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 15.96/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 15.96/2.49      | k1_xboole_0 = X1
% 15.96/2.49      | k1_xboole_0 = X0 ),
% 15.96/2.49      inference(cnf_transformation,[],[f91]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_373,plain,
% 15.96/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 15.96/2.49      | sK3 != X0
% 15.96/2.49      | sK1 != k1_xboole_0
% 15.96/2.49      | sK0 != X1
% 15.96/2.49      | k1_xboole_0 = X0
% 15.96/2.49      | k1_xboole_0 = X1 ),
% 15.96/2.49      inference(resolution_lifted,[status(thm)],[c_18,c_30]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_374,plain,
% 15.96/2.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
% 15.96/2.49      | sK1 != k1_xboole_0
% 15.96/2.49      | k1_xboole_0 = sK3
% 15.96/2.49      | k1_xboole_0 = sK0 ),
% 15.96/2.49      inference(unflattening,[status(thm)],[c_373]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_1150,plain,
% 15.96/2.49      ( sK1 != k1_xboole_0
% 15.96/2.49      | k1_xboole_0 = sK3
% 15.96/2.49      | k1_xboole_0 = sK0
% 15.96/2.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
% 15.96/2.49      inference(predicate_to_equality,[status(thm)],[c_374]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_2,plain,
% 15.96/2.49      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 15.96/2.49      inference(cnf_transformation,[],[f87]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_1252,plain,
% 15.96/2.49      ( sK3 = k1_xboole_0
% 15.96/2.49      | sK1 != k1_xboole_0
% 15.96/2.49      | sK0 = k1_xboole_0
% 15.96/2.49      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 15.96/2.49      inference(demodulation,[status(thm)],[c_1150,c_2]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_27,negated_conjecture,
% 15.96/2.49      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 15.96/2.49      inference(cnf_transformation,[],[f85]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_678,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_1473,plain,
% 15.96/2.49      ( sK0 != X0 | sK0 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 15.96/2.49      inference(instantiation,[status(thm)],[c_678]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_1859,plain,
% 15.96/2.49      ( sK0 != sK0 | sK0 = k1_xboole_0 | k1_xboole_0 != sK0 ),
% 15.96/2.49      inference(instantiation,[status(thm)],[c_1473]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_677,plain,( X0 = X0 ),theory(equality) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_1860,plain,
% 15.96/2.49      ( sK0 = sK0 ),
% 15.96/2.49      inference(instantiation,[status(thm)],[c_677]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_1934,plain,
% 15.96/2.49      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 15.96/2.49      inference(instantiation,[status(thm)],[c_678]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_1935,plain,
% 15.96/2.49      ( sK1 != k1_xboole_0
% 15.96/2.49      | k1_xboole_0 = sK1
% 15.96/2.49      | k1_xboole_0 != k1_xboole_0 ),
% 15.96/2.49      inference(instantiation,[status(thm)],[c_1934]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_1975,plain,
% 15.96/2.49      ( sK0 = k1_xboole_0 | sK1 != k1_xboole_0 ),
% 15.96/2.49      inference(global_propositional_subsumption,
% 15.96/2.49                [status(thm)],
% 15.96/2.49                [c_1252,c_27,c_96,c_97,c_1859,c_1860,c_1935]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_1976,plain,
% 15.96/2.49      ( sK1 != k1_xboole_0 | sK0 = k1_xboole_0 ),
% 15.96/2.49      inference(renaming,[status(thm)],[c_1975]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_1587,plain,
% 15.96/2.49      ( ~ r1_tarski(X0,k1_relat_1(sK3))
% 15.96/2.49      | ~ v1_relat_1(sK3)
% 15.96/2.49      | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
% 15.96/2.49      inference(instantiation,[status(thm)],[c_10]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_2226,plain,
% 15.96/2.49      ( ~ r1_tarski(sK2,k1_relat_1(sK3))
% 15.96/2.49      | ~ v1_relat_1(sK3)
% 15.96/2.49      | k1_relat_1(k7_relat_1(sK3,sK2)) = sK2 ),
% 15.96/2.49      inference(instantiation,[status(thm)],[c_1587]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_2620,plain,
% 15.96/2.49      ( ~ r1_tarski(X0,X1) | r1_tarski(sK0,X2) | X2 != X1 | sK0 != X0 ),
% 15.96/2.49      inference(instantiation,[status(thm)],[c_679]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_2622,plain,
% 15.96/2.49      ( r1_tarski(sK0,k1_xboole_0)
% 15.96/2.49      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 15.96/2.49      | sK0 != k1_xboole_0
% 15.96/2.49      | k1_xboole_0 != k1_xboole_0 ),
% 15.96/2.49      inference(instantiation,[status(thm)],[c_2620]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_1607,plain,
% 15.96/2.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(sK2,X0) | r1_tarski(sK2,X1) ),
% 15.96/2.49      inference(instantiation,[status(thm)],[c_0]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_2771,plain,
% 15.96/2.49      ( ~ r1_tarski(X0,k1_relat_1(sK3))
% 15.96/2.49      | ~ r1_tarski(sK2,X0)
% 15.96/2.49      | r1_tarski(sK2,k1_relat_1(sK3)) ),
% 15.96/2.49      inference(instantiation,[status(thm)],[c_1607]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_2773,plain,
% 15.96/2.49      ( r1_tarski(sK2,k1_relat_1(sK3))
% 15.96/2.49      | ~ r1_tarski(sK2,k1_xboole_0)
% 15.96/2.49      | ~ r1_tarski(k1_xboole_0,k1_relat_1(sK3)) ),
% 15.96/2.49      inference(instantiation,[status(thm)],[c_2771]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_1817,plain,
% 15.96/2.49      ( r1_tarski(X0,X1)
% 15.96/2.49      | ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,X2)),k1_relat_1(sK3))
% 15.96/2.49      | X0 != k1_relat_1(k7_relat_1(sK3,X2))
% 15.96/2.49      | X1 != k1_relat_1(sK3) ),
% 15.96/2.49      inference(instantiation,[status(thm)],[c_679]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_3484,plain,
% 15.96/2.49      ( r1_tarski(X0,k1_relat_1(sK3))
% 15.96/2.49      | ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,X1)),k1_relat_1(sK3))
% 15.96/2.49      | X0 != k1_relat_1(k7_relat_1(sK3,X1))
% 15.96/2.49      | k1_relat_1(sK3) != k1_relat_1(sK3) ),
% 15.96/2.49      inference(instantiation,[status(thm)],[c_1817]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_3487,plain,
% 15.96/2.49      ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,k1_xboole_0)),k1_relat_1(sK3))
% 15.96/2.49      | r1_tarski(k1_xboole_0,k1_relat_1(sK3))
% 15.96/2.49      | k1_relat_1(sK3) != k1_relat_1(sK3)
% 15.96/2.49      | k1_xboole_0 != k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) ),
% 15.96/2.49      inference(instantiation,[status(thm)],[c_3484]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_3485,plain,
% 15.96/2.49      ( k1_relat_1(sK3) = k1_relat_1(sK3) ),
% 15.96/2.49      inference(instantiation,[status(thm)],[c_677]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_5540,plain,
% 15.96/2.49      ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2 ),
% 15.96/2.49      inference(global_propositional_subsumption,
% 15.96/2.49                [status(thm)],
% 15.96/2.49                [c_5210,c_29,c_28,c_96,c_97,c_1417,c_1465,c_1564,c_1572,
% 15.96/2.49                 c_1872,c_1879,c_1976,c_2226,c_2622,c_2773,c_3487,c_3485]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_1167,plain,
% 15.96/2.49      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
% 15.96/2.49      | v1_relat_1(X0) != iProver_top ),
% 15.96/2.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_5544,plain,
% 15.96/2.49      ( r1_tarski(sK2,sK2) = iProver_top
% 15.96/2.49      | v1_relat_1(sK3) != iProver_top ),
% 15.96/2.49      inference(superposition,[status(thm)],[c_5540,c_1167]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_6365,plain,
% 15.96/2.49      ( r1_tarski(sK2,sK2) = iProver_top ),
% 15.96/2.49      inference(global_propositional_subsumption,
% 15.96/2.49                [status(thm)],
% 15.96/2.49                [c_5544,c_34,c_1418]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_1166,plain,
% 15.96/2.49      ( r1_tarski(k7_relat_1(X0,X1),X0) = iProver_top
% 15.96/2.49      | v1_relat_1(X0) != iProver_top ),
% 15.96/2.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_1159,plain,
% 15.96/2.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 15.96/2.49      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 15.96/2.49      | r1_tarski(X3,X0) != iProver_top ),
% 15.96/2.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_5590,plain,
% 15.96/2.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 15.96/2.49      | r1_tarski(X0,sK3) != iProver_top ),
% 15.96/2.49      inference(superposition,[status(thm)],[c_1154,c_1159]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_7154,plain,
% 15.96/2.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
% 15.96/2.49      | r1_tarski(X0,sK3) != iProver_top
% 15.96/2.49      | r1_tarski(k1_relat_1(X0),X1) != iProver_top ),
% 15.96/2.49      inference(superposition,[status(thm)],[c_5590,c_1160]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_10980,plain,
% 15.96/2.49      ( k1_relset_1(X0,sK1,X1) = k1_relat_1(X1)
% 15.96/2.49      | r1_tarski(X1,sK3) != iProver_top
% 15.96/2.49      | r1_tarski(k1_relat_1(X1),X0) != iProver_top ),
% 15.96/2.49      inference(superposition,[status(thm)],[c_7154,c_1161]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_42769,plain,
% 15.96/2.49      ( k1_relset_1(X0,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
% 15.96/2.49      | r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top
% 15.96/2.49      | r1_tarski(sK2,X0) != iProver_top ),
% 15.96/2.49      inference(superposition,[status(thm)],[c_5540,c_10980]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_42789,plain,
% 15.96/2.49      ( k1_relset_1(X0,sK1,k7_relat_1(sK3,sK2)) = sK2
% 15.96/2.49      | r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top
% 15.96/2.49      | r1_tarski(sK2,X0) != iProver_top ),
% 15.96/2.49      inference(light_normalisation,[status(thm)],[c_42769,c_5540]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_42908,plain,
% 15.96/2.49      ( k1_relset_1(X0,sK1,k7_relat_1(sK3,sK2)) = sK2
% 15.96/2.49      | r1_tarski(sK2,X0) != iProver_top
% 15.96/2.49      | v1_relat_1(sK3) != iProver_top ),
% 15.96/2.49      inference(superposition,[status(thm)],[c_1166,c_42789]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_43220,plain,
% 15.96/2.49      ( r1_tarski(sK2,X0) != iProver_top
% 15.96/2.49      | k1_relset_1(X0,sK1,k7_relat_1(sK3,sK2)) = sK2 ),
% 15.96/2.49      inference(global_propositional_subsumption,
% 15.96/2.49                [status(thm)],
% 15.96/2.49                [c_42908,c_34,c_1418]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_43221,plain,
% 15.96/2.49      ( k1_relset_1(X0,sK1,k7_relat_1(sK3,sK2)) = sK2
% 15.96/2.49      | r1_tarski(sK2,X0) != iProver_top ),
% 15.96/2.49      inference(renaming,[status(thm)],[c_43220]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_43233,plain,
% 15.96/2.49      ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) = sK2 ),
% 15.96/2.49      inference(superposition,[status(thm)],[c_6365,c_43221]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_20,plain,
% 15.96/2.49      ( v1_funct_2(X0,X1,X2)
% 15.96/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.96/2.49      | k1_relset_1(X1,X2,X0) != X1
% 15.96/2.49      | k1_xboole_0 = X2 ),
% 15.96/2.49      inference(cnf_transformation,[],[f74]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_26,negated_conjecture,
% 15.96/2.49      ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
% 15.96/2.49      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 15.96/2.49      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
% 15.96/2.49      inference(cnf_transformation,[],[f86]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_425,plain,
% 15.96/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.96/2.49      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 15.96/2.49      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 15.96/2.49      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 15.96/2.49      | k1_relset_1(X1,X2,X0) != X1
% 15.96/2.49      | sK2 != X1
% 15.96/2.49      | sK1 != X2
% 15.96/2.49      | k1_xboole_0 = X2 ),
% 15.96/2.49      inference(resolution_lifted,[status(thm)],[c_20,c_26]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_426,plain,
% 15.96/2.49      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 15.96/2.49      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 15.96/2.49      | k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 15.96/2.49      | k1_xboole_0 = sK1 ),
% 15.96/2.49      inference(unflattening,[status(thm)],[c_425]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_1147,plain,
% 15.96/2.49      ( k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 15.96/2.49      | k1_xboole_0 = sK1
% 15.96/2.49      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 15.96/2.49      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 15.96/2.49      inference(predicate_to_equality,[status(thm)],[c_426]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_2496,plain,
% 15.96/2.49      ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) != sK2
% 15.96/2.49      | sK1 = k1_xboole_0
% 15.96/2.49      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 15.96/2.49      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 15.96/2.49      inference(demodulation,[status(thm)],[c_2489,c_1147]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_43484,plain,
% 15.96/2.49      ( sK2 != sK2
% 15.96/2.49      | sK1 = k1_xboole_0
% 15.96/2.49      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 15.96/2.49      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 15.96/2.49      inference(demodulation,[status(thm)],[c_43233,c_2496]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_72495,plain,
% 15.96/2.49      ( sK1 = k1_xboole_0
% 15.96/2.49      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 15.96/2.49      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 15.96/2.49      inference(equality_resolution_simp,[status(thm)],[c_43484]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_24,plain,
% 15.96/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.96/2.49      | ~ v1_funct_1(X0)
% 15.96/2.49      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
% 15.96/2.49      inference(cnf_transformation,[],[f78]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_1157,plain,
% 15.96/2.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 15.96/2.49      | v1_funct_1(X0) != iProver_top
% 15.96/2.49      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
% 15.96/2.49      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_2784,plain,
% 15.96/2.49      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
% 15.96/2.49      | v1_funct_1(sK3) != iProver_top ),
% 15.96/2.49      inference(superposition,[status(thm)],[c_1154,c_1157]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_2801,plain,
% 15.96/2.49      ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top
% 15.96/2.49      | v1_funct_1(sK3) != iProver_top ),
% 15.96/2.49      inference(light_normalisation,[status(thm)],[c_2784,c_2489]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_32,plain,
% 15.96/2.49      ( v1_funct_1(sK3) = iProver_top ),
% 15.96/2.49      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_3731,plain,
% 15.96/2.49      ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 15.96/2.49      inference(global_propositional_subsumption,
% 15.96/2.49                [status(thm)],
% 15.96/2.49                [c_2801,c_32]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_72500,plain,
% 15.96/2.49      ( sK1 = k1_xboole_0
% 15.96/2.49      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 15.96/2.49      inference(forward_subsumption_resolution,
% 15.96/2.49                [status(thm)],
% 15.96/2.49                [c_72495,c_3731]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_72505,plain,
% 15.96/2.49      ( sK1 = k1_xboole_0
% 15.96/2.49      | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) != iProver_top ),
% 15.96/2.49      inference(superposition,[status(thm)],[c_7155,c_72500]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_72508,plain,
% 15.96/2.49      ( sK1 = k1_xboole_0 | r1_tarski(sK2,sK2) != iProver_top ),
% 15.96/2.49      inference(light_normalisation,[status(thm)],[c_72505,c_5540]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_72909,plain,
% 15.96/2.49      ( sK1 = k1_xboole_0 ),
% 15.96/2.49      inference(global_propositional_subsumption,
% 15.96/2.49                [status(thm)],
% 15.96/2.49                [c_72508,c_34,c_1418,c_5544]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_73045,plain,
% 15.96/2.49      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
% 15.96/2.49      inference(demodulation,[status(thm)],[c_72909,c_5035]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_73055,plain,
% 15.96/2.49      ( sK0 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 15.96/2.49      inference(demodulation,[status(thm)],[c_72909,c_27]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_73056,plain,
% 15.96/2.49      ( sK0 = k1_xboole_0 ),
% 15.96/2.49      inference(equality_resolution_simp,[status(thm)],[c_73055]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_73107,plain,
% 15.96/2.49      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 15.96/2.49      inference(light_normalisation,[status(thm)],[c_73045,c_73056]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_73109,plain,
% 15.96/2.49      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 15.96/2.49      inference(demodulation,[status(thm)],[c_73107,c_3]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_19,plain,
% 15.96/2.49      ( v1_funct_2(X0,k1_xboole_0,X1)
% 15.96/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 15.96/2.49      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 15.96/2.49      inference(cnf_transformation,[],[f92]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_393,plain,
% 15.96/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 15.96/2.49      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 15.96/2.49      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 15.96/2.49      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 15.96/2.49      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 15.96/2.49      | sK2 != k1_xboole_0
% 15.96/2.49      | sK1 != X1 ),
% 15.96/2.49      inference(resolution_lifted,[status(thm)],[c_19,c_26]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_394,plain,
% 15.96/2.49      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 15.96/2.49      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 15.96/2.49      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 15.96/2.49      | k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
% 15.96/2.49      | sK2 != k1_xboole_0 ),
% 15.96/2.49      inference(unflattening,[status(thm)],[c_393]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_1149,plain,
% 15.96/2.49      ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
% 15.96/2.49      | sK2 != k1_xboole_0
% 15.96/2.49      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 15.96/2.49      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
% 15.96/2.49      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 15.96/2.49      inference(predicate_to_equality,[status(thm)],[c_394]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_1320,plain,
% 15.96/2.49      ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
% 15.96/2.49      | sK2 != k1_xboole_0
% 15.96/2.49      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 15.96/2.49      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 15.96/2.49      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 15.96/2.49      inference(demodulation,[status(thm)],[c_1149,c_3]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_2493,plain,
% 15.96/2.49      ( k1_relset_1(k1_xboole_0,sK1,k7_relat_1(sK3,sK2)) != k1_xboole_0
% 15.96/2.49      | sK2 != k1_xboole_0
% 15.96/2.49      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 15.96/2.49      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 15.96/2.49      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 15.96/2.49      inference(demodulation,[status(thm)],[c_2489,c_1320]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_73047,plain,
% 15.96/2.49      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,sK2)) != k1_xboole_0
% 15.96/2.49      | sK2 != k1_xboole_0
% 15.96/2.49      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
% 15.96/2.49      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 15.96/2.49      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 15.96/2.49      inference(demodulation,[status(thm)],[c_72909,c_2493]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_17,plain,
% 15.96/2.49      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
% 15.96/2.49      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 15.96/2.49      | k1_xboole_0 = X0 ),
% 15.96/2.49      inference(cnf_transformation,[],[f90]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_347,plain,
% 15.96/2.49      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 15.96/2.49      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 15.96/2.49      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 15.96/2.49      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 15.96/2.49      | sK2 != X0
% 15.96/2.49      | sK1 != k1_xboole_0
% 15.96/2.49      | k1_xboole_0 = X0 ),
% 15.96/2.49      inference(resolution_lifted,[status(thm)],[c_17,c_26]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_348,plain,
% 15.96/2.49      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 15.96/2.49      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
% 15.96/2.49      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 15.96/2.49      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 15.96/2.49      | sK1 != k1_xboole_0
% 15.96/2.49      | k1_xboole_0 = sK2 ),
% 15.96/2.49      inference(unflattening,[status(thm)],[c_347]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_1151,plain,
% 15.96/2.49      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 15.96/2.49      | sK1 != k1_xboole_0
% 15.96/2.49      | k1_xboole_0 = sK2
% 15.96/2.49      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 15.96/2.49      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
% 15.96/2.49      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 15.96/2.49      inference(predicate_to_equality,[status(thm)],[c_348]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_1307,plain,
% 15.96/2.49      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 15.96/2.49      | sK2 = k1_xboole_0
% 15.96/2.49      | sK1 != k1_xboole_0
% 15.96/2.49      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 15.96/2.49      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 15.96/2.49      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 15.96/2.49      inference(demodulation,[status(thm)],[c_1151,c_2]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_2494,plain,
% 15.96/2.49      ( k7_relat_1(sK3,sK2) != k1_xboole_0
% 15.96/2.49      | sK2 = k1_xboole_0
% 15.96/2.49      | sK1 != k1_xboole_0
% 15.96/2.49      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 15.96/2.49      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 15.96/2.49      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 15.96/2.49      inference(demodulation,[status(thm)],[c_2489,c_1307]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_1611,plain,
% 15.96/2.49      ( ~ r1_tarski(sK2,k1_xboole_0) | k1_xboole_0 = sK2 ),
% 15.96/2.49      inference(instantiation,[status(thm)],[c_1]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_1520,plain,
% 15.96/2.49      ( r1_tarski(X0,X1) | ~ r1_tarski(sK2,sK0) | X0 != sK2 | X1 != sK0 ),
% 15.96/2.49      inference(instantiation,[status(thm)],[c_679]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_1645,plain,
% 15.96/2.49      ( r1_tarski(sK2,X0)
% 15.96/2.49      | ~ r1_tarski(sK2,sK0)
% 15.96/2.49      | X0 != sK0
% 15.96/2.49      | sK2 != sK2 ),
% 15.96/2.49      inference(instantiation,[status(thm)],[c_1520]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_1648,plain,
% 15.96/2.49      ( ~ r1_tarski(sK2,sK0)
% 15.96/2.49      | r1_tarski(sK2,k1_xboole_0)
% 15.96/2.49      | sK2 != sK2
% 15.96/2.49      | k1_xboole_0 != sK0 ),
% 15.96/2.49      inference(instantiation,[status(thm)],[c_1645]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_1646,plain,
% 15.96/2.49      ( sK2 = sK2 ),
% 15.96/2.49      inference(instantiation,[status(thm)],[c_677]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_1472,plain,
% 15.96/2.49      ( sK2 != X0 | sK2 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 15.96/2.49      inference(instantiation,[status(thm)],[c_678]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_1858,plain,
% 15.96/2.49      ( sK2 != sK2 | sK2 = k1_xboole_0 | k1_xboole_0 != sK2 ),
% 15.96/2.49      inference(instantiation,[status(thm)],[c_1472]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_1931,plain,
% 15.96/2.49      ( X0 != X1 | X0 = sK0 | sK0 != X1 ),
% 15.96/2.49      inference(instantiation,[status(thm)],[c_678]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_1932,plain,
% 15.96/2.49      ( sK0 != k1_xboole_0
% 15.96/2.49      | k1_xboole_0 = sK0
% 15.96/2.49      | k1_xboole_0 != k1_xboole_0 ),
% 15.96/2.49      inference(instantiation,[status(thm)],[c_1931]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_2689,plain,
% 15.96/2.49      ( sK1 != k1_xboole_0 | sK2 = k1_xboole_0 ),
% 15.96/2.49      inference(global_propositional_subsumption,
% 15.96/2.49                [status(thm)],
% 15.96/2.49                [c_2494,c_28,c_96,c_97,c_1611,c_1648,c_1646,c_1858,
% 15.96/2.49                 c_1932,c_1976]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_2690,plain,
% 15.96/2.49      ( sK2 = k1_xboole_0 | sK1 != k1_xboole_0 ),
% 15.96/2.49      inference(renaming,[status(thm)],[c_2689]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_73048,plain,
% 15.96/2.49      ( sK2 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 15.96/2.49      inference(demodulation,[status(thm)],[c_72909,c_2690]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_73083,plain,
% 15.96/2.49      ( sK2 = k1_xboole_0 ),
% 15.96/2.49      inference(equality_resolution_simp,[status(thm)],[c_73048]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_73094,plain,
% 15.96/2.49      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0
% 15.96/2.49      | k1_xboole_0 != k1_xboole_0
% 15.96/2.49      | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 15.96/2.49      | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 15.96/2.49      | v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
% 15.96/2.49      inference(light_normalisation,[status(thm)],[c_73047,c_73083]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_73095,plain,
% 15.96/2.49      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0
% 15.96/2.49      | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 15.96/2.49      | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 15.96/2.49      | v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
% 15.96/2.49      inference(equality_resolution_simp,[status(thm)],[c_73094]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_1162,plain,
% 15.96/2.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 15.96/2.49      | v1_relat_1(X0) = iProver_top ),
% 15.96/2.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_2282,plain,
% 15.96/2.49      ( v1_relat_1(sK3) = iProver_top ),
% 15.96/2.49      inference(superposition,[status(thm)],[c_1154,c_1162]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_1169,plain,
% 15.96/2.49      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 15.96/2.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_2926,plain,
% 15.96/2.49      ( k1_relat_1(k7_relat_1(X0,k1_xboole_0)) = k1_xboole_0
% 15.96/2.49      | v1_relat_1(X0) != iProver_top ),
% 15.96/2.49      inference(superposition,[status(thm)],[c_1167,c_1169]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_3927,plain,
% 15.96/2.49      ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
% 15.96/2.49      inference(superposition,[status(thm)],[c_2282,c_2926]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_34877,plain,
% 15.96/2.49      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 15.96/2.49      | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),k1_xboole_0) != iProver_top ),
% 15.96/2.49      inference(superposition,[status(thm)],[c_3,c_7155]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_37815,plain,
% 15.96/2.49      ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 15.96/2.49      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 15.96/2.49      inference(superposition,[status(thm)],[c_3927,c_34877]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_1563,plain,
% 15.96/2.49      ( r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X0) = iProver_top
% 15.96/2.49      | v1_relat_1(sK3) != iProver_top ),
% 15.96/2.49      inference(predicate_to_equality,[status(thm)],[c_1562]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_1565,plain,
% 15.96/2.49      ( r1_tarski(k1_relat_1(k7_relat_1(sK3,k1_xboole_0)),k1_xboole_0) = iProver_top
% 15.96/2.49      | v1_relat_1(sK3) != iProver_top ),
% 15.96/2.49      inference(instantiation,[status(thm)],[c_1563]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_1569,plain,
% 15.96/2.49      ( r1_tarski(k7_relat_1(sK3,k1_xboole_0),sK3) = iProver_top
% 15.96/2.49      | v1_relat_1(sK3) != iProver_top ),
% 15.96/2.49      inference(instantiation,[status(thm)],[c_1567]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_1871,plain,
% 15.96/2.49      ( X0 != X1
% 15.96/2.49      | X2 != k1_relat_1(k7_relat_1(sK3,X1))
% 15.96/2.49      | r1_tarski(X2,X0) = iProver_top
% 15.96/2.49      | r1_tarski(k1_relat_1(k7_relat_1(sK3,X1)),X1) != iProver_top ),
% 15.96/2.49      inference(predicate_to_equality,[status(thm)],[c_1870]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_1873,plain,
% 15.96/2.49      ( k1_xboole_0 != k1_relat_1(k7_relat_1(sK3,k1_xboole_0))
% 15.96/2.49      | k1_xboole_0 != k1_xboole_0
% 15.96/2.49      | r1_tarski(k1_relat_1(k7_relat_1(sK3,k1_xboole_0)),k1_xboole_0) != iProver_top
% 15.96/2.49      | r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 15.96/2.49      inference(instantiation,[status(thm)],[c_1871]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_10974,plain,
% 15.96/2.49      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 15.96/2.49      | r1_tarski(X0,sK3) != iProver_top
% 15.96/2.49      | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top ),
% 15.96/2.49      inference(superposition,[status(thm)],[c_3,c_7154]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_12227,plain,
% 15.96/2.49      ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 15.96/2.49      | r1_tarski(k7_relat_1(sK3,k1_xboole_0),sK3) != iProver_top
% 15.96/2.49      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 15.96/2.49      inference(superposition,[status(thm)],[c_3927,c_10974]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_38842,plain,
% 15.96/2.49      ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 15.96/2.49      inference(global_propositional_subsumption,
% 15.96/2.49                [status(thm)],
% 15.96/2.49                [c_37815,c_29,c_34,c_96,c_97,c_1417,c_1418,c_1564,c_1565,
% 15.96/2.49                 c_1569,c_1873,c_1879,c_12227]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_3096,plain,
% 15.96/2.49      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
% 15.96/2.49      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 15.96/2.49      inference(superposition,[status(thm)],[c_3,c_1161]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_38858,plain,
% 15.96/2.49      ( k1_relset_1(k1_xboole_0,X0,k7_relat_1(sK3,k1_xboole_0)) = k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) ),
% 15.96/2.49      inference(superposition,[status(thm)],[c_38842,c_3096]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_38864,plain,
% 15.96/2.49      ( k1_relset_1(k1_xboole_0,X0,k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
% 15.96/2.49      inference(light_normalisation,[status(thm)],[c_38858,c_3927]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_73100,plain,
% 15.96/2.49      ( k1_xboole_0 != k1_xboole_0
% 15.96/2.49      | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 15.96/2.49      | v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
% 15.96/2.49      inference(demodulation,[status(thm)],[c_73095,c_3,c_38864]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_73101,plain,
% 15.96/2.49      ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 15.96/2.49      | v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
% 15.96/2.49      inference(equality_resolution_simp,[status(thm)],[c_73100]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_73111,plain,
% 15.96/2.49      ( v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
% 15.96/2.49      inference(backward_subsumption_resolution,
% 15.96/2.49                [status(thm)],
% 15.96/2.49                [c_73109,c_73101]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(c_2809,plain,
% 15.96/2.49      ( v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) = iProver_top
% 15.96/2.49      | v1_funct_1(sK3) != iProver_top ),
% 15.96/2.49      inference(instantiation,[status(thm)],[c_2801]) ).
% 15.96/2.49  
% 15.96/2.49  cnf(contradiction,plain,
% 15.96/2.49      ( $false ),
% 15.96/2.49      inference(minisat,[status(thm)],[c_73111,c_2809,c_32]) ).
% 15.96/2.49  
% 15.96/2.49  
% 15.96/2.49  % SZS output end CNFRefutation for theBenchmark.p
% 15.96/2.49  
% 15.96/2.49  ------                               Statistics
% 15.96/2.49  
% 15.96/2.49  ------ Selected
% 15.96/2.49  
% 15.96/2.49  total_time:                             1.852
% 15.96/2.49  
%------------------------------------------------------------------------------
