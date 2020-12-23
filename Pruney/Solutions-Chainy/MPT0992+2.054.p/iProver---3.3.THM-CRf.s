%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:57 EST 2020

% Result     : Theorem 11.99s
% Output     : CNFRefutation 11.99s
% Verified   : 
% Statistics : Number of formulae       :  380 (5354 expanded)
%              Number of clauses        :  301 (2221 expanded)
%              Number of leaves         :   24 ( 964 expanded)
%              Depth                    :   22
%              Number of atoms          : 1062 (23350 expanded)
%              Number of equality atoms :  666 (7908 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,conjecture,(
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

fof(f21,negated_conjecture,(
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
    inference(negated_conjecture,[],[f20])).

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f44,f51])).

fof(f84,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f52])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f82,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f45])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f88,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f54])).

fof(f85,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f52])).

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

fof(f37,plain,(
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

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

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
    inference(nnf_transformation,[],[f38])).

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

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( r1_tarski(X0,X3)
       => m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(flattening,[],[f35])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f33])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

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

fof(f6,axiom,(
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
    inference(nnf_transformation,[],[f6])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
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
    inference(nnf_transformation,[],[f4])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f47])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f91,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f59])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f94,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f77])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f90,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f60])).

fof(f86,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f52])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f65,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f55,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1468,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1470,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_5106,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1468,c_1470])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_35,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_5398,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5106,c_35])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1471,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2325,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1468,c_1471])).

cnf(c_2459,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2325,c_35])).

cnf(c_5405,plain,
    ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5398,c_2459])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1487,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_31,negated_conjecture,
    ( r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1469,plain,
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

cnf(c_511,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X0
    | sK1 != X2
    | sK0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_33])).

cnf(c_512,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_511])).

cnf(c_514,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_512,c_32])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1475,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2582,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1468,c_1475])).

cnf(c_2730,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_514,c_2582])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1478,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2997,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2730,c_1478])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1476,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2424,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1468,c_1476])).

cnf(c_7793,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | sK1 = k1_xboole_0
    | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2997,c_2424])).

cnf(c_7794,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_7793])).

cnf(c_7802,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1469,c_7794])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X3,X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1473,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(X3,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2907,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1468,c_1473])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1474,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) = iProver_top
    | r1_tarski(k1_relat_1(X0),X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3493,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2907,c_1474])).

cnf(c_6526,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X2,sK3) != iProver_top
    | r1_tarski(k1_relat_1(X2),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3493,c_1473])).

cnf(c_43773,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
    | r1_tarski(X0,k7_relat_1(sK3,sK2)) != iProver_top
    | r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top
    | r1_tarski(sK2,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_7802,c_6526])).

cnf(c_13,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_11780,plain,
    ( r1_tarski(k7_relat_1(sK3,X0),sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_43625,plain,
    ( r1_tarski(k7_relat_1(sK3,sK2),sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_11780])).

cnf(c_43628,plain,
    ( r1_tarski(k7_relat_1(sK3,sK2),sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43625])).

cnf(c_43969,plain,
    ( r1_tarski(X0,k7_relat_1(sK3,sK2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
    | sK1 = k1_xboole_0
    | r1_tarski(sK2,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_43773,c_2424,c_43628])).

cnf(c_43970,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
    | r1_tarski(X0,k7_relat_1(sK3,sK2)) != iProver_top
    | r1_tarski(sK2,X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_43969])).

cnf(c_1479,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_6524,plain,
    ( k1_relset_1(X0,sK1,X1) = k1_relat_1(X1)
    | r1_tarski(X1,sK3) != iProver_top
    | r1_tarski(k1_relat_1(X1),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3493,c_1475])).

cnf(c_16543,plain,
    ( k1_relset_1(k1_relat_1(X0),sK1,X0) = k1_relat_1(X0)
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1487,c_6524])).

cnf(c_17077,plain,
    ( k1_relset_1(k1_relat_1(k7_relat_1(sK3,X0)),sK1,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0))
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1479,c_16543])).

cnf(c_26016,plain,
    ( k1_relset_1(k1_relat_1(k7_relat_1(sK3,X0)),sK1,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17077,c_2424])).

cnf(c_26021,plain,
    ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7802,c_26016])).

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

cnf(c_495,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_relset_1(X1,X2,X0) != X1
    | sK2 != X1
    | sK1 != X2
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_29])).

cnf(c_496,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_495])).

cnf(c_1462,plain,
    ( k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | k1_xboole_0 = sK1
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_496])).

cnf(c_5404,plain,
    ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) != sK2
    | sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5398,c_1462])).

cnf(c_26122,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_26021,c_5404])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_90,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_92,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_90])).

cnf(c_8,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_96,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_98,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_96])).

cnf(c_7,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_99,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_6,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_100,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_831,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1564,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK0,k1_xboole_0)
    | sK0 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_831])).

cnf(c_1565,plain,
    ( sK0 != X0
    | k1_xboole_0 != X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(sK0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1564])).

cnf(c_1567,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1565])).

cnf(c_9,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1617,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(sK0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1618,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1617])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_443,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK3 != X0
    | sK1 != k1_xboole_0
    | sK0 != X1
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_33])).

cnf(c_444,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0 ),
    inference(unflattening,[status(thm)],[c_443])).

cnf(c_1465,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_444])).

cnf(c_5,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1490,plain,
    ( sK3 = k1_xboole_0
    | sK1 != k1_xboole_0
    | sK0 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1465,c_5])).

cnf(c_30,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_830,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1536,plain,
    ( sK0 != X0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_830])).

cnf(c_1583,plain,
    ( sK0 != sK0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1536])).

cnf(c_829,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1685,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_829])).

cnf(c_1944,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_830])).

cnf(c_1945,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1944])).

cnf(c_2057,plain,
    ( sK0 = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1490,c_30,c_99,c_100,c_1583,c_1685,c_1945])).

cnf(c_2058,plain,
    ( sK1 != k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_2057])).

cnf(c_3495,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_1474])).

cnf(c_1482,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_5089,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(X0,k2_zfmisc_1(X1,X2)) = iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3495,c_1482])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1486,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2984,plain,
    ( r1_tarski(sK2,X0) = iProver_top
    | r1_tarski(sK0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1469,c_1486])).

cnf(c_32161,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k1_relat_1(sK0),X0) != iProver_top
    | r1_tarski(sK2,k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5089,c_2984])).

cnf(c_1558,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0))
    | r1_tarski(sK0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1559,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(sK0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1558])).

cnf(c_1484,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2904,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1484,c_1473])).

cnf(c_11398,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) = iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2904,c_1482])).

cnf(c_12130,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(X0,X1)) = iProver_top
    | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_11398,c_2984])).

cnf(c_32830,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(sK2,k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_32161,c_1559,c_12130])).

cnf(c_1483,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2905,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(X0,X3) != iProver_top
    | r1_tarski(X3,k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1483,c_1473])).

cnf(c_32844,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_32830,c_2905])).

cnf(c_34730,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(X0,k2_zfmisc_1(X1,X2)) = iProver_top
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_32844,c_1482])).

cnf(c_2381,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1468,c_1482])).

cnf(c_2985,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),X0) != iProver_top
    | r1_tarski(sK3,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2381,c_1486])).

cnf(c_51209,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k2_zfmisc_1(sK0,sK1),sK2) != iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_34730,c_2985])).

cnf(c_2711,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
    | r1_tarski(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_5525,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | r1_tarski(sK3,k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_2711])).

cnf(c_5526,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5525])).

cnf(c_2688,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(sK3),k1_xboole_0)
    | k1_relat_1(sK3) != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_831])).

cnf(c_5753,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | r1_tarski(k1_relat_1(sK3),k1_xboole_0)
    | k1_relat_1(sK3) != k1_relat_1(X0)
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_2688])).

cnf(c_5754,plain,
    ( k1_relat_1(sK3) != k1_relat_1(X0)
    | k1_xboole_0 != X1
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5753])).

cnf(c_5756,plain,
    ( k1_relat_1(sK3) != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0
    | r1_tarski(k1_relat_1(sK3),k1_xboole_0) = iProver_top
    | r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5754])).

cnf(c_2423,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1483,c_1476])).

cnf(c_7019,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1487,c_2423])).

cnf(c_4,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1485,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2995,plain,
    ( k1_relat_1(k7_relat_1(X0,k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1485,c_1478])).

cnf(c_8726,plain,
    ( k1_relat_1(k7_relat_1(k2_zfmisc_1(X0,X1),k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7019,c_2995])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1480,plain,
    ( k7_relat_1(X0,k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_8286,plain,
    ( k7_relat_1(k2_zfmisc_1(X0,X1),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7019,c_1480])).

cnf(c_8727,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_8726,c_8286])).

cnf(c_837,plain,
    ( X0 != X1
    | k1_relat_1(X0) = k1_relat_1(X1) ),
    theory(equality)).

cnf(c_12247,plain,
    ( k1_relat_1(sK3) = k1_relat_1(X0)
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_837])).

cnf(c_12248,plain,
    ( k1_relat_1(sK3) = k1_relat_1(k1_xboole_0)
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_12247])).

cnf(c_3492,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) = iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1468,c_1474])).

cnf(c_3944,plain,
    ( r1_tarski(k1_relat_1(sK3),X0) != iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(X0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3492,c_1482])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1488,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4274,plain,
    ( k2_zfmisc_1(X0,sK1) = sK3
    | r1_tarski(k2_zfmisc_1(X0,sK1),sK3) != iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3944,c_1488])).

cnf(c_15601,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK1) = sK3
    | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_4274])).

cnf(c_15602,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_15601,c_6])).

cnf(c_5686,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
    | r1_tarski(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_5687,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK3)) != iProver_top
    | r1_tarski(X0,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5686])).

cnf(c_5689,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) != iProver_top
    | r1_tarski(k1_xboole_0,sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_5687])).

cnf(c_15431,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_15432,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15431])).

cnf(c_16107,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_15602,c_5689,c_15432])).

cnf(c_16108,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_16107])).

cnf(c_16111,plain,
    ( sK3 = k1_xboole_0
    | sK1 = k1_xboole_0
    | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2730,c_16108])).

cnf(c_38,plain,
    ( r1_tarski(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_91,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_97,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1533,plain,
    ( ~ r1_tarski(sK0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK0)
    | sK0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1534,plain,
    ( sK0 = k1_xboole_0
    | r1_tarski(sK0,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1533])).

cnf(c_1719,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,sK0)
    | r1_tarski(X0,sK0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2118,plain,
    ( ~ r1_tarski(X0,sK2)
    | r1_tarski(X0,sK0)
    | ~ r1_tarski(sK2,sK0) ),
    inference(instantiation,[status(thm)],[c_1719])).

cnf(c_2119,plain,
    ( r1_tarski(X0,sK2) != iProver_top
    | r1_tarski(X0,sK0) = iProver_top
    | r1_tarski(sK2,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2118])).

cnf(c_2121,plain,
    ( r1_tarski(sK2,sK0) != iProver_top
    | r1_tarski(k1_xboole_0,sK2) != iProver_top
    | r1_tarski(k1_xboole_0,sK0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2119])).

cnf(c_2143,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_zfmisc_1(X2,X3),k1_xboole_0)
    | k2_zfmisc_1(X2,X3) != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_831])).

cnf(c_2145,plain,
    ( r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2143])).

cnf(c_2417,plain,
    ( r1_tarski(k1_xboole_0,sK2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2418,plain,
    ( r1_tarski(k1_xboole_0,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2417])).

cnf(c_2712,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(sK3,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2711])).

cnf(c_2714,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2712])).

cnf(c_2733,plain,
    ( ~ r1_tarski(X0,sK3)
    | ~ r1_tarski(sK3,X0)
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2735,plain,
    ( ~ r1_tarski(sK3,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK3)
    | sK3 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2733])).

cnf(c_2734,plain,
    ( sK3 = X0
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2733])).

cnf(c_2736,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(sK3,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2734])).

cnf(c_2990,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),X0)
    | r1_tarski(sK3,X0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2985])).

cnf(c_2992,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k1_xboole_0)
    | r1_tarski(sK3,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2990])).

cnf(c_3943,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_3492])).

cnf(c_4095,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2730,c_3943])).

cnf(c_5688,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3))
    | r1_tarski(k1_xboole_0,sK3) ),
    inference(instantiation,[status(thm)],[c_5686])).

cnf(c_5269,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_zfmisc_1(sK0,sK1),k1_xboole_0)
    | k2_zfmisc_1(sK0,sK1) != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_2143])).

cnf(c_11980,plain,
    ( ~ r1_tarski(k2_zfmisc_1(X0,X1),X2)
    | r1_tarski(k2_zfmisc_1(sK0,sK1),k1_xboole_0)
    | k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X0,X1)
    | k1_xboole_0 != X2 ),
    inference(instantiation,[status(thm)],[c_5269])).

cnf(c_11982,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k1_xboole_0)
    | ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_11980])).

cnf(c_832,plain,
    ( X0 != X1
    | X2 != X3
    | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
    theory(equality)).

cnf(c_12044,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(X0,X1)
    | sK1 != X1
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_832])).

cnf(c_12045,plain,
    ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | sK1 != k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_12044])).

cnf(c_16360,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16111,c_38,c_91,c_97,c_99,c_100,c_1534,c_2121,c_2145,c_2418,c_2714,c_2735,c_2736,c_2992,c_4095,c_5688,c_5689,c_11982,c_12045,c_15431,c_15432])).

cnf(c_37472,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(X2),k1_xboole_0)
    | k1_relat_1(X2) != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_831])).

cnf(c_37473,plain,
    ( k1_relat_1(X0) != X1
    | k1_xboole_0 != X2
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37472])).

cnf(c_37475,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_37473])).

cnf(c_11403,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(X0,X3) != iProver_top
    | r1_tarski(X3,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2904,c_1473])).

cnf(c_44470,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
    | r1_tarski(k2_zfmisc_1(X2,sK1),k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(sK3),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3944,c_11403])).

cnf(c_47016,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_44470])).

cnf(c_51733,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_51209,c_92,c_98,c_99,c_100,c_1559,c_5526,c_5756,c_8727,c_12248,c_16360,c_37475,c_47016])).

cnf(c_51739,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_51733])).

cnf(c_522,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != sK3
    | sK2 != sK0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_33])).

cnf(c_1545,plain,
    ( sK2 != X0
    | sK2 = sK0
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_830])).

cnf(c_1546,plain,
    ( sK2 = sK0
    | sK2 != k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1545])).

cnf(c_1553,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_831])).

cnf(c_1555,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | sK2 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1553])).

cnf(c_1688,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_829])).

cnf(c_1953,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_2144,plain,
    ( k2_zfmisc_1(X0,X1) != X2
    | k1_xboole_0 != X3
    | r1_tarski(X2,X3) != iProver_top
    | r1_tarski(k2_zfmisc_1(X0,X1),k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2143])).

cnf(c_2146,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2144])).

cnf(c_2429,plain,
    ( v1_relat_1(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2424])).

cnf(c_2477,plain,
    ( ~ r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_6154,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_partfun1(sK0,sK1,sK3,sK2)))
    | r1_tarski(X0,k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_6156,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_partfun1(sK0,sK1,sK3,sK2)))
    | r1_tarski(k1_xboole_0,k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(instantiation,[status(thm)],[c_6154])).

cnf(c_2865,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k1_xboole_0)
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_831])).

cnf(c_6177,plain,
    ( r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k1_xboole_0)
    | ~ r1_tarski(k7_relat_1(sK3,sK2),X0)
    | k2_partfun1(sK0,sK1,sK3,sK2) != k7_relat_1(sK3,sK2)
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_2865])).

cnf(c_6179,plain,
    ( r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k1_xboole_0)
    | ~ r1_tarski(k7_relat_1(sK3,sK2),k1_xboole_0)
    | k2_partfun1(sK0,sK1,sK3,sK2) != k7_relat_1(sK3,sK2)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6177])).

cnf(c_6521,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_3493])).

cnf(c_8438,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top
    | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7802,c_6521])).

cnf(c_8515,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top
    | r1_tarski(k7_relat_1(sK3,sK2),k1_xboole_0) = iProver_top
    | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8438,c_1482])).

cnf(c_8522,plain,
    ( ~ r1_tarski(k7_relat_1(sK3,sK2),sK3)
    | r1_tarski(k7_relat_1(sK3,sK2),k1_xboole_0)
    | ~ r1_tarski(sK2,k1_xboole_0)
    | sK1 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8515])).

cnf(c_8706,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_9391,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) = k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_829])).

cnf(c_11981,plain,
    ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X0,X1)
    | k1_xboole_0 != X2
    | r1_tarski(k2_zfmisc_1(X0,X1),X2) != iProver_top
    | r1_tarski(k2_zfmisc_1(sK0,sK1),k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11980])).

cnf(c_11983,plain,
    ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0
    | r1_tarski(k2_zfmisc_1(sK0,sK1),k1_xboole_0) = iProver_top
    | r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_11981])).

cnf(c_13613,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(sK0,sK1,sK3,sK2) = k7_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_834,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2777,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) != X1 ),
    inference(instantiation,[status(thm)],[c_834])).

cnf(c_5181,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_2777])).

cnf(c_18175,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k7_relat_1(sK3,sK2)
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_5181])).

cnf(c_18833,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_partfun1(sK0,sK1,sK3,sK2))) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_32842,plain,
    ( k2_zfmisc_1(X0,X1) = sK2
    | m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k2_zfmisc_1(X0,X1),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_32830,c_1488])).

cnf(c_33385,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = sK2
    | m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k1_xboole_0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_32842])).

cnf(c_33386,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k1_xboole_0,sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_33385,c_6])).

cnf(c_33715,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_33386,c_2418])).

cnf(c_33716,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_33715])).

cnf(c_5023,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(X1,X0) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_9727,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(X0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_5023])).

cnf(c_39710,plain,
    ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k7_relat_1(sK3,sK2),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_9727])).

cnf(c_51782,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k2_partfun1(sK0,sK1,sK3,sK2) = sK3
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_830])).

cnf(c_51784,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) = sK3
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_51782])).

cnf(c_2983,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k7_relat_1(X0,X2),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1479,c_1486])).

cnf(c_3185,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2907,c_1473])).

cnf(c_16946,plain,
    ( m1_subset_1(k7_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X2,sK3) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2983,c_3185])).

cnf(c_49282,plain,
    ( m1_subset_1(k7_relat_1(sK2,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | r1_tarski(sK0,sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1469,c_16946])).

cnf(c_4820,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | r1_tarski(sK0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1469,c_3185])).

cnf(c_5247,plain,
    ( r1_tarski(sK0,sK3) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4820,c_1476])).

cnf(c_49406,plain,
    ( r1_tarski(sK0,sK3) != iProver_top
    | m1_subset_1(k7_relat_1(sK2,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_49282,c_5247])).

cnf(c_49407,plain,
    ( m1_subset_1(k7_relat_1(sK2,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | r1_tarski(sK0,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_49406])).

cnf(c_49412,plain,
    ( r1_tarski(k7_relat_1(sK2,X0),k2_zfmisc_1(sK0,sK1)) = iProver_top
    | r1_tarski(sK0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_49407,c_1482])).

cnf(c_49617,plain,
    ( m1_subset_1(k7_relat_1(sK2,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(k2_zfmisc_1(sK0,sK1),k1_xboole_0) != iProver_top
    | r1_tarski(sK0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_49412,c_11403])).

cnf(c_37,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_1529,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK2)
    | sK2 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1530,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(sK2,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1529])).

cnf(c_1547,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | r1_tarski(sK2,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1548,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(sK2,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1547])).

cnf(c_1943,plain,
    ( k2_zfmisc_1(X0,sK1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1965,plain,
    ( k2_zfmisc_1(sK0,sK1) != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1943])).

cnf(c_2478,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) = k1_xboole_0
    | r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2477])).

cnf(c_2831,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(sK0,sK1))
    | k2_zfmisc_1(sK0,sK1) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2832,plain,
    ( k2_zfmisc_1(sK0,sK1) = k1_xboole_0
    | r1_tarski(k2_zfmisc_1(sK0,sK1),k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,k2_zfmisc_1(sK0,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2831])).

cnf(c_2991,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k1_xboole_0) != iProver_top
    | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2985])).

cnf(c_6155,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_partfun1(sK0,sK1,sK3,sK2))) != iProver_top
    | r1_tarski(X0,k2_partfun1(sK0,sK1,sK3,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6154])).

cnf(c_6157,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_partfun1(sK0,sK1,sK3,sK2))) != iProver_top
    | r1_tarski(k1_xboole_0,k2_partfun1(sK0,sK1,sK3,sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_6155])).

cnf(c_2433,plain,
    ( k7_relat_1(sK3,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2424,c_1480])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1472,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_5413,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5398,c_1472])).

cnf(c_6929,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5413,c_35,c_37])).

cnf(c_6942,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | r1_tarski(X0,k7_relat_1(sK3,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6929,c_1473])).

cnf(c_9444,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2433,c_6942])).

cnf(c_9877,plain,
    ( r1_tarski(X0,k2_zfmisc_1(sK0,sK1)) = iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9444,c_1482])).

cnf(c_9886,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(sK0,sK1)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_9877])).

cnf(c_18834,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_partfun1(sK0,sK1,sK3,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18833])).

cnf(c_3183,plain,
    ( r1_tarski(X0,k2_zfmisc_1(sK0,sK1)) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2907,c_1482])).

cnf(c_3481,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) = iProver_top
    | r1_tarski(sK0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3183,c_2984])).

cnf(c_2909,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_1473])).

cnf(c_2910,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2909,c_6])).

cnf(c_3089,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1483,c_2910])).

cnf(c_17847,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_zfmisc_1(sK0,sK1),k1_xboole_0) != iProver_top
    | r1_tarski(sK0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3481,c_3089])).

cnf(c_1609,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(sK2,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1610,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1609])).

cnf(c_1682,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_829])).

cnf(c_1735,plain,
    ( ~ r1_tarski(sK2,X0)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != sK2
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1553])).

cnf(c_2008,plain,
    ( ~ r1_tarski(sK2,sK0)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != sK2
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1735])).

cnf(c_2009,plain,
    ( sK2 != sK2
    | k1_xboole_0 != sK0
    | r1_tarski(sK2,sK0) != iProver_top
    | r1_tarski(sK2,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2008])).

cnf(c_19659,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k1_xboole_0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17847,c_38,c_30,c_92,c_98,c_1610,c_1682,c_1965,c_2009,c_2832,c_9886])).

cnf(c_19660,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_zfmisc_1(sK0,sK1),k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_19659])).

cnf(c_6118,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(X0))
    | r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),X0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_13564,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_6118])).

cnf(c_24015,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_13564])).

cnf(c_24016,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24015])).

cnf(c_2862,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | ~ r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),X0)
    | r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_28781,plain,
    ( ~ r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k2_zfmisc_1(sK0,sK1))
    | r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k1_xboole_0)
    | ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2862])).

cnf(c_28786,plain,
    ( r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k2_zfmisc_1(sK0,sK1)) != iProver_top
    | r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k1_xboole_0) = iProver_top
    | r1_tarski(k2_zfmisc_1(sK0,sK1),k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28781])).

cnf(c_2767,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),X0) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_28776,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k2_zfmisc_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_2767])).

cnf(c_5036,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | X2 != X0
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) != X1 ),
    inference(instantiation,[status(thm)],[c_834])).

cnf(c_10011,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | X1 != X0
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_5036])).

cnf(c_32996,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | m1_subset_1(k2_zfmisc_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | k2_zfmisc_1(sK0,sK1) != X0
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_10011])).

cnf(c_33001,plain,
    ( m1_subset_1(k2_zfmisc_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | k2_zfmisc_1(sK0,sK1) != k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_32996])).

cnf(c_44595,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_44596,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44595])).

cnf(c_51887,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_49617,c_34,c_35,c_32,c_37,c_30,c_92,c_98,c_522,c_1530,c_1546,c_1548,c_1583,c_1685,c_1688,c_1953,c_1965,c_2418,c_2478,c_2736,c_2832,c_2991,c_5689,c_6157,c_8706,c_9391,c_9886,c_15432,c_18834,c_19660,c_24015,c_24016,c_28786,c_28776,c_33001,c_44595,c_44596,c_51784])).

cnf(c_52013,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_51739,c_34,c_35,c_32,c_37,c_38,c_30,c_91,c_92,c_97,c_98,c_99,c_100,c_522,c_1530,c_1534,c_1546,c_1548,c_1555,c_1559,c_1583,c_1685,c_1688,c_1953,c_1965,c_2121,c_2146,c_2418,c_2429,c_2477,c_2478,c_2736,c_2832,c_2991,c_5689,c_6156,c_6157,c_6179,c_8522,c_8706,c_9391,c_9886,c_11983,c_12045,c_13613,c_15432,c_16360,c_18175,c_18833,c_18834,c_19660,c_24015,c_24016,c_28786,c_28776,c_33001,c_33716,c_39710,c_43625,c_44595,c_44596,c_51784])).

cnf(c_55668,plain,
    ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_26122,c_34,c_35,c_32,c_37,c_38,c_30,c_91,c_92,c_97,c_98,c_99,c_100,c_522,c_1530,c_1534,c_1546,c_1548,c_1555,c_1559,c_1567,c_1583,c_1618,c_1685,c_1688,c_1953,c_1965,c_2058,c_2121,c_2146,c_2418,c_2429,c_2477,c_2478,c_2736,c_2832,c_2991,c_5689,c_6156,c_6157,c_6179,c_7802,c_8522,c_8706,c_9391,c_9886,c_11983,c_12045,c_13613,c_15432,c_16360,c_18175,c_18833,c_18834,c_19660,c_24015,c_24016,c_28786,c_28776,c_33001,c_33716,c_39710,c_43625,c_44595,c_44596,c_51784])).

cnf(c_55678,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k7_relat_1(sK3,sK2),k7_relat_1(sK3,sK2)) != iProver_top
    | r1_tarski(sK2,sK2) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_43970,c_55668])).

cnf(c_2501,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2502,plain,
    ( r1_tarski(sK2,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2501])).

cnf(c_56343,plain,
    ( r1_tarski(k7_relat_1(sK3,sK2),k7_relat_1(sK3,sK2)) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_55678,c_34,c_35,c_32,c_37,c_38,c_30,c_91,c_92,c_97,c_98,c_99,c_100,c_522,c_1530,c_1534,c_1546,c_1548,c_1555,c_1559,c_1567,c_1583,c_1618,c_1685,c_1688,c_1953,c_1965,c_2058,c_2121,c_2146,c_2418,c_2429,c_2477,c_2478,c_2502,c_2736,c_2832,c_2991,c_5689,c_6156,c_6157,c_6179,c_8522,c_8706,c_9391,c_9886,c_11983,c_12045,c_13613,c_15432,c_16360,c_18175,c_18833,c_18834,c_19660,c_24015,c_24016,c_28786,c_28776,c_33001,c_33716,c_39710,c_43625,c_44595,c_44596,c_51784])).

cnf(c_56347,plain,
    ( v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1487,c_56343])).

cnf(c_56615,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_5405,c_56347])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:16:35 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  % Running in FOF mode
% 11.99/2.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.99/2.00  
% 11.99/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.99/2.00  
% 11.99/2.00  ------  iProver source info
% 11.99/2.00  
% 11.99/2.00  git: date: 2020-06-30 10:37:57 +0100
% 11.99/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.99/2.00  git: non_committed_changes: false
% 11.99/2.00  git: last_make_outside_of_git: false
% 11.99/2.00  
% 11.99/2.00  ------ 
% 11.99/2.00  
% 11.99/2.00  ------ Input Options
% 11.99/2.00  
% 11.99/2.00  --out_options                           all
% 11.99/2.00  --tptp_safe_out                         true
% 11.99/2.00  --problem_path                          ""
% 11.99/2.00  --include_path                          ""
% 11.99/2.00  --clausifier                            res/vclausify_rel
% 11.99/2.00  --clausifier_options                    ""
% 11.99/2.00  --stdin                                 false
% 11.99/2.00  --stats_out                             all
% 11.99/2.00  
% 11.99/2.00  ------ General Options
% 11.99/2.00  
% 11.99/2.00  --fof                                   false
% 11.99/2.00  --time_out_real                         305.
% 11.99/2.00  --time_out_virtual                      -1.
% 11.99/2.00  --symbol_type_check                     false
% 11.99/2.00  --clausify_out                          false
% 11.99/2.00  --sig_cnt_out                           false
% 11.99/2.00  --trig_cnt_out                          false
% 11.99/2.00  --trig_cnt_out_tolerance                1.
% 11.99/2.00  --trig_cnt_out_sk_spl                   false
% 11.99/2.00  --abstr_cl_out                          false
% 11.99/2.00  
% 11.99/2.00  ------ Global Options
% 11.99/2.00  
% 11.99/2.00  --schedule                              default
% 11.99/2.00  --add_important_lit                     false
% 11.99/2.00  --prop_solver_per_cl                    1000
% 11.99/2.00  --min_unsat_core                        false
% 11.99/2.00  --soft_assumptions                      false
% 11.99/2.00  --soft_lemma_size                       3
% 11.99/2.00  --prop_impl_unit_size                   0
% 11.99/2.00  --prop_impl_unit                        []
% 11.99/2.00  --share_sel_clauses                     true
% 11.99/2.00  --reset_solvers                         false
% 11.99/2.00  --bc_imp_inh                            [conj_cone]
% 11.99/2.00  --conj_cone_tolerance                   3.
% 11.99/2.00  --extra_neg_conj                        none
% 11.99/2.00  --large_theory_mode                     true
% 11.99/2.00  --prolific_symb_bound                   200
% 11.99/2.00  --lt_threshold                          2000
% 11.99/2.00  --clause_weak_htbl                      true
% 11.99/2.00  --gc_record_bc_elim                     false
% 11.99/2.00  
% 11.99/2.00  ------ Preprocessing Options
% 11.99/2.00  
% 11.99/2.00  --preprocessing_flag                    true
% 11.99/2.00  --time_out_prep_mult                    0.1
% 11.99/2.00  --splitting_mode                        input
% 11.99/2.00  --splitting_grd                         true
% 11.99/2.00  --splitting_cvd                         false
% 11.99/2.00  --splitting_cvd_svl                     false
% 11.99/2.00  --splitting_nvd                         32
% 11.99/2.00  --sub_typing                            true
% 11.99/2.00  --prep_gs_sim                           true
% 11.99/2.00  --prep_unflatten                        true
% 11.99/2.00  --prep_res_sim                          true
% 11.99/2.00  --prep_upred                            true
% 11.99/2.00  --prep_sem_filter                       exhaustive
% 11.99/2.00  --prep_sem_filter_out                   false
% 11.99/2.00  --pred_elim                             true
% 11.99/2.00  --res_sim_input                         true
% 11.99/2.00  --eq_ax_congr_red                       true
% 11.99/2.00  --pure_diseq_elim                       true
% 11.99/2.00  --brand_transform                       false
% 11.99/2.00  --non_eq_to_eq                          false
% 11.99/2.00  --prep_def_merge                        true
% 11.99/2.00  --prep_def_merge_prop_impl              false
% 11.99/2.00  --prep_def_merge_mbd                    true
% 11.99/2.00  --prep_def_merge_tr_red                 false
% 11.99/2.00  --prep_def_merge_tr_cl                  false
% 11.99/2.00  --smt_preprocessing                     true
% 11.99/2.00  --smt_ac_axioms                         fast
% 11.99/2.00  --preprocessed_out                      false
% 11.99/2.00  --preprocessed_stats                    false
% 11.99/2.00  
% 11.99/2.00  ------ Abstraction refinement Options
% 11.99/2.00  
% 11.99/2.00  --abstr_ref                             []
% 11.99/2.00  --abstr_ref_prep                        false
% 11.99/2.00  --abstr_ref_until_sat                   false
% 11.99/2.00  --abstr_ref_sig_restrict                funpre
% 11.99/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.99/2.00  --abstr_ref_under                       []
% 11.99/2.00  
% 11.99/2.00  ------ SAT Options
% 11.99/2.00  
% 11.99/2.00  --sat_mode                              false
% 11.99/2.00  --sat_fm_restart_options                ""
% 11.99/2.00  --sat_gr_def                            false
% 11.99/2.00  --sat_epr_types                         true
% 11.99/2.00  --sat_non_cyclic_types                  false
% 11.99/2.00  --sat_finite_models                     false
% 11.99/2.00  --sat_fm_lemmas                         false
% 11.99/2.00  --sat_fm_prep                           false
% 11.99/2.00  --sat_fm_uc_incr                        true
% 11.99/2.00  --sat_out_model                         small
% 11.99/2.00  --sat_out_clauses                       false
% 11.99/2.00  
% 11.99/2.00  ------ QBF Options
% 11.99/2.00  
% 11.99/2.00  --qbf_mode                              false
% 11.99/2.00  --qbf_elim_univ                         false
% 11.99/2.00  --qbf_dom_inst                          none
% 11.99/2.00  --qbf_dom_pre_inst                      false
% 11.99/2.00  --qbf_sk_in                             false
% 11.99/2.00  --qbf_pred_elim                         true
% 11.99/2.00  --qbf_split                             512
% 11.99/2.00  
% 11.99/2.00  ------ BMC1 Options
% 11.99/2.00  
% 11.99/2.00  --bmc1_incremental                      false
% 11.99/2.00  --bmc1_axioms                           reachable_all
% 11.99/2.00  --bmc1_min_bound                        0
% 11.99/2.00  --bmc1_max_bound                        -1
% 11.99/2.00  --bmc1_max_bound_default                -1
% 11.99/2.00  --bmc1_symbol_reachability              true
% 11.99/2.00  --bmc1_property_lemmas                  false
% 11.99/2.00  --bmc1_k_induction                      false
% 11.99/2.00  --bmc1_non_equiv_states                 false
% 11.99/2.00  --bmc1_deadlock                         false
% 11.99/2.00  --bmc1_ucm                              false
% 11.99/2.00  --bmc1_add_unsat_core                   none
% 11.99/2.00  --bmc1_unsat_core_children              false
% 11.99/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.99/2.00  --bmc1_out_stat                         full
% 11.99/2.00  --bmc1_ground_init                      false
% 11.99/2.00  --bmc1_pre_inst_next_state              false
% 11.99/2.00  --bmc1_pre_inst_state                   false
% 11.99/2.00  --bmc1_pre_inst_reach_state             false
% 11.99/2.00  --bmc1_out_unsat_core                   false
% 11.99/2.00  --bmc1_aig_witness_out                  false
% 11.99/2.00  --bmc1_verbose                          false
% 11.99/2.00  --bmc1_dump_clauses_tptp                false
% 11.99/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.99/2.00  --bmc1_dump_file                        -
% 11.99/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.99/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.99/2.00  --bmc1_ucm_extend_mode                  1
% 11.99/2.00  --bmc1_ucm_init_mode                    2
% 11.99/2.00  --bmc1_ucm_cone_mode                    none
% 11.99/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.99/2.00  --bmc1_ucm_relax_model                  4
% 11.99/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.99/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.99/2.00  --bmc1_ucm_layered_model                none
% 11.99/2.00  --bmc1_ucm_max_lemma_size               10
% 11.99/2.00  
% 11.99/2.00  ------ AIG Options
% 11.99/2.00  
% 11.99/2.00  --aig_mode                              false
% 11.99/2.00  
% 11.99/2.00  ------ Instantiation Options
% 11.99/2.00  
% 11.99/2.00  --instantiation_flag                    true
% 11.99/2.00  --inst_sos_flag                         true
% 11.99/2.00  --inst_sos_phase                        true
% 11.99/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.99/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.99/2.00  --inst_lit_sel_side                     num_symb
% 11.99/2.00  --inst_solver_per_active                1400
% 11.99/2.00  --inst_solver_calls_frac                1.
% 11.99/2.00  --inst_passive_queue_type               priority_queues
% 11.99/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.99/2.00  --inst_passive_queues_freq              [25;2]
% 11.99/2.00  --inst_dismatching                      true
% 11.99/2.00  --inst_eager_unprocessed_to_passive     true
% 11.99/2.00  --inst_prop_sim_given                   true
% 11.99/2.00  --inst_prop_sim_new                     false
% 11.99/2.00  --inst_subs_new                         false
% 11.99/2.00  --inst_eq_res_simp                      false
% 11.99/2.00  --inst_subs_given                       false
% 11.99/2.00  --inst_orphan_elimination               true
% 11.99/2.00  --inst_learning_loop_flag               true
% 11.99/2.00  --inst_learning_start                   3000
% 11.99/2.00  --inst_learning_factor                  2
% 11.99/2.00  --inst_start_prop_sim_after_learn       3
% 11.99/2.00  --inst_sel_renew                        solver
% 11.99/2.00  --inst_lit_activity_flag                true
% 11.99/2.00  --inst_restr_to_given                   false
% 11.99/2.00  --inst_activity_threshold               500
% 11.99/2.00  --inst_out_proof                        true
% 11.99/2.00  
% 11.99/2.00  ------ Resolution Options
% 11.99/2.00  
% 11.99/2.00  --resolution_flag                       true
% 11.99/2.00  --res_lit_sel                           adaptive
% 11.99/2.00  --res_lit_sel_side                      none
% 11.99/2.00  --res_ordering                          kbo
% 11.99/2.00  --res_to_prop_solver                    active
% 11.99/2.00  --res_prop_simpl_new                    false
% 11.99/2.00  --res_prop_simpl_given                  true
% 11.99/2.00  --res_passive_queue_type                priority_queues
% 11.99/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.99/2.00  --res_passive_queues_freq               [15;5]
% 11.99/2.00  --res_forward_subs                      full
% 11.99/2.00  --res_backward_subs                     full
% 11.99/2.00  --res_forward_subs_resolution           true
% 11.99/2.00  --res_backward_subs_resolution          true
% 11.99/2.00  --res_orphan_elimination                true
% 11.99/2.00  --res_time_limit                        2.
% 11.99/2.00  --res_out_proof                         true
% 11.99/2.00  
% 11.99/2.00  ------ Superposition Options
% 11.99/2.00  
% 11.99/2.00  --superposition_flag                    true
% 11.99/2.00  --sup_passive_queue_type                priority_queues
% 11.99/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.99/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.99/2.00  --demod_completeness_check              fast
% 11.99/2.00  --demod_use_ground                      true
% 11.99/2.00  --sup_to_prop_solver                    passive
% 11.99/2.00  --sup_prop_simpl_new                    true
% 11.99/2.00  --sup_prop_simpl_given                  true
% 11.99/2.00  --sup_fun_splitting                     true
% 11.99/2.00  --sup_smt_interval                      50000
% 11.99/2.00  
% 11.99/2.00  ------ Superposition Simplification Setup
% 11.99/2.00  
% 11.99/2.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.99/2.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.99/2.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.99/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.99/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.99/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.99/2.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.99/2.00  --sup_immed_triv                        [TrivRules]
% 11.99/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.99/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.99/2.00  --sup_immed_bw_main                     []
% 11.99/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.99/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.99/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.99/2.00  --sup_input_bw                          []
% 11.99/2.00  
% 11.99/2.00  ------ Combination Options
% 11.99/2.00  
% 11.99/2.00  --comb_res_mult                         3
% 11.99/2.00  --comb_sup_mult                         2
% 11.99/2.00  --comb_inst_mult                        10
% 11.99/2.00  
% 11.99/2.00  ------ Debug Options
% 11.99/2.00  
% 11.99/2.00  --dbg_backtrace                         false
% 11.99/2.00  --dbg_dump_prop_clauses                 false
% 11.99/2.00  --dbg_dump_prop_clauses_file            -
% 11.99/2.00  --dbg_out_stat                          false
% 11.99/2.00  ------ Parsing...
% 11.99/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.99/2.00  
% 11.99/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 11.99/2.00  
% 11.99/2.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.99/2.00  
% 11.99/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.99/2.00  ------ Proving...
% 11.99/2.00  ------ Problem Properties 
% 11.99/2.00  
% 11.99/2.00  
% 11.99/2.00  clauses                                 33
% 11.99/2.00  conjectures                             4
% 11.99/2.00  EPR                                     7
% 11.99/2.00  Horn                                    30
% 11.99/2.00  unary                                   8
% 11.99/2.00  binary                                  10
% 11.99/2.00  lits                                    80
% 11.99/2.00  lits eq                                 29
% 11.99/2.00  fd_pure                                 0
% 11.99/2.00  fd_pseudo                               0
% 11.99/2.00  fd_cond                                 1
% 11.99/2.00  fd_pseudo_cond                          1
% 11.99/2.00  AC symbols                              0
% 11.99/2.00  
% 11.99/2.00  ------ Schedule dynamic 5 is on 
% 11.99/2.00  
% 11.99/2.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.99/2.00  
% 11.99/2.00  
% 11.99/2.00  ------ 
% 11.99/2.00  Current options:
% 11.99/2.00  ------ 
% 11.99/2.00  
% 11.99/2.00  ------ Input Options
% 11.99/2.00  
% 11.99/2.00  --out_options                           all
% 11.99/2.00  --tptp_safe_out                         true
% 11.99/2.00  --problem_path                          ""
% 11.99/2.00  --include_path                          ""
% 11.99/2.00  --clausifier                            res/vclausify_rel
% 11.99/2.00  --clausifier_options                    ""
% 11.99/2.00  --stdin                                 false
% 11.99/2.00  --stats_out                             all
% 11.99/2.00  
% 11.99/2.00  ------ General Options
% 11.99/2.00  
% 11.99/2.00  --fof                                   false
% 11.99/2.00  --time_out_real                         305.
% 11.99/2.00  --time_out_virtual                      -1.
% 11.99/2.00  --symbol_type_check                     false
% 11.99/2.00  --clausify_out                          false
% 11.99/2.00  --sig_cnt_out                           false
% 11.99/2.00  --trig_cnt_out                          false
% 11.99/2.00  --trig_cnt_out_tolerance                1.
% 11.99/2.00  --trig_cnt_out_sk_spl                   false
% 11.99/2.00  --abstr_cl_out                          false
% 11.99/2.00  
% 11.99/2.00  ------ Global Options
% 11.99/2.00  
% 11.99/2.00  --schedule                              default
% 11.99/2.00  --add_important_lit                     false
% 11.99/2.00  --prop_solver_per_cl                    1000
% 11.99/2.00  --min_unsat_core                        false
% 11.99/2.00  --soft_assumptions                      false
% 11.99/2.00  --soft_lemma_size                       3
% 11.99/2.00  --prop_impl_unit_size                   0
% 11.99/2.00  --prop_impl_unit                        []
% 11.99/2.00  --share_sel_clauses                     true
% 11.99/2.00  --reset_solvers                         false
% 11.99/2.00  --bc_imp_inh                            [conj_cone]
% 11.99/2.00  --conj_cone_tolerance                   3.
% 11.99/2.00  --extra_neg_conj                        none
% 11.99/2.00  --large_theory_mode                     true
% 11.99/2.00  --prolific_symb_bound                   200
% 11.99/2.00  --lt_threshold                          2000
% 11.99/2.00  --clause_weak_htbl                      true
% 11.99/2.00  --gc_record_bc_elim                     false
% 11.99/2.00  
% 11.99/2.00  ------ Preprocessing Options
% 11.99/2.00  
% 11.99/2.00  --preprocessing_flag                    true
% 11.99/2.00  --time_out_prep_mult                    0.1
% 11.99/2.00  --splitting_mode                        input
% 11.99/2.00  --splitting_grd                         true
% 11.99/2.00  --splitting_cvd                         false
% 11.99/2.00  --splitting_cvd_svl                     false
% 11.99/2.00  --splitting_nvd                         32
% 11.99/2.00  --sub_typing                            true
% 11.99/2.00  --prep_gs_sim                           true
% 11.99/2.00  --prep_unflatten                        true
% 11.99/2.00  --prep_res_sim                          true
% 11.99/2.00  --prep_upred                            true
% 11.99/2.00  --prep_sem_filter                       exhaustive
% 11.99/2.00  --prep_sem_filter_out                   false
% 11.99/2.00  --pred_elim                             true
% 11.99/2.00  --res_sim_input                         true
% 11.99/2.00  --eq_ax_congr_red                       true
% 11.99/2.00  --pure_diseq_elim                       true
% 11.99/2.00  --brand_transform                       false
% 11.99/2.00  --non_eq_to_eq                          false
% 11.99/2.00  --prep_def_merge                        true
% 11.99/2.00  --prep_def_merge_prop_impl              false
% 11.99/2.00  --prep_def_merge_mbd                    true
% 11.99/2.00  --prep_def_merge_tr_red                 false
% 11.99/2.00  --prep_def_merge_tr_cl                  false
% 11.99/2.00  --smt_preprocessing                     true
% 11.99/2.00  --smt_ac_axioms                         fast
% 11.99/2.00  --preprocessed_out                      false
% 11.99/2.00  --preprocessed_stats                    false
% 11.99/2.00  
% 11.99/2.00  ------ Abstraction refinement Options
% 11.99/2.00  
% 11.99/2.00  --abstr_ref                             []
% 11.99/2.00  --abstr_ref_prep                        false
% 11.99/2.00  --abstr_ref_until_sat                   false
% 11.99/2.00  --abstr_ref_sig_restrict                funpre
% 11.99/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.99/2.00  --abstr_ref_under                       []
% 11.99/2.00  
% 11.99/2.00  ------ SAT Options
% 11.99/2.00  
% 11.99/2.00  --sat_mode                              false
% 11.99/2.00  --sat_fm_restart_options                ""
% 11.99/2.00  --sat_gr_def                            false
% 11.99/2.00  --sat_epr_types                         true
% 11.99/2.00  --sat_non_cyclic_types                  false
% 11.99/2.00  --sat_finite_models                     false
% 11.99/2.00  --sat_fm_lemmas                         false
% 11.99/2.00  --sat_fm_prep                           false
% 11.99/2.00  --sat_fm_uc_incr                        true
% 11.99/2.00  --sat_out_model                         small
% 11.99/2.00  --sat_out_clauses                       false
% 11.99/2.00  
% 11.99/2.00  ------ QBF Options
% 11.99/2.00  
% 11.99/2.00  --qbf_mode                              false
% 11.99/2.00  --qbf_elim_univ                         false
% 11.99/2.00  --qbf_dom_inst                          none
% 11.99/2.00  --qbf_dom_pre_inst                      false
% 11.99/2.00  --qbf_sk_in                             false
% 11.99/2.00  --qbf_pred_elim                         true
% 11.99/2.00  --qbf_split                             512
% 11.99/2.00  
% 11.99/2.00  ------ BMC1 Options
% 11.99/2.00  
% 11.99/2.00  --bmc1_incremental                      false
% 11.99/2.00  --bmc1_axioms                           reachable_all
% 11.99/2.00  --bmc1_min_bound                        0
% 11.99/2.00  --bmc1_max_bound                        -1
% 11.99/2.00  --bmc1_max_bound_default                -1
% 11.99/2.00  --bmc1_symbol_reachability              true
% 11.99/2.00  --bmc1_property_lemmas                  false
% 11.99/2.00  --bmc1_k_induction                      false
% 11.99/2.00  --bmc1_non_equiv_states                 false
% 11.99/2.00  --bmc1_deadlock                         false
% 11.99/2.00  --bmc1_ucm                              false
% 11.99/2.00  --bmc1_add_unsat_core                   none
% 11.99/2.00  --bmc1_unsat_core_children              false
% 11.99/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.99/2.00  --bmc1_out_stat                         full
% 11.99/2.00  --bmc1_ground_init                      false
% 11.99/2.00  --bmc1_pre_inst_next_state              false
% 11.99/2.00  --bmc1_pre_inst_state                   false
% 11.99/2.00  --bmc1_pre_inst_reach_state             false
% 11.99/2.00  --bmc1_out_unsat_core                   false
% 11.99/2.00  --bmc1_aig_witness_out                  false
% 11.99/2.00  --bmc1_verbose                          false
% 11.99/2.00  --bmc1_dump_clauses_tptp                false
% 11.99/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.99/2.00  --bmc1_dump_file                        -
% 11.99/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.99/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.99/2.00  --bmc1_ucm_extend_mode                  1
% 11.99/2.00  --bmc1_ucm_init_mode                    2
% 11.99/2.00  --bmc1_ucm_cone_mode                    none
% 11.99/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.99/2.00  --bmc1_ucm_relax_model                  4
% 11.99/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.99/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.99/2.00  --bmc1_ucm_layered_model                none
% 11.99/2.00  --bmc1_ucm_max_lemma_size               10
% 11.99/2.00  
% 11.99/2.00  ------ AIG Options
% 11.99/2.00  
% 11.99/2.00  --aig_mode                              false
% 11.99/2.00  
% 11.99/2.00  ------ Instantiation Options
% 11.99/2.00  
% 11.99/2.00  --instantiation_flag                    true
% 11.99/2.00  --inst_sos_flag                         true
% 11.99/2.00  --inst_sos_phase                        true
% 11.99/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.99/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.99/2.00  --inst_lit_sel_side                     none
% 11.99/2.00  --inst_solver_per_active                1400
% 11.99/2.00  --inst_solver_calls_frac                1.
% 11.99/2.00  --inst_passive_queue_type               priority_queues
% 11.99/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.99/2.00  --inst_passive_queues_freq              [25;2]
% 11.99/2.00  --inst_dismatching                      true
% 11.99/2.00  --inst_eager_unprocessed_to_passive     true
% 11.99/2.00  --inst_prop_sim_given                   true
% 11.99/2.00  --inst_prop_sim_new                     false
% 11.99/2.00  --inst_subs_new                         false
% 11.99/2.00  --inst_eq_res_simp                      false
% 11.99/2.00  --inst_subs_given                       false
% 11.99/2.00  --inst_orphan_elimination               true
% 11.99/2.00  --inst_learning_loop_flag               true
% 11.99/2.00  --inst_learning_start                   3000
% 11.99/2.00  --inst_learning_factor                  2
% 11.99/2.00  --inst_start_prop_sim_after_learn       3
% 11.99/2.00  --inst_sel_renew                        solver
% 11.99/2.00  --inst_lit_activity_flag                true
% 11.99/2.00  --inst_restr_to_given                   false
% 11.99/2.00  --inst_activity_threshold               500
% 11.99/2.00  --inst_out_proof                        true
% 11.99/2.00  
% 11.99/2.00  ------ Resolution Options
% 11.99/2.00  
% 11.99/2.00  --resolution_flag                       false
% 11.99/2.00  --res_lit_sel                           adaptive
% 11.99/2.00  --res_lit_sel_side                      none
% 11.99/2.00  --res_ordering                          kbo
% 11.99/2.00  --res_to_prop_solver                    active
% 11.99/2.00  --res_prop_simpl_new                    false
% 11.99/2.00  --res_prop_simpl_given                  true
% 11.99/2.00  --res_passive_queue_type                priority_queues
% 11.99/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.99/2.00  --res_passive_queues_freq               [15;5]
% 11.99/2.00  --res_forward_subs                      full
% 11.99/2.00  --res_backward_subs                     full
% 11.99/2.00  --res_forward_subs_resolution           true
% 11.99/2.00  --res_backward_subs_resolution          true
% 11.99/2.00  --res_orphan_elimination                true
% 11.99/2.00  --res_time_limit                        2.
% 11.99/2.00  --res_out_proof                         true
% 11.99/2.00  
% 11.99/2.00  ------ Superposition Options
% 11.99/2.00  
% 11.99/2.00  --superposition_flag                    true
% 11.99/2.00  --sup_passive_queue_type                priority_queues
% 11.99/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.99/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.99/2.00  --demod_completeness_check              fast
% 11.99/2.00  --demod_use_ground                      true
% 11.99/2.00  --sup_to_prop_solver                    passive
% 11.99/2.00  --sup_prop_simpl_new                    true
% 11.99/2.00  --sup_prop_simpl_given                  true
% 11.99/2.00  --sup_fun_splitting                     true
% 11.99/2.00  --sup_smt_interval                      50000
% 11.99/2.00  
% 11.99/2.00  ------ Superposition Simplification Setup
% 11.99/2.00  
% 11.99/2.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.99/2.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.99/2.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.99/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.99/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.99/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.99/2.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.99/2.00  --sup_immed_triv                        [TrivRules]
% 11.99/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.99/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.99/2.00  --sup_immed_bw_main                     []
% 11.99/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.99/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.99/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.99/2.00  --sup_input_bw                          []
% 11.99/2.00  
% 11.99/2.00  ------ Combination Options
% 11.99/2.00  
% 11.99/2.00  --comb_res_mult                         3
% 11.99/2.00  --comb_sup_mult                         2
% 11.99/2.00  --comb_inst_mult                        10
% 11.99/2.00  
% 11.99/2.00  ------ Debug Options
% 11.99/2.00  
% 11.99/2.00  --dbg_backtrace                         false
% 11.99/2.00  --dbg_dump_prop_clauses                 false
% 11.99/2.00  --dbg_dump_prop_clauses_file            -
% 11.99/2.00  --dbg_out_stat                          false
% 11.99/2.00  
% 11.99/2.00  
% 11.99/2.00  
% 11.99/2.00  
% 11.99/2.00  ------ Proving...
% 11.99/2.00  
% 11.99/2.00  
% 11.99/2.00  % SZS status Theorem for theBenchmark.p
% 11.99/2.00  
% 11.99/2.00   Resolution empty clause
% 11.99/2.00  
% 11.99/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 11.99/2.00  
% 11.99/2.00  fof(f20,conjecture,(
% 11.99/2.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 11.99/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.99/2.00  
% 11.99/2.00  fof(f21,negated_conjecture,(
% 11.99/2.00    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 11.99/2.00    inference(negated_conjecture,[],[f20])).
% 11.99/2.00  
% 11.99/2.00  fof(f43,plain,(
% 11.99/2.00    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 11.99/2.00    inference(ennf_transformation,[],[f21])).
% 11.99/2.00  
% 11.99/2.00  fof(f44,plain,(
% 11.99/2.00    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 11.99/2.00    inference(flattening,[],[f43])).
% 11.99/2.00  
% 11.99/2.00  fof(f51,plain,(
% 11.99/2.00    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 11.99/2.00    introduced(choice_axiom,[])).
% 11.99/2.00  
% 11.99/2.00  fof(f52,plain,(
% 11.99/2.00    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 11.99/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f44,f51])).
% 11.99/2.00  
% 11.99/2.00  fof(f84,plain,(
% 11.99/2.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 11.99/2.00    inference(cnf_transformation,[],[f52])).
% 11.99/2.00  
% 11.99/2.00  fof(f19,axiom,(
% 11.99/2.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 11.99/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.99/2.00  
% 11.99/2.00  fof(f41,plain,(
% 11.99/2.00    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 11.99/2.00    inference(ennf_transformation,[],[f19])).
% 11.99/2.00  
% 11.99/2.00  fof(f42,plain,(
% 11.99/2.00    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 11.99/2.00    inference(flattening,[],[f41])).
% 11.99/2.00  
% 11.99/2.00  fof(f81,plain,(
% 11.99/2.00    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 11.99/2.00    inference(cnf_transformation,[],[f42])).
% 11.99/2.00  
% 11.99/2.00  fof(f82,plain,(
% 11.99/2.00    v1_funct_1(sK3)),
% 11.99/2.00    inference(cnf_transformation,[],[f52])).
% 11.99/2.00  
% 11.99/2.00  fof(f18,axiom,(
% 11.99/2.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 11.99/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.99/2.00  
% 11.99/2.00  fof(f39,plain,(
% 11.99/2.00    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 11.99/2.00    inference(ennf_transformation,[],[f18])).
% 11.99/2.00  
% 11.99/2.00  fof(f40,plain,(
% 11.99/2.00    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 11.99/2.00    inference(flattening,[],[f39])).
% 11.99/2.00  
% 11.99/2.00  fof(f79,plain,(
% 11.99/2.00    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 11.99/2.00    inference(cnf_transformation,[],[f40])).
% 11.99/2.00  
% 11.99/2.00  fof(f1,axiom,(
% 11.99/2.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.99/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.99/2.00  
% 11.99/2.00  fof(f45,plain,(
% 11.99/2.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.99/2.00    inference(nnf_transformation,[],[f1])).
% 11.99/2.00  
% 11.99/2.00  fof(f46,plain,(
% 11.99/2.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.99/2.00    inference(flattening,[],[f45])).
% 11.99/2.00  
% 11.99/2.00  fof(f54,plain,(
% 11.99/2.00    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 11.99/2.00    inference(cnf_transformation,[],[f46])).
% 11.99/2.00  
% 11.99/2.00  fof(f88,plain,(
% 11.99/2.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.99/2.00    inference(equality_resolution,[],[f54])).
% 11.99/2.00  
% 11.99/2.00  fof(f85,plain,(
% 11.99/2.00    r1_tarski(sK2,sK0)),
% 11.99/2.00    inference(cnf_transformation,[],[f52])).
% 11.99/2.00  
% 11.99/2.00  fof(f17,axiom,(
% 11.99/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 11.99/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.99/2.00  
% 11.99/2.00  fof(f37,plain,(
% 11.99/2.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.99/2.00    inference(ennf_transformation,[],[f17])).
% 11.99/2.00  
% 11.99/2.00  fof(f38,plain,(
% 11.99/2.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.99/2.00    inference(flattening,[],[f37])).
% 11.99/2.00  
% 11.99/2.00  fof(f50,plain,(
% 11.99/2.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.99/2.00    inference(nnf_transformation,[],[f38])).
% 11.99/2.00  
% 11.99/2.00  fof(f73,plain,(
% 11.99/2.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.99/2.00    inference(cnf_transformation,[],[f50])).
% 11.99/2.00  
% 11.99/2.00  fof(f83,plain,(
% 11.99/2.00    v1_funct_2(sK3,sK0,sK1)),
% 11.99/2.00    inference(cnf_transformation,[],[f52])).
% 11.99/2.00  
% 11.99/2.00  fof(f14,axiom,(
% 11.99/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 11.99/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.99/2.00  
% 11.99/2.00  fof(f32,plain,(
% 11.99/2.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.99/2.00    inference(ennf_transformation,[],[f14])).
% 11.99/2.00  
% 11.99/2.00  fof(f70,plain,(
% 11.99/2.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.99/2.00    inference(cnf_transformation,[],[f32])).
% 11.99/2.00  
% 11.99/2.00  fof(f11,axiom,(
% 11.99/2.00    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 11.99/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.99/2.00  
% 11.99/2.00  fof(f28,plain,(
% 11.99/2.00    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 11.99/2.00    inference(ennf_transformation,[],[f11])).
% 11.99/2.00  
% 11.99/2.00  fof(f29,plain,(
% 11.99/2.00    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 11.99/2.00    inference(flattening,[],[f28])).
% 11.99/2.00  
% 11.99/2.00  fof(f67,plain,(
% 11.99/2.00    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 11.99/2.00    inference(cnf_transformation,[],[f29])).
% 11.99/2.00  
% 11.99/2.00  fof(f13,axiom,(
% 11.99/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 11.99/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.99/2.00  
% 11.99/2.00  fof(f31,plain,(
% 11.99/2.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.99/2.00    inference(ennf_transformation,[],[f13])).
% 11.99/2.00  
% 11.99/2.00  fof(f69,plain,(
% 11.99/2.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.99/2.00    inference(cnf_transformation,[],[f31])).
% 11.99/2.00  
% 11.99/2.00  fof(f16,axiom,(
% 11.99/2.00    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => (r1_tarski(X0,X3) => m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 11.99/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.99/2.00  
% 11.99/2.00  fof(f35,plain,(
% 11.99/2.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 11.99/2.00    inference(ennf_transformation,[],[f16])).
% 11.99/2.00  
% 11.99/2.00  fof(f36,plain,(
% 11.99/2.00    ! [X0,X1,X2,X3] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 11.99/2.00    inference(flattening,[],[f35])).
% 11.99/2.00  
% 11.99/2.00  fof(f72,plain,(
% 11.99/2.00    ( ! [X2,X0,X3,X1] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 11.99/2.00    inference(cnf_transformation,[],[f36])).
% 11.99/2.00  
% 11.99/2.00  fof(f15,axiom,(
% 11.99/2.00    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 11.99/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.99/2.00  
% 11.99/2.00  fof(f33,plain,(
% 11.99/2.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 11.99/2.00    inference(ennf_transformation,[],[f15])).
% 11.99/2.00  
% 11.99/2.00  fof(f34,plain,(
% 11.99/2.00    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 11.99/2.00    inference(flattening,[],[f33])).
% 11.99/2.00  
% 11.99/2.00  fof(f71,plain,(
% 11.99/2.00    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 11.99/2.00    inference(cnf_transformation,[],[f34])).
% 11.99/2.00  
% 11.99/2.00  fof(f10,axiom,(
% 11.99/2.00    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 11.99/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.99/2.00  
% 11.99/2.00  fof(f27,plain,(
% 11.99/2.00    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 11.99/2.00    inference(ennf_transformation,[],[f10])).
% 11.99/2.00  
% 11.99/2.00  fof(f66,plain,(
% 11.99/2.00    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 11.99/2.00    inference(cnf_transformation,[],[f27])).
% 11.99/2.00  
% 11.99/2.00  fof(f75,plain,(
% 11.99/2.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.99/2.00    inference(cnf_transformation,[],[f50])).
% 11.99/2.00  
% 11.99/2.00  fof(f87,plain,(
% 11.99/2.00    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 11.99/2.00    inference(cnf_transformation,[],[f52])).
% 11.99/2.00  
% 11.99/2.00  fof(f6,axiom,(
% 11.99/2.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 11.99/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.99/2.00  
% 11.99/2.00  fof(f49,plain,(
% 11.99/2.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 11.99/2.00    inference(nnf_transformation,[],[f6])).
% 11.99/2.00  
% 11.99/2.00  fof(f62,plain,(
% 11.99/2.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 11.99/2.00    inference(cnf_transformation,[],[f49])).
% 11.99/2.00  
% 11.99/2.00  fof(f5,axiom,(
% 11.99/2.00    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 11.99/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.99/2.00  
% 11.99/2.00  fof(f61,plain,(
% 11.99/2.00    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 11.99/2.00    inference(cnf_transformation,[],[f5])).
% 11.99/2.00  
% 11.99/2.00  fof(f4,axiom,(
% 11.99/2.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 11.99/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.99/2.00  
% 11.99/2.00  fof(f47,plain,(
% 11.99/2.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 11.99/2.00    inference(nnf_transformation,[],[f4])).
% 11.99/2.00  
% 11.99/2.00  fof(f48,plain,(
% 11.99/2.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 11.99/2.00    inference(flattening,[],[f47])).
% 11.99/2.00  
% 11.99/2.00  fof(f58,plain,(
% 11.99/2.00    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 11.99/2.00    inference(cnf_transformation,[],[f48])).
% 11.99/2.00  
% 11.99/2.00  fof(f59,plain,(
% 11.99/2.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 11.99/2.00    inference(cnf_transformation,[],[f48])).
% 11.99/2.00  
% 11.99/2.00  fof(f91,plain,(
% 11.99/2.00    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 11.99/2.00    inference(equality_resolution,[],[f59])).
% 11.99/2.00  
% 11.99/2.00  fof(f63,plain,(
% 11.99/2.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 11.99/2.00    inference(cnf_transformation,[],[f49])).
% 11.99/2.00  
% 11.99/2.00  fof(f77,plain,(
% 11.99/2.00    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.99/2.00    inference(cnf_transformation,[],[f50])).
% 11.99/2.00  
% 11.99/2.00  fof(f94,plain,(
% 11.99/2.00    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 11.99/2.00    inference(equality_resolution,[],[f77])).
% 11.99/2.00  
% 11.99/2.00  fof(f60,plain,(
% 11.99/2.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 11.99/2.00    inference(cnf_transformation,[],[f48])).
% 11.99/2.00  
% 11.99/2.00  fof(f90,plain,(
% 11.99/2.00    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 11.99/2.00    inference(equality_resolution,[],[f60])).
% 11.99/2.00  
% 11.99/2.00  fof(f86,plain,(
% 11.99/2.00    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 11.99/2.00    inference(cnf_transformation,[],[f52])).
% 11.99/2.00  
% 11.99/2.00  fof(f2,axiom,(
% 11.99/2.00    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 11.99/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.99/2.00  
% 11.99/2.00  fof(f23,plain,(
% 11.99/2.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 11.99/2.00    inference(ennf_transformation,[],[f2])).
% 11.99/2.00  
% 11.99/2.00  fof(f24,plain,(
% 11.99/2.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 11.99/2.00    inference(flattening,[],[f23])).
% 11.99/2.00  
% 11.99/2.00  fof(f56,plain,(
% 11.99/2.00    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 11.99/2.00    inference(cnf_transformation,[],[f24])).
% 11.99/2.00  
% 11.99/2.00  fof(f3,axiom,(
% 11.99/2.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 11.99/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.99/2.00  
% 11.99/2.00  fof(f57,plain,(
% 11.99/2.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 11.99/2.00    inference(cnf_transformation,[],[f3])).
% 11.99/2.00  
% 11.99/2.00  fof(f9,axiom,(
% 11.99/2.00    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0))),
% 11.99/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.99/2.00  
% 11.99/2.00  fof(f26,plain,(
% 11.99/2.00    ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 11.99/2.00    inference(ennf_transformation,[],[f9])).
% 11.99/2.00  
% 11.99/2.00  fof(f65,plain,(
% 11.99/2.00    ( ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 11.99/2.00    inference(cnf_transformation,[],[f26])).
% 11.99/2.00  
% 11.99/2.00  fof(f55,plain,(
% 11.99/2.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 11.99/2.00    inference(cnf_transformation,[],[f46])).
% 11.99/2.00  
% 11.99/2.00  fof(f80,plain,(
% 11.99/2.00    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 11.99/2.00    inference(cnf_transformation,[],[f40])).
% 11.99/2.00  
% 11.99/2.00  cnf(c_32,negated_conjecture,
% 11.99/2.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 11.99/2.00      inference(cnf_transformation,[],[f84]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1468,plain,
% 11.99/2.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_28,plain,
% 11.99/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.99/2.00      | ~ v1_funct_1(X0)
% 11.99/2.00      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 11.99/2.00      inference(cnf_transformation,[],[f81]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1470,plain,
% 11.99/2.00      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 11.99/2.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.99/2.00      | v1_funct_1(X2) != iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_5106,plain,
% 11.99/2.00      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
% 11.99/2.00      | v1_funct_1(sK3) != iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_1468,c_1470]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_34,negated_conjecture,
% 11.99/2.00      ( v1_funct_1(sK3) ),
% 11.99/2.00      inference(cnf_transformation,[],[f82]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_35,plain,
% 11.99/2.00      ( v1_funct_1(sK3) = iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_5398,plain,
% 11.99/2.00      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 11.99/2.00      inference(global_propositional_subsumption,[status(thm)],[c_5106,c_35]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_27,plain,
% 11.99/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.99/2.00      | ~ v1_funct_1(X0)
% 11.99/2.00      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
% 11.99/2.00      inference(cnf_transformation,[],[f79]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1471,plain,
% 11.99/2.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.99/2.00      | v1_funct_1(X0) != iProver_top
% 11.99/2.00      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_2325,plain,
% 11.99/2.00      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
% 11.99/2.00      | v1_funct_1(sK3) != iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_1468,c_1471]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_2459,plain,
% 11.99/2.00      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
% 11.99/2.00      inference(global_propositional_subsumption,[status(thm)],[c_2325,c_35]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_5405,plain,
% 11.99/2.00      ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 11.99/2.00      inference(demodulation,[status(thm)],[c_5398,c_2459]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f88]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1487,plain,
% 11.99/2.00      ( r1_tarski(X0,X0) = iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_31,negated_conjecture,
% 11.99/2.00      ( r1_tarski(sK2,sK0) ),
% 11.99/2.00      inference(cnf_transformation,[],[f85]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1469,plain,
% 11.99/2.00      ( r1_tarski(sK2,sK0) = iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_25,plain,
% 11.99/2.00      ( ~ v1_funct_2(X0,X1,X2)
% 11.99/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.99/2.00      | k1_relset_1(X1,X2,X0) = X1
% 11.99/2.00      | k1_xboole_0 = X2 ),
% 11.99/2.00      inference(cnf_transformation,[],[f73]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_33,negated_conjecture,
% 11.99/2.00      ( v1_funct_2(sK3,sK0,sK1) ),
% 11.99/2.00      inference(cnf_transformation,[],[f83]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_511,plain,
% 11.99/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.99/2.00      | k1_relset_1(X1,X2,X0) = X1
% 11.99/2.00      | sK3 != X0
% 11.99/2.00      | sK1 != X2
% 11.99/2.00      | sK0 != X1
% 11.99/2.00      | k1_xboole_0 = X2 ),
% 11.99/2.00      inference(resolution_lifted,[status(thm)],[c_25,c_33]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_512,plain,
% 11.99/2.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 11.99/2.00      | k1_relset_1(sK0,sK1,sK3) = sK0
% 11.99/2.00      | k1_xboole_0 = sK1 ),
% 11.99/2.00      inference(unflattening,[status(thm)],[c_511]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_514,plain,
% 11.99/2.00      ( k1_relset_1(sK0,sK1,sK3) = sK0 | k1_xboole_0 = sK1 ),
% 11.99/2.00      inference(global_propositional_subsumption,[status(thm)],[c_512,c_32]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_17,plain,
% 11.99/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.99/2.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 11.99/2.00      inference(cnf_transformation,[],[f70]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1475,plain,
% 11.99/2.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 11.99/2.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_2582,plain,
% 11.99/2.00      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_1468,c_1475]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_2730,plain,
% 11.99/2.00      ( k1_relat_1(sK3) = sK0 | sK1 = k1_xboole_0 ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_514,c_2582]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_14,plain,
% 11.99/2.00      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 11.99/2.00      | ~ v1_relat_1(X1)
% 11.99/2.00      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 11.99/2.00      inference(cnf_transformation,[],[f67]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1478,plain,
% 11.99/2.00      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 11.99/2.00      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 11.99/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_2997,plain,
% 11.99/2.00      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 11.99/2.00      | sK1 = k1_xboole_0
% 11.99/2.00      | r1_tarski(X0,sK0) != iProver_top
% 11.99/2.00      | v1_relat_1(sK3) != iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_2730,c_1478]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_16,plain,
% 11.99/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 11.99/2.00      inference(cnf_transformation,[],[f69]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1476,plain,
% 11.99/2.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.99/2.00      | v1_relat_1(X0) = iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_2424,plain,
% 11.99/2.00      ( v1_relat_1(sK3) = iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_1468,c_1476]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_7793,plain,
% 11.99/2.00      ( r1_tarski(X0,sK0) != iProver_top
% 11.99/2.00      | sK1 = k1_xboole_0
% 11.99/2.00      | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
% 11.99/2.00      inference(global_propositional_subsumption,[status(thm)],[c_2997,c_2424]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_7794,plain,
% 11.99/2.00      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 11.99/2.00      | sK1 = k1_xboole_0
% 11.99/2.00      | r1_tarski(X0,sK0) != iProver_top ),
% 11.99/2.00      inference(renaming,[status(thm)],[c_7793]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_7802,plain,
% 11.99/2.00      ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2 | sK1 = k1_xboole_0 ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_1469,c_7794]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_19,plain,
% 11.99/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.99/2.00      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.99/2.00      | ~ r1_tarski(X3,X0) ),
% 11.99/2.00      inference(cnf_transformation,[],[f72]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1473,plain,
% 11.99/2.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.99/2.00      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 11.99/2.00      | r1_tarski(X3,X0) != iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_2907,plain,
% 11.99/2.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 11.99/2.00      | r1_tarski(X0,sK3) != iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_1468,c_1473]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_18,plain,
% 11.99/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.99/2.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 11.99/2.00      | ~ r1_tarski(k1_relat_1(X0),X3) ),
% 11.99/2.00      inference(cnf_transformation,[],[f71]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1474,plain,
% 11.99/2.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.99/2.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) = iProver_top
% 11.99/2.00      | r1_tarski(k1_relat_1(X0),X3) != iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_3493,plain,
% 11.99/2.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
% 11.99/2.00      | r1_tarski(X0,sK3) != iProver_top
% 11.99/2.00      | r1_tarski(k1_relat_1(X0),X1) != iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_2907,c_1474]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_6526,plain,
% 11.99/2.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
% 11.99/2.00      | r1_tarski(X0,X2) != iProver_top
% 11.99/2.00      | r1_tarski(X2,sK3) != iProver_top
% 11.99/2.00      | r1_tarski(k1_relat_1(X2),X1) != iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_3493,c_1473]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_43773,plain,
% 11.99/2.00      ( sK1 = k1_xboole_0
% 11.99/2.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
% 11.99/2.00      | r1_tarski(X0,k7_relat_1(sK3,sK2)) != iProver_top
% 11.99/2.00      | r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top
% 11.99/2.00      | r1_tarski(sK2,X1) != iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_7802,c_6526]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_13,plain,
% 11.99/2.00      ( r1_tarski(k7_relat_1(X0,X1),X0) | ~ v1_relat_1(X0) ),
% 11.99/2.00      inference(cnf_transformation,[],[f66]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_11780,plain,
% 11.99/2.00      ( r1_tarski(k7_relat_1(sK3,X0),sK3) | ~ v1_relat_1(sK3) ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_13]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_43625,plain,
% 11.99/2.00      ( r1_tarski(k7_relat_1(sK3,sK2),sK3) | ~ v1_relat_1(sK3) ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_11780]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_43628,plain,
% 11.99/2.00      ( r1_tarski(k7_relat_1(sK3,sK2),sK3) = iProver_top
% 11.99/2.00      | v1_relat_1(sK3) != iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_43625]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_43969,plain,
% 11.99/2.00      ( r1_tarski(X0,k7_relat_1(sK3,sK2)) != iProver_top
% 11.99/2.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
% 11.99/2.00      | sK1 = k1_xboole_0
% 11.99/2.00      | r1_tarski(sK2,X1) != iProver_top ),
% 11.99/2.00      inference(global_propositional_subsumption,
% 11.99/2.00                [status(thm)],
% 11.99/2.00                [c_43773,c_2424,c_43628]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_43970,plain,
% 11.99/2.00      ( sK1 = k1_xboole_0
% 11.99/2.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
% 11.99/2.00      | r1_tarski(X0,k7_relat_1(sK3,sK2)) != iProver_top
% 11.99/2.00      | r1_tarski(sK2,X1) != iProver_top ),
% 11.99/2.00      inference(renaming,[status(thm)],[c_43969]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1479,plain,
% 11.99/2.00      ( r1_tarski(k7_relat_1(X0,X1),X0) = iProver_top
% 11.99/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_6524,plain,
% 11.99/2.00      ( k1_relset_1(X0,sK1,X1) = k1_relat_1(X1)
% 11.99/2.00      | r1_tarski(X1,sK3) != iProver_top
% 11.99/2.00      | r1_tarski(k1_relat_1(X1),X0) != iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_3493,c_1475]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_16543,plain,
% 11.99/2.00      ( k1_relset_1(k1_relat_1(X0),sK1,X0) = k1_relat_1(X0)
% 11.99/2.00      | r1_tarski(X0,sK3) != iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_1487,c_6524]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_17077,plain,
% 11.99/2.00      ( k1_relset_1(k1_relat_1(k7_relat_1(sK3,X0)),sK1,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0))
% 11.99/2.00      | v1_relat_1(sK3) != iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_1479,c_16543]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_26016,plain,
% 11.99/2.00      ( k1_relset_1(k1_relat_1(k7_relat_1(sK3,X0)),sK1,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
% 11.99/2.00      inference(global_propositional_subsumption,
% 11.99/2.00                [status(thm)],
% 11.99/2.00                [c_17077,c_2424]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_26021,plain,
% 11.99/2.00      ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
% 11.99/2.00      | sK1 = k1_xboole_0 ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_7802,c_26016]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_23,plain,
% 11.99/2.00      ( v1_funct_2(X0,X1,X2)
% 11.99/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.99/2.00      | k1_relset_1(X1,X2,X0) != X1
% 11.99/2.00      | k1_xboole_0 = X2 ),
% 11.99/2.00      inference(cnf_transformation,[],[f75]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_29,negated_conjecture,
% 11.99/2.00      ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
% 11.99/2.00      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 11.99/2.00      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
% 11.99/2.00      inference(cnf_transformation,[],[f87]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_495,plain,
% 11.99/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.99/2.00      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 11.99/2.00      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 11.99/2.00      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 11.99/2.00      | k1_relset_1(X1,X2,X0) != X1
% 11.99/2.00      | sK2 != X1
% 11.99/2.00      | sK1 != X2
% 11.99/2.00      | k1_xboole_0 = X2 ),
% 11.99/2.00      inference(resolution_lifted,[status(thm)],[c_23,c_29]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_496,plain,
% 11.99/2.00      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 11.99/2.00      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 11.99/2.00      | k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 11.99/2.00      | k1_xboole_0 = sK1 ),
% 11.99/2.00      inference(unflattening,[status(thm)],[c_495]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1462,plain,
% 11.99/2.00      ( k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 11.99/2.00      | k1_xboole_0 = sK1
% 11.99/2.00      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 11.99/2.00      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_496]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_5404,plain,
% 11.99/2.00      ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) != sK2
% 11.99/2.00      | sK1 = k1_xboole_0
% 11.99/2.00      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 11.99/2.00      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 11.99/2.00      inference(demodulation,[status(thm)],[c_5398,c_1462]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_26122,plain,
% 11.99/2.00      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 11.99/2.00      | sK1 = k1_xboole_0
% 11.99/2.00      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 11.99/2.00      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_26021,c_5404]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_10,plain,
% 11.99/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 11.99/2.00      inference(cnf_transformation,[],[f62]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_90,plain,
% 11.99/2.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 11.99/2.00      | r1_tarski(X0,X1) = iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_92,plain,
% 11.99/2.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 11.99/2.00      | r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_90]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_8,plain,
% 11.99/2.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 11.99/2.00      inference(cnf_transformation,[],[f61]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_96,plain,
% 11.99/2.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_98,plain,
% 11.99/2.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_96]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_7,plain,
% 11.99/2.00      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 11.99/2.00      | k1_xboole_0 = X1
% 11.99/2.00      | k1_xboole_0 = X0 ),
% 11.99/2.00      inference(cnf_transformation,[],[f58]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_99,plain,
% 11.99/2.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 11.99/2.00      | k1_xboole_0 = k1_xboole_0 ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_7]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_6,plain,
% 11.99/2.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 11.99/2.00      inference(cnf_transformation,[],[f91]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_100,plain,
% 11.99/2.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_6]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_831,plain,
% 11.99/2.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.99/2.00      theory(equality) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1564,plain,
% 11.99/2.00      ( ~ r1_tarski(X0,X1)
% 11.99/2.00      | r1_tarski(sK0,k1_xboole_0)
% 11.99/2.00      | sK0 != X0
% 11.99/2.00      | k1_xboole_0 != X1 ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_831]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1565,plain,
% 11.99/2.00      ( sK0 != X0
% 11.99/2.00      | k1_xboole_0 != X1
% 11.99/2.00      | r1_tarski(X0,X1) != iProver_top
% 11.99/2.00      | r1_tarski(sK0,k1_xboole_0) = iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_1564]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1567,plain,
% 11.99/2.00      ( sK0 != k1_xboole_0
% 11.99/2.00      | k1_xboole_0 != k1_xboole_0
% 11.99/2.00      | r1_tarski(sK0,k1_xboole_0) = iProver_top
% 11.99/2.00      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_1565]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_9,plain,
% 11.99/2.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.99/2.00      inference(cnf_transformation,[],[f63]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1617,plain,
% 11.99/2.00      ( m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0))
% 11.99/2.00      | ~ r1_tarski(sK0,k1_xboole_0) ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_9]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1618,plain,
% 11.99/2.00      ( m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 11.99/2.00      | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_1617]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_21,plain,
% 11.99/2.00      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 11.99/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 11.99/2.00      | k1_xboole_0 = X1
% 11.99/2.00      | k1_xboole_0 = X0 ),
% 11.99/2.00      inference(cnf_transformation,[],[f94]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_443,plain,
% 11.99/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 11.99/2.00      | sK3 != X0
% 11.99/2.00      | sK1 != k1_xboole_0
% 11.99/2.00      | sK0 != X1
% 11.99/2.00      | k1_xboole_0 = X1
% 11.99/2.00      | k1_xboole_0 = X0 ),
% 11.99/2.00      inference(resolution_lifted,[status(thm)],[c_21,c_33]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_444,plain,
% 11.99/2.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
% 11.99/2.00      | sK1 != k1_xboole_0
% 11.99/2.00      | k1_xboole_0 = sK3
% 11.99/2.00      | k1_xboole_0 = sK0 ),
% 11.99/2.00      inference(unflattening,[status(thm)],[c_443]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1465,plain,
% 11.99/2.00      ( sK1 != k1_xboole_0
% 11.99/2.00      | k1_xboole_0 = sK3
% 11.99/2.00      | k1_xboole_0 = sK0
% 11.99/2.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_444]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_5,plain,
% 11.99/2.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 11.99/2.00      inference(cnf_transformation,[],[f90]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1490,plain,
% 11.99/2.00      ( sK3 = k1_xboole_0
% 11.99/2.00      | sK1 != k1_xboole_0
% 11.99/2.00      | sK0 = k1_xboole_0
% 11.99/2.00      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 11.99/2.00      inference(demodulation,[status(thm)],[c_1465,c_5]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_30,negated_conjecture,
% 11.99/2.00      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 11.99/2.00      inference(cnf_transformation,[],[f86]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_830,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1536,plain,
% 11.99/2.00      ( sK0 != X0 | sK0 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_830]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1583,plain,
% 11.99/2.00      ( sK0 != sK0 | sK0 = k1_xboole_0 | k1_xboole_0 != sK0 ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_1536]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_829,plain,( X0 = X0 ),theory(equality) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1685,plain,
% 11.99/2.00      ( sK0 = sK0 ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_829]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1944,plain,
% 11.99/2.00      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_830]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1945,plain,
% 11.99/2.00      ( sK1 != k1_xboole_0 | k1_xboole_0 = sK1 | k1_xboole_0 != k1_xboole_0 ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_1944]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_2057,plain,
% 11.99/2.00      ( sK0 = k1_xboole_0 | sK1 != k1_xboole_0 ),
% 11.99/2.00      inference(global_propositional_subsumption,
% 11.99/2.00                [status(thm)],
% 11.99/2.00                [c_1490,c_30,c_99,c_100,c_1583,c_1685,c_1945]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_2058,plain,
% 11.99/2.00      ( sK1 != k1_xboole_0 | sK0 = k1_xboole_0 ),
% 11.99/2.00      inference(renaming,[status(thm)],[c_2057]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_3495,plain,
% 11.99/2.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 11.99/2.00      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 11.99/2.00      | r1_tarski(k1_relat_1(X0),X1) != iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_6,c_1474]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1482,plain,
% 11.99/2.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 11.99/2.00      | r1_tarski(X0,X1) = iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_5089,plain,
% 11.99/2.00      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 11.99/2.00      | r1_tarski(X0,k2_zfmisc_1(X1,X2)) = iProver_top
% 11.99/2.00      | r1_tarski(k1_relat_1(X0),X1) != iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_3495,c_1482]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_3,plain,
% 11.99/2.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 11.99/2.00      inference(cnf_transformation,[],[f56]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1486,plain,
% 11.99/2.00      ( r1_tarski(X0,X1) != iProver_top
% 11.99/2.00      | r1_tarski(X1,X2) != iProver_top
% 11.99/2.00      | r1_tarski(X0,X2) = iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_2984,plain,
% 11.99/2.00      ( r1_tarski(sK2,X0) = iProver_top | r1_tarski(sK0,X0) != iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_1469,c_1486]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_32161,plain,
% 11.99/2.00      ( m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 11.99/2.00      | r1_tarski(k1_relat_1(sK0),X0) != iProver_top
% 11.99/2.00      | r1_tarski(sK2,k2_zfmisc_1(X0,X1)) = iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_5089,c_2984]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1558,plain,
% 11.99/2.00      ( ~ m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0))
% 11.99/2.00      | r1_tarski(sK0,k1_xboole_0) ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_10]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1559,plain,
% 11.99/2.00      ( m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 11.99/2.00      | r1_tarski(sK0,k1_xboole_0) = iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_1558]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1484,plain,
% 11.99/2.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_2904,plain,
% 11.99/2.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 11.99/2.00      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_1484,c_1473]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_11398,plain,
% 11.99/2.00      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) = iProver_top
% 11.99/2.00      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_2904,c_1482]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_12130,plain,
% 11.99/2.00      ( r1_tarski(sK2,k2_zfmisc_1(X0,X1)) = iProver_top
% 11.99/2.00      | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_11398,c_2984]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_32830,plain,
% 11.99/2.00      ( m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 11.99/2.00      | r1_tarski(sK2,k2_zfmisc_1(X0,X1)) = iProver_top ),
% 11.99/2.00      inference(global_propositional_subsumption,
% 11.99/2.00                [status(thm)],
% 11.99/2.00                [c_32161,c_1559,c_12130]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1483,plain,
% 11.99/2.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 11.99/2.00      | r1_tarski(X0,X1) != iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_2905,plain,
% 11.99/2.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 11.99/2.00      | r1_tarski(X0,X3) != iProver_top
% 11.99/2.00      | r1_tarski(X3,k2_zfmisc_1(X1,X2)) != iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_1483,c_1473]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_32844,plain,
% 11.99/2.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 11.99/2.00      | m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 11.99/2.00      | r1_tarski(X0,sK2) != iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_32830,c_2905]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_34730,plain,
% 11.99/2.00      ( m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 11.99/2.00      | r1_tarski(X0,k2_zfmisc_1(X1,X2)) = iProver_top
% 11.99/2.00      | r1_tarski(X0,sK2) != iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_32844,c_1482]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_2381,plain,
% 11.99/2.00      ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_1468,c_1482]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_2985,plain,
% 11.99/2.00      ( r1_tarski(k2_zfmisc_1(sK0,sK1),X0) != iProver_top
% 11.99/2.00      | r1_tarski(sK3,X0) = iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_2381,c_1486]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_51209,plain,
% 11.99/2.00      ( m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 11.99/2.00      | r1_tarski(k2_zfmisc_1(sK0,sK1),sK2) != iProver_top
% 11.99/2.00      | r1_tarski(sK3,k2_zfmisc_1(X0,X1)) = iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_34730,c_2985]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_2711,plain,
% 11.99/2.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0)) | r1_tarski(sK3,X0) ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_10]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_5525,plain,
% 11.99/2.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.99/2.00      | r1_tarski(sK3,k2_zfmisc_1(X0,X1)) ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_2711]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_5526,plain,
% 11.99/2.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.99/2.00      | r1_tarski(sK3,k2_zfmisc_1(X0,X1)) = iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_5525]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_2688,plain,
% 11.99/2.00      ( ~ r1_tarski(X0,X1)
% 11.99/2.00      | r1_tarski(k1_relat_1(sK3),k1_xboole_0)
% 11.99/2.00      | k1_relat_1(sK3) != X0
% 11.99/2.00      | k1_xboole_0 != X1 ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_831]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_5753,plain,
% 11.99/2.00      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 11.99/2.00      | r1_tarski(k1_relat_1(sK3),k1_xboole_0)
% 11.99/2.00      | k1_relat_1(sK3) != k1_relat_1(X0)
% 11.99/2.00      | k1_xboole_0 != X1 ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_2688]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_5754,plain,
% 11.99/2.00      ( k1_relat_1(sK3) != k1_relat_1(X0)
% 11.99/2.00      | k1_xboole_0 != X1
% 11.99/2.00      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 11.99/2.00      | r1_tarski(k1_relat_1(sK3),k1_xboole_0) = iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_5753]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_5756,plain,
% 11.99/2.00      ( k1_relat_1(sK3) != k1_relat_1(k1_xboole_0)
% 11.99/2.00      | k1_xboole_0 != k1_xboole_0
% 11.99/2.00      | r1_tarski(k1_relat_1(sK3),k1_xboole_0) = iProver_top
% 11.99/2.00      | r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0) != iProver_top ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_5754]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_2423,plain,
% 11.99/2.00      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 11.99/2.00      | v1_relat_1(X0) = iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_1483,c_1476]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_7019,plain,
% 11.99/2.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_1487,c_2423]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_4,plain,
% 11.99/2.00      ( r1_tarski(k1_xboole_0,X0) ),
% 11.99/2.00      inference(cnf_transformation,[],[f57]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1485,plain,
% 11.99/2.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_2995,plain,
% 11.99/2.00      ( k1_relat_1(k7_relat_1(X0,k1_xboole_0)) = k1_xboole_0
% 11.99/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_1485,c_1478]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_8726,plain,
% 11.99/2.00      ( k1_relat_1(k7_relat_1(k2_zfmisc_1(X0,X1),k1_xboole_0)) = k1_xboole_0 ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_7019,c_2995]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_12,plain,
% 11.99/2.00      ( ~ v1_relat_1(X0) | k7_relat_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 11.99/2.00      inference(cnf_transformation,[],[f65]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1480,plain,
% 11.99/2.00      ( k7_relat_1(X0,k1_xboole_0) = k1_xboole_0
% 11.99/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_8286,plain,
% 11.99/2.00      ( k7_relat_1(k2_zfmisc_1(X0,X1),k1_xboole_0) = k1_xboole_0 ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_7019,c_1480]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_8727,plain,
% 11.99/2.00      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 11.99/2.00      inference(light_normalisation,[status(thm)],[c_8726,c_8286]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_837,plain,
% 11.99/2.00      ( X0 != X1 | k1_relat_1(X0) = k1_relat_1(X1) ),
% 11.99/2.00      theory(equality) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_12247,plain,
% 11.99/2.00      ( k1_relat_1(sK3) = k1_relat_1(X0) | sK3 != X0 ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_837]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_12248,plain,
% 11.99/2.00      ( k1_relat_1(sK3) = k1_relat_1(k1_xboole_0) | sK3 != k1_xboole_0 ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_12247]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_3492,plain,
% 11.99/2.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) = iProver_top
% 11.99/2.00      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_1468,c_1474]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_3944,plain,
% 11.99/2.00      ( r1_tarski(k1_relat_1(sK3),X0) != iProver_top
% 11.99/2.00      | r1_tarski(sK3,k2_zfmisc_1(X0,sK1)) = iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_3492,c_1482]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_0,plain,
% 11.99/2.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 11.99/2.00      inference(cnf_transformation,[],[f55]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1488,plain,
% 11.99/2.00      ( X0 = X1
% 11.99/2.00      | r1_tarski(X0,X1) != iProver_top
% 11.99/2.00      | r1_tarski(X1,X0) != iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_4274,plain,
% 11.99/2.00      ( k2_zfmisc_1(X0,sK1) = sK3
% 11.99/2.00      | r1_tarski(k2_zfmisc_1(X0,sK1),sK3) != iProver_top
% 11.99/2.00      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_3944,c_1488]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_15601,plain,
% 11.99/2.00      ( k2_zfmisc_1(k1_xboole_0,sK1) = sK3
% 11.99/2.00      | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top
% 11.99/2.00      | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_6,c_4274]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_15602,plain,
% 11.99/2.00      ( sK3 = k1_xboole_0
% 11.99/2.00      | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top
% 11.99/2.00      | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
% 11.99/2.00      inference(demodulation,[status(thm)],[c_15601,c_6]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_5686,plain,
% 11.99/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3)) | r1_tarski(X0,sK3) ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_10]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_5687,plain,
% 11.99/2.00      ( m1_subset_1(X0,k1_zfmisc_1(sK3)) != iProver_top
% 11.99/2.00      | r1_tarski(X0,sK3) = iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_5686]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_5689,plain,
% 11.99/2.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) != iProver_top
% 11.99/2.00      | r1_tarski(k1_xboole_0,sK3) = iProver_top ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_5687]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_15431,plain,
% 11.99/2.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_8]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_15432,plain,
% 11.99/2.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3)) = iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_15431]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_16107,plain,
% 11.99/2.00      ( r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top
% 11.99/2.00      | sK3 = k1_xboole_0 ),
% 11.99/2.00      inference(global_propositional_subsumption,
% 11.99/2.00                [status(thm)],
% 11.99/2.00                [c_15602,c_5689,c_15432]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_16108,plain,
% 11.99/2.00      ( sK3 = k1_xboole_0
% 11.99/2.00      | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top ),
% 11.99/2.00      inference(renaming,[status(thm)],[c_16107]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_16111,plain,
% 11.99/2.00      ( sK3 = k1_xboole_0
% 11.99/2.00      | sK1 = k1_xboole_0
% 11.99/2.00      | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_2730,c_16108]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_38,plain,
% 11.99/2.00      ( r1_tarski(sK2,sK0) = iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_91,plain,
% 11.99/2.00      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
% 11.99/2.00      | r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_10]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_97,plain,
% 11.99/2.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_8]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1533,plain,
% 11.99/2.00      ( ~ r1_tarski(sK0,k1_xboole_0)
% 11.99/2.00      | ~ r1_tarski(k1_xboole_0,sK0)
% 11.99/2.00      | sK0 = k1_xboole_0 ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_0]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1534,plain,
% 11.99/2.00      ( sK0 = k1_xboole_0
% 11.99/2.00      | r1_tarski(sK0,k1_xboole_0) != iProver_top
% 11.99/2.00      | r1_tarski(k1_xboole_0,sK0) != iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_1533]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1719,plain,
% 11.99/2.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,sK0) | r1_tarski(X0,sK0) ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_3]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_2118,plain,
% 11.99/2.00      ( ~ r1_tarski(X0,sK2) | r1_tarski(X0,sK0) | ~ r1_tarski(sK2,sK0) ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_1719]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_2119,plain,
% 11.99/2.00      ( r1_tarski(X0,sK2) != iProver_top
% 11.99/2.00      | r1_tarski(X0,sK0) = iProver_top
% 11.99/2.00      | r1_tarski(sK2,sK0) != iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_2118]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_2121,plain,
% 11.99/2.00      ( r1_tarski(sK2,sK0) != iProver_top
% 11.99/2.00      | r1_tarski(k1_xboole_0,sK2) != iProver_top
% 11.99/2.00      | r1_tarski(k1_xboole_0,sK0) = iProver_top ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_2119]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_2143,plain,
% 11.99/2.00      ( ~ r1_tarski(X0,X1)
% 11.99/2.00      | r1_tarski(k2_zfmisc_1(X2,X3),k1_xboole_0)
% 11.99/2.00      | k2_zfmisc_1(X2,X3) != X0
% 11.99/2.00      | k1_xboole_0 != X1 ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_831]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_2145,plain,
% 11.99/2.00      ( r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0)
% 11.99/2.00      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 11.99/2.00      | k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 11.99/2.00      | k1_xboole_0 != k1_xboole_0 ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_2143]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_2417,plain,
% 11.99/2.00      ( r1_tarski(k1_xboole_0,sK2) ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_4]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_2418,plain,
% 11.99/2.00      ( r1_tarski(k1_xboole_0,sK2) = iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_2417]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_2712,plain,
% 11.99/2.00      ( m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 11.99/2.00      | r1_tarski(sK3,X0) = iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_2711]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_2714,plain,
% 11.99/2.00      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 11.99/2.00      | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_2712]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_2733,plain,
% 11.99/2.00      ( ~ r1_tarski(X0,sK3) | ~ r1_tarski(sK3,X0) | sK3 = X0 ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_0]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_2735,plain,
% 11.99/2.00      ( ~ r1_tarski(sK3,k1_xboole_0)
% 11.99/2.00      | ~ r1_tarski(k1_xboole_0,sK3)
% 11.99/2.00      | sK3 = k1_xboole_0 ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_2733]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_2734,plain,
% 11.99/2.00      ( sK3 = X0
% 11.99/2.00      | r1_tarski(X0,sK3) != iProver_top
% 11.99/2.00      | r1_tarski(sK3,X0) != iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_2733]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_2736,plain,
% 11.99/2.00      ( sK3 = k1_xboole_0
% 11.99/2.00      | r1_tarski(sK3,k1_xboole_0) != iProver_top
% 11.99/2.00      | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_2734]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_2990,plain,
% 11.99/2.00      ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),X0) | r1_tarski(sK3,X0) ),
% 11.99/2.00      inference(predicate_to_equality_rev,[status(thm)],[c_2985]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_2992,plain,
% 11.99/2.00      ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k1_xboole_0)
% 11.99/2.00      | r1_tarski(sK3,k1_xboole_0) ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_2990]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_3943,plain,
% 11.99/2.00      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 11.99/2.00      | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_6,c_3492]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_4095,plain,
% 11.99/2.00      ( sK1 = k1_xboole_0
% 11.99/2.00      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 11.99/2.00      | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_2730,c_3943]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_5688,plain,
% 11.99/2.00      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK3))
% 11.99/2.00      | r1_tarski(k1_xboole_0,sK3) ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_5686]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_5269,plain,
% 11.99/2.00      ( ~ r1_tarski(X0,X1)
% 11.99/2.00      | r1_tarski(k2_zfmisc_1(sK0,sK1),k1_xboole_0)
% 11.99/2.00      | k2_zfmisc_1(sK0,sK1) != X0
% 11.99/2.00      | k1_xboole_0 != X1 ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_2143]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_11980,plain,
% 11.99/2.00      ( ~ r1_tarski(k2_zfmisc_1(X0,X1),X2)
% 11.99/2.00      | r1_tarski(k2_zfmisc_1(sK0,sK1),k1_xboole_0)
% 11.99/2.00      | k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X0,X1)
% 11.99/2.00      | k1_xboole_0 != X2 ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_5269]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_11982,plain,
% 11.99/2.00      ( r1_tarski(k2_zfmisc_1(sK0,sK1),k1_xboole_0)
% 11.99/2.00      | ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0)
% 11.99/2.00      | k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
% 11.99/2.00      | k1_xboole_0 != k1_xboole_0 ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_11980]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_832,plain,
% 11.99/2.00      ( X0 != X1 | X2 != X3 | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
% 11.99/2.00      theory(equality) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_12044,plain,
% 11.99/2.00      ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(X0,X1) | sK1 != X1 | sK0 != X0 ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_832]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_12045,plain,
% 11.99/2.00      ( k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
% 11.99/2.00      | sK1 != k1_xboole_0
% 11.99/2.00      | sK0 != k1_xboole_0 ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_12044]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_16360,plain,
% 11.99/2.00      ( sK3 = k1_xboole_0 | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
% 11.99/2.00      inference(global_propositional_subsumption,
% 11.99/2.00                [status(thm)],
% 11.99/2.00                [c_16111,c_38,c_91,c_97,c_99,c_100,c_1534,c_2121,c_2145,
% 11.99/2.00                 c_2418,c_2714,c_2735,c_2736,c_2992,c_4095,c_5688,c_5689,
% 11.99/2.00                 c_11982,c_12045,c_15431,c_15432]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_37472,plain,
% 11.99/2.00      ( ~ r1_tarski(X0,X1)
% 11.99/2.00      | r1_tarski(k1_relat_1(X2),k1_xboole_0)
% 11.99/2.00      | k1_relat_1(X2) != X0
% 11.99/2.00      | k1_xboole_0 != X1 ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_831]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_37473,plain,
% 11.99/2.00      ( k1_relat_1(X0) != X1
% 11.99/2.00      | k1_xboole_0 != X2
% 11.99/2.00      | r1_tarski(X1,X2) != iProver_top
% 11.99/2.00      | r1_tarski(k1_relat_1(X0),k1_xboole_0) = iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_37472]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_37475,plain,
% 11.99/2.00      ( k1_relat_1(k1_xboole_0) != k1_xboole_0
% 11.99/2.00      | k1_xboole_0 != k1_xboole_0
% 11.99/2.00      | r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0) = iProver_top
% 11.99/2.00      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_37473]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_11403,plain,
% 11.99/2.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 11.99/2.00      | r1_tarski(X0,X3) != iProver_top
% 11.99/2.00      | r1_tarski(X3,k1_xboole_0) != iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_2904,c_1473]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_44470,plain,
% 11.99/2.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
% 11.99/2.00      | r1_tarski(k2_zfmisc_1(X2,sK1),k1_xboole_0) != iProver_top
% 11.99/2.00      | r1_tarski(k1_relat_1(sK3),X2) != iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_3944,c_11403]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_47016,plain,
% 11.99/2.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
% 11.99/2.00      | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top
% 11.99/2.00      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_6,c_44470]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_51733,plain,
% 11.99/2.00      ( m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 11.99/2.00      | r1_tarski(sK3,k2_zfmisc_1(X0,X1)) = iProver_top ),
% 11.99/2.00      inference(global_propositional_subsumption,
% 11.99/2.00                [status(thm)],
% 11.99/2.00                [c_51209,c_92,c_98,c_99,c_100,c_1559,c_5526,c_5756,c_8727,
% 11.99/2.00                 c_12248,c_16360,c_37475,c_47016]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_51739,plain,
% 11.99/2.00      ( m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 11.99/2.00      | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_5,c_51733]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_522,plain,
% 11.99/2.00      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 11.99/2.00      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 11.99/2.00      | k2_partfun1(sK0,sK1,sK3,sK2) != sK3
% 11.99/2.00      | sK2 != sK0
% 11.99/2.00      | sK1 != sK1 ),
% 11.99/2.00      inference(resolution_lifted,[status(thm)],[c_29,c_33]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1545,plain,
% 11.99/2.00      ( sK2 != X0 | sK2 = sK0 | sK0 != X0 ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_830]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1546,plain,
% 11.99/2.00      ( sK2 = sK0 | sK2 != k1_xboole_0 | sK0 != k1_xboole_0 ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_1545]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1553,plain,
% 11.99/2.00      ( ~ r1_tarski(X0,X1)
% 11.99/2.00      | r1_tarski(sK2,k1_xboole_0)
% 11.99/2.00      | sK2 != X0
% 11.99/2.00      | k1_xboole_0 != X1 ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_831]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1555,plain,
% 11.99/2.00      ( r1_tarski(sK2,k1_xboole_0)
% 11.99/2.00      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 11.99/2.00      | sK2 != k1_xboole_0
% 11.99/2.00      | k1_xboole_0 != k1_xboole_0 ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_1553]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1688,plain,
% 11.99/2.00      ( sK1 = sK1 ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_829]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1953,plain,
% 11.99/2.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 11.99/2.00      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 11.99/2.00      | ~ v1_funct_1(sK3) ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_27]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_2144,plain,
% 11.99/2.00      ( k2_zfmisc_1(X0,X1) != X2
% 11.99/2.00      | k1_xboole_0 != X3
% 11.99/2.00      | r1_tarski(X2,X3) != iProver_top
% 11.99/2.00      | r1_tarski(k2_zfmisc_1(X0,X1),k1_xboole_0) = iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_2143]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_2146,plain,
% 11.99/2.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 11.99/2.00      | k1_xboole_0 != k1_xboole_0
% 11.99/2.00      | r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0) = iProver_top
% 11.99/2.00      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_2144]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_2429,plain,
% 11.99/2.00      ( v1_relat_1(sK3) ),
% 11.99/2.00      inference(predicate_to_equality_rev,[status(thm)],[c_2424]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_2477,plain,
% 11.99/2.00      ( ~ r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k1_xboole_0)
% 11.99/2.00      | ~ r1_tarski(k1_xboole_0,k2_partfun1(sK0,sK1,sK3,sK2))
% 11.99/2.00      | k2_partfun1(sK0,sK1,sK3,sK2) = k1_xboole_0 ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_0]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_6154,plain,
% 11.99/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_partfun1(sK0,sK1,sK3,sK2)))
% 11.99/2.00      | r1_tarski(X0,k2_partfun1(sK0,sK1,sK3,sK2)) ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_10]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_6156,plain,
% 11.99/2.00      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_partfun1(sK0,sK1,sK3,sK2)))
% 11.99/2.00      | r1_tarski(k1_xboole_0,k2_partfun1(sK0,sK1,sK3,sK2)) ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_6154]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_2865,plain,
% 11.99/2.00      ( ~ r1_tarski(X0,X1)
% 11.99/2.00      | r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k1_xboole_0)
% 11.99/2.00      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 11.99/2.00      | k1_xboole_0 != X1 ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_831]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_6177,plain,
% 11.99/2.00      ( r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k1_xboole_0)
% 11.99/2.00      | ~ r1_tarski(k7_relat_1(sK3,sK2),X0)
% 11.99/2.00      | k2_partfun1(sK0,sK1,sK3,sK2) != k7_relat_1(sK3,sK2)
% 11.99/2.00      | k1_xboole_0 != X0 ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_2865]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_6179,plain,
% 11.99/2.00      ( r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k1_xboole_0)
% 11.99/2.00      | ~ r1_tarski(k7_relat_1(sK3,sK2),k1_xboole_0)
% 11.99/2.00      | k2_partfun1(sK0,sK1,sK3,sK2) != k7_relat_1(sK3,sK2)
% 11.99/2.00      | k1_xboole_0 != k1_xboole_0 ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_6177]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_6521,plain,
% 11.99/2.00      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 11.99/2.00      | r1_tarski(X0,sK3) != iProver_top
% 11.99/2.00      | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_6,c_3493]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_8438,plain,
% 11.99/2.00      ( sK1 = k1_xboole_0
% 11.99/2.00      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 11.99/2.00      | r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top
% 11.99/2.00      | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_7802,c_6521]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_8515,plain,
% 11.99/2.00      ( sK1 = k1_xboole_0
% 11.99/2.00      | r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top
% 11.99/2.00      | r1_tarski(k7_relat_1(sK3,sK2),k1_xboole_0) = iProver_top
% 11.99/2.00      | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_8438,c_1482]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_8522,plain,
% 11.99/2.00      ( ~ r1_tarski(k7_relat_1(sK3,sK2),sK3)
% 11.99/2.00      | r1_tarski(k7_relat_1(sK3,sK2),k1_xboole_0)
% 11.99/2.00      | ~ r1_tarski(sK2,k1_xboole_0)
% 11.99/2.00      | sK1 = k1_xboole_0 ),
% 11.99/2.00      inference(predicate_to_equality_rev,[status(thm)],[c_8515]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_8706,plain,
% 11.99/2.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_8]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_9391,plain,
% 11.99/2.00      ( k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) = k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_829]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_11981,plain,
% 11.99/2.00      ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(X0,X1)
% 11.99/2.00      | k1_xboole_0 != X2
% 11.99/2.00      | r1_tarski(k2_zfmisc_1(X0,X1),X2) != iProver_top
% 11.99/2.00      | r1_tarski(k2_zfmisc_1(sK0,sK1),k1_xboole_0) = iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_11980]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_11983,plain,
% 11.99/2.00      ( k2_zfmisc_1(sK0,sK1) != k2_zfmisc_1(k1_xboole_0,k1_xboole_0)
% 11.99/2.00      | k1_xboole_0 != k1_xboole_0
% 11.99/2.00      | r1_tarski(k2_zfmisc_1(sK0,sK1),k1_xboole_0) = iProver_top
% 11.99/2.00      | r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0) != iProver_top ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_11981]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_13613,plain,
% 11.99/2.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 11.99/2.00      | ~ v1_funct_1(sK3)
% 11.99/2.00      | k2_partfun1(sK0,sK1,sK3,sK2) = k7_relat_1(sK3,sK2) ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_28]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_834,plain,
% 11.99/2.00      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.99/2.00      theory(equality) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_2777,plain,
% 11.99/2.00      ( ~ m1_subset_1(X0,X1)
% 11.99/2.00      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 11.99/2.00      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 11.99/2.00      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) != X1 ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_834]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_5181,plain,
% 11.99/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 11.99/2.00      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 11.99/2.00      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 11.99/2.00      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_2777]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_18175,plain,
% 11.99/2.00      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 11.99/2.00      | ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 11.99/2.00      | k2_partfun1(sK0,sK1,sK3,sK2) != k7_relat_1(sK3,sK2)
% 11.99/2.00      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_5181]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_18833,plain,
% 11.99/2.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_partfun1(sK0,sK1,sK3,sK2))) ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_8]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_32842,plain,
% 11.99/2.00      ( k2_zfmisc_1(X0,X1) = sK2
% 11.99/2.00      | m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 11.99/2.00      | r1_tarski(k2_zfmisc_1(X0,X1),sK2) != iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_32830,c_1488]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_33385,plain,
% 11.99/2.00      ( k2_zfmisc_1(k1_xboole_0,X0) = sK2
% 11.99/2.00      | m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 11.99/2.00      | r1_tarski(k1_xboole_0,sK2) != iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_6,c_32842]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_33386,plain,
% 11.99/2.00      ( sK2 = k1_xboole_0
% 11.99/2.00      | m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 11.99/2.00      | r1_tarski(k1_xboole_0,sK2) != iProver_top ),
% 11.99/2.00      inference(light_normalisation,[status(thm)],[c_33385,c_6]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_33715,plain,
% 11.99/2.00      ( m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 11.99/2.00      | sK2 = k1_xboole_0 ),
% 11.99/2.00      inference(global_propositional_subsumption,
% 11.99/2.00                [status(thm)],
% 11.99/2.00                [c_33386,c_2418]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_33716,plain,
% 11.99/2.00      ( sK2 = k1_xboole_0
% 11.99/2.00      | m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 11.99/2.00      inference(renaming,[status(thm)],[c_33715]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_5023,plain,
% 11.99/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 11.99/2.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 11.99/2.00      | ~ r1_tarski(X1,X0) ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_19]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_9727,plain,
% 11.99/2.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 11.99/2.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 11.99/2.00      | ~ r1_tarski(X0,k1_xboole_0) ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_5023]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_39710,plain,
% 11.99/2.00      ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 11.99/2.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 11.99/2.00      | ~ r1_tarski(k7_relat_1(sK3,sK2),k1_xboole_0) ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_9727]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_51782,plain,
% 11.99/2.00      ( k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 11.99/2.00      | k2_partfun1(sK0,sK1,sK3,sK2) = sK3
% 11.99/2.00      | sK3 != X0 ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_830]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_51784,plain,
% 11.99/2.00      ( k2_partfun1(sK0,sK1,sK3,sK2) = sK3
% 11.99/2.00      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 11.99/2.00      | sK3 != k1_xboole_0 ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_51782]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_2983,plain,
% 11.99/2.00      ( r1_tarski(X0,X1) != iProver_top
% 11.99/2.00      | r1_tarski(k7_relat_1(X0,X2),X1) = iProver_top
% 11.99/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_1479,c_1486]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_3185,plain,
% 11.99/2.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 11.99/2.00      | r1_tarski(X0,X1) != iProver_top
% 11.99/2.00      | r1_tarski(X1,sK3) != iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_2907,c_1473]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_16946,plain,
% 11.99/2.00      ( m1_subset_1(k7_relat_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 11.99/2.00      | r1_tarski(X0,X2) != iProver_top
% 11.99/2.00      | r1_tarski(X2,sK3) != iProver_top
% 11.99/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_2983,c_3185]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_49282,plain,
% 11.99/2.00      ( m1_subset_1(k7_relat_1(sK2,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 11.99/2.00      | r1_tarski(sK0,sK3) != iProver_top
% 11.99/2.00      | v1_relat_1(sK2) != iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_1469,c_16946]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_4820,plain,
% 11.99/2.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 11.99/2.00      | r1_tarski(sK0,sK3) != iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_1469,c_3185]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_5247,plain,
% 11.99/2.00      ( r1_tarski(sK0,sK3) != iProver_top | v1_relat_1(sK2) = iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_4820,c_1476]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_49406,plain,
% 11.99/2.00      ( r1_tarski(sK0,sK3) != iProver_top
% 11.99/2.00      | m1_subset_1(k7_relat_1(sK2,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 11.99/2.00      inference(global_propositional_subsumption,
% 11.99/2.00                [status(thm)],
% 11.99/2.00                [c_49282,c_5247]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_49407,plain,
% 11.99/2.00      ( m1_subset_1(k7_relat_1(sK2,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 11.99/2.00      | r1_tarski(sK0,sK3) != iProver_top ),
% 11.99/2.00      inference(renaming,[status(thm)],[c_49406]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_49412,plain,
% 11.99/2.00      ( r1_tarski(k7_relat_1(sK2,X0),k2_zfmisc_1(sK0,sK1)) = iProver_top
% 11.99/2.00      | r1_tarski(sK0,sK3) != iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_49407,c_1482]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_49617,plain,
% 11.99/2.00      ( m1_subset_1(k7_relat_1(sK2,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 11.99/2.00      | r1_tarski(k2_zfmisc_1(sK0,sK1),k1_xboole_0) != iProver_top
% 11.99/2.00      | r1_tarski(sK0,sK3) != iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_49412,c_11403]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_37,plain,
% 11.99/2.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1529,plain,
% 11.99/2.00      ( ~ r1_tarski(sK2,k1_xboole_0)
% 11.99/2.00      | ~ r1_tarski(k1_xboole_0,sK2)
% 11.99/2.00      | sK2 = k1_xboole_0 ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_0]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1530,plain,
% 11.99/2.00      ( sK2 = k1_xboole_0
% 11.99/2.00      | r1_tarski(sK2,k1_xboole_0) != iProver_top
% 11.99/2.00      | r1_tarski(k1_xboole_0,sK2) != iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_1529]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1547,plain,
% 11.99/2.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
% 11.99/2.00      | r1_tarski(sK2,k1_xboole_0) ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_10]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1548,plain,
% 11.99/2.00      ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 11.99/2.00      | r1_tarski(sK2,k1_xboole_0) = iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_1547]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1943,plain,
% 11.99/2.00      ( k2_zfmisc_1(X0,sK1) != k1_xboole_0
% 11.99/2.00      | k1_xboole_0 = X0
% 11.99/2.00      | k1_xboole_0 = sK1 ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_7]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1965,plain,
% 11.99/2.00      ( k2_zfmisc_1(sK0,sK1) != k1_xboole_0
% 11.99/2.00      | k1_xboole_0 = sK1
% 11.99/2.00      | k1_xboole_0 = sK0 ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_1943]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_2478,plain,
% 11.99/2.00      ( k2_partfun1(sK0,sK1,sK3,sK2) = k1_xboole_0
% 11.99/2.00      | r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k1_xboole_0) != iProver_top
% 11.99/2.00      | r1_tarski(k1_xboole_0,k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_2477]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_2831,plain,
% 11.99/2.00      ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k1_xboole_0)
% 11.99/2.00      | ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(sK0,sK1))
% 11.99/2.00      | k2_zfmisc_1(sK0,sK1) = k1_xboole_0 ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_0]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_2832,plain,
% 11.99/2.00      ( k2_zfmisc_1(sK0,sK1) = k1_xboole_0
% 11.99/2.00      | r1_tarski(k2_zfmisc_1(sK0,sK1),k1_xboole_0) != iProver_top
% 11.99/2.00      | r1_tarski(k1_xboole_0,k2_zfmisc_1(sK0,sK1)) != iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_2831]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_2991,plain,
% 11.99/2.00      ( r1_tarski(k2_zfmisc_1(sK0,sK1),k1_xboole_0) != iProver_top
% 11.99/2.00      | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_2985]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_6155,plain,
% 11.99/2.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_partfun1(sK0,sK1,sK3,sK2))) != iProver_top
% 11.99/2.00      | r1_tarski(X0,k2_partfun1(sK0,sK1,sK3,sK2)) = iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_6154]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_6157,plain,
% 11.99/2.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_partfun1(sK0,sK1,sK3,sK2))) != iProver_top
% 11.99/2.00      | r1_tarski(k1_xboole_0,k2_partfun1(sK0,sK1,sK3,sK2)) = iProver_top ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_6155]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_2433,plain,
% 11.99/2.00      ( k7_relat_1(sK3,k1_xboole_0) = k1_xboole_0 ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_2424,c_1480]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_26,plain,
% 11.99/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.99/2.00      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.99/2.00      | ~ v1_funct_1(X0) ),
% 11.99/2.00      inference(cnf_transformation,[],[f80]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1472,plain,
% 11.99/2.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.99/2.00      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 11.99/2.00      | v1_funct_1(X0) != iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_5413,plain,
% 11.99/2.00      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 11.99/2.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 11.99/2.00      | v1_funct_1(sK3) != iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_5398,c_1472]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_6929,plain,
% 11.99/2.00      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 11.99/2.00      inference(global_propositional_subsumption,
% 11.99/2.00                [status(thm)],
% 11.99/2.00                [c_5413,c_35,c_37]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_6942,plain,
% 11.99/2.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 11.99/2.00      | r1_tarski(X0,k7_relat_1(sK3,X1)) != iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_6929,c_1473]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_9444,plain,
% 11.99/2.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 11.99/2.00      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_2433,c_6942]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_9877,plain,
% 11.99/2.00      ( r1_tarski(X0,k2_zfmisc_1(sK0,sK1)) = iProver_top
% 11.99/2.00      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_9444,c_1482]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_9886,plain,
% 11.99/2.00      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(sK0,sK1)) = iProver_top
% 11.99/2.00      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_9877]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_18834,plain,
% 11.99/2.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_partfun1(sK0,sK1,sK3,sK2))) = iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_18833]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_3183,plain,
% 11.99/2.00      ( r1_tarski(X0,k2_zfmisc_1(sK0,sK1)) = iProver_top
% 11.99/2.00      | r1_tarski(X0,sK3) != iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_2907,c_1482]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_3481,plain,
% 11.99/2.00      ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) = iProver_top
% 11.99/2.00      | r1_tarski(sK0,sK3) != iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_3183,c_2984]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_2909,plain,
% 11.99/2.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) = iProver_top
% 11.99/2.00      | m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 11.99/2.00      | r1_tarski(X0,X2) != iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_6,c_1473]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_2910,plain,
% 11.99/2.00      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 11.99/2.00      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 11.99/2.00      | r1_tarski(X1,X0) != iProver_top ),
% 11.99/2.00      inference(demodulation,[status(thm)],[c_2909,c_6]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_3089,plain,
% 11.99/2.00      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 11.99/2.00      | r1_tarski(X0,X1) != iProver_top
% 11.99/2.00      | r1_tarski(X1,k1_xboole_0) != iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_1483,c_2910]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_17847,plain,
% 11.99/2.00      ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 11.99/2.00      | r1_tarski(k2_zfmisc_1(sK0,sK1),k1_xboole_0) != iProver_top
% 11.99/2.00      | r1_tarski(sK0,sK3) != iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_3481,c_3089]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1609,plain,
% 11.99/2.00      ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
% 11.99/2.00      | ~ r1_tarski(sK2,k1_xboole_0) ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_9]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1610,plain,
% 11.99/2.00      ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 11.99/2.00      | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_1609]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1682,plain,
% 11.99/2.00      ( sK2 = sK2 ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_829]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_1735,plain,
% 11.99/2.00      ( ~ r1_tarski(sK2,X0)
% 11.99/2.00      | r1_tarski(sK2,k1_xboole_0)
% 11.99/2.00      | sK2 != sK2
% 11.99/2.00      | k1_xboole_0 != X0 ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_1553]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_2008,plain,
% 11.99/2.00      ( ~ r1_tarski(sK2,sK0)
% 11.99/2.00      | r1_tarski(sK2,k1_xboole_0)
% 11.99/2.00      | sK2 != sK2
% 11.99/2.00      | k1_xboole_0 != sK0 ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_1735]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_2009,plain,
% 11.99/2.00      ( sK2 != sK2
% 11.99/2.00      | k1_xboole_0 != sK0
% 11.99/2.00      | r1_tarski(sK2,sK0) != iProver_top
% 11.99/2.00      | r1_tarski(sK2,k1_xboole_0) = iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_2008]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_19659,plain,
% 11.99/2.00      ( r1_tarski(k2_zfmisc_1(sK0,sK1),k1_xboole_0) != iProver_top
% 11.99/2.00      | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 11.99/2.00      inference(global_propositional_subsumption,
% 11.99/2.00                [status(thm)],
% 11.99/2.00                [c_17847,c_38,c_30,c_92,c_98,c_1610,c_1682,c_1965,c_2009,
% 11.99/2.00                 c_2832,c_9886]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_19660,plain,
% 11.99/2.00      ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 11.99/2.00      | r1_tarski(k2_zfmisc_1(sK0,sK1),k1_xboole_0) != iProver_top ),
% 11.99/2.00      inference(renaming,[status(thm)],[c_19659]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_6118,plain,
% 11.99/2.00      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(X0))
% 11.99/2.00      | r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),X0) ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_10]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_13564,plain,
% 11.99/2.00      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.99/2.00      | r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k2_zfmisc_1(X0,X1)) ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_6118]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_24015,plain,
% 11.99/2.00      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 11.99/2.00      | r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k2_zfmisc_1(sK0,sK1)) ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_13564]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_24016,plain,
% 11.99/2.00      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 11.99/2.00      | r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_24015]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_2862,plain,
% 11.99/2.00      ( ~ r1_tarski(X0,k1_xboole_0)
% 11.99/2.00      | ~ r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),X0)
% 11.99/2.00      | r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k1_xboole_0) ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_3]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_28781,plain,
% 11.99/2.00      ( ~ r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k2_zfmisc_1(sK0,sK1))
% 11.99/2.00      | r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k1_xboole_0)
% 11.99/2.00      | ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k1_xboole_0) ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_2862]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_28786,plain,
% 11.99/2.00      ( r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k2_zfmisc_1(sK0,sK1)) != iProver_top
% 11.99/2.00      | r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k1_xboole_0) = iProver_top
% 11.99/2.00      | r1_tarski(k2_zfmisc_1(sK0,sK1),k1_xboole_0) != iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_28781]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_2767,plain,
% 11.99/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 11.99/2.00      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 11.99/2.00      | ~ r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),X0) ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_19]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_28776,plain,
% 11.99/2.00      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 11.99/2.00      | ~ m1_subset_1(k2_zfmisc_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 11.99/2.00      | ~ r1_tarski(k2_partfun1(sK0,sK1,sK3,sK2),k2_zfmisc_1(sK0,sK1)) ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_2767]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_5036,plain,
% 11.99/2.00      ( ~ m1_subset_1(X0,X1)
% 11.99/2.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 11.99/2.00      | X2 != X0
% 11.99/2.00      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) != X1 ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_834]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_10011,plain,
% 11.99/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 11.99/2.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 11.99/2.00      | X1 != X0
% 11.99/2.00      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_5036]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_32996,plain,
% 11.99/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 11.99/2.00      | m1_subset_1(k2_zfmisc_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 11.99/2.00      | k2_zfmisc_1(sK0,sK1) != X0
% 11.99/2.00      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_10011]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_33001,plain,
% 11.99/2.00      ( m1_subset_1(k2_zfmisc_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 11.99/2.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 11.99/2.00      | k2_zfmisc_1(sK0,sK1) != k1_xboole_0
% 11.99/2.00      | k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)) ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_32996]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_44595,plain,
% 11.99/2.00      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 11.99/2.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 11.99/2.00      | ~ v1_funct_1(sK3) ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_26]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_44596,plain,
% 11.99/2.00      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 11.99/2.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 11.99/2.00      | v1_funct_1(sK3) != iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_44595]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_51887,plain,
% 11.99/2.00      ( r1_tarski(k2_zfmisc_1(sK0,sK1),k1_xboole_0) != iProver_top ),
% 11.99/2.00      inference(global_propositional_subsumption,
% 11.99/2.00                [status(thm)],
% 11.99/2.00                [c_49617,c_34,c_35,c_32,c_37,c_30,c_92,c_98,c_522,c_1530,
% 11.99/2.00                 c_1546,c_1548,c_1583,c_1685,c_1688,c_1953,c_1965,c_2418,
% 11.99/2.00                 c_2478,c_2736,c_2832,c_2991,c_5689,c_6157,c_8706,c_9391,
% 11.99/2.00                 c_9886,c_15432,c_18834,c_19660,c_24015,c_24016,c_28786,
% 11.99/2.00                 c_28776,c_33001,c_44595,c_44596,c_51784]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_52013,plain,
% 11.99/2.00      ( m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 11.99/2.00      inference(global_propositional_subsumption,
% 11.99/2.00                [status(thm)],
% 11.99/2.00                [c_51739,c_34,c_35,c_32,c_37,c_38,c_30,c_91,c_92,c_97,c_98,
% 11.99/2.00                 c_99,c_100,c_522,c_1530,c_1534,c_1546,c_1548,c_1555,c_1559,
% 11.99/2.00                 c_1583,c_1685,c_1688,c_1953,c_1965,c_2121,c_2146,c_2418,
% 11.99/2.00                 c_2429,c_2477,c_2478,c_2736,c_2832,c_2991,c_5689,c_6156,
% 11.99/2.00                 c_6157,c_6179,c_8522,c_8706,c_9391,c_9886,c_11983,c_12045,
% 11.99/2.00                 c_13613,c_15432,c_16360,c_18175,c_18833,c_18834,c_19660,
% 11.99/2.00                 c_24015,c_24016,c_28786,c_28776,c_33001,c_33716,c_39710,
% 11.99/2.00                 c_43625,c_44595,c_44596,c_51784]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_55668,plain,
% 11.99/2.00      ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 11.99/2.00      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 11.99/2.00      inference(global_propositional_subsumption,
% 11.99/2.00                [status(thm)],
% 11.99/2.00                [c_26122,c_34,c_35,c_32,c_37,c_38,c_30,c_91,c_92,c_97,c_98,
% 11.99/2.00                 c_99,c_100,c_522,c_1530,c_1534,c_1546,c_1548,c_1555,c_1559,
% 11.99/2.00                 c_1567,c_1583,c_1618,c_1685,c_1688,c_1953,c_1965,c_2058,
% 11.99/2.00                 c_2121,c_2146,c_2418,c_2429,c_2477,c_2478,c_2736,c_2832,
% 11.99/2.00                 c_2991,c_5689,c_6156,c_6157,c_6179,c_7802,c_8522,c_8706,
% 11.99/2.00                 c_9391,c_9886,c_11983,c_12045,c_13613,c_15432,c_16360,
% 11.99/2.00                 c_18175,c_18833,c_18834,c_19660,c_24015,c_24016,c_28786,
% 11.99/2.00                 c_28776,c_33001,c_33716,c_39710,c_43625,c_44595,c_44596,
% 11.99/2.00                 c_51784]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_55678,plain,
% 11.99/2.00      ( sK1 = k1_xboole_0
% 11.99/2.00      | r1_tarski(k7_relat_1(sK3,sK2),k7_relat_1(sK3,sK2)) != iProver_top
% 11.99/2.00      | r1_tarski(sK2,sK2) != iProver_top
% 11.99/2.00      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_43970,c_55668]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_2501,plain,
% 11.99/2.00      ( r1_tarski(sK2,sK2) ),
% 11.99/2.00      inference(instantiation,[status(thm)],[c_1]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_2502,plain,
% 11.99/2.00      ( r1_tarski(sK2,sK2) = iProver_top ),
% 11.99/2.00      inference(predicate_to_equality,[status(thm)],[c_2501]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_56343,plain,
% 11.99/2.00      ( r1_tarski(k7_relat_1(sK3,sK2),k7_relat_1(sK3,sK2)) != iProver_top
% 11.99/2.00      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 11.99/2.00      inference(global_propositional_subsumption,
% 11.99/2.00                [status(thm)],
% 11.99/2.00                [c_55678,c_34,c_35,c_32,c_37,c_38,c_30,c_91,c_92,c_97,c_98,
% 11.99/2.00                 c_99,c_100,c_522,c_1530,c_1534,c_1546,c_1548,c_1555,c_1559,
% 11.99/2.00                 c_1567,c_1583,c_1618,c_1685,c_1688,c_1953,c_1965,c_2058,
% 11.99/2.00                 c_2121,c_2146,c_2418,c_2429,c_2477,c_2478,c_2502,c_2736,
% 11.99/2.00                 c_2832,c_2991,c_5689,c_6156,c_6157,c_6179,c_8522,c_8706,
% 11.99/2.00                 c_9391,c_9886,c_11983,c_12045,c_13613,c_15432,c_16360,
% 11.99/2.00                 c_18175,c_18833,c_18834,c_19660,c_24015,c_24016,c_28786,
% 11.99/2.00                 c_28776,c_33001,c_33716,c_39710,c_43625,c_44595,c_44596,
% 11.99/2.00                 c_51784]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_56347,plain,
% 11.99/2.00      ( v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_1487,c_56343]) ).
% 11.99/2.00  
% 11.99/2.00  cnf(c_56615,plain,
% 11.99/2.00      ( $false ),
% 11.99/2.00      inference(superposition,[status(thm)],[c_5405,c_56347]) ).
% 11.99/2.00  
% 11.99/2.00  
% 11.99/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 11.99/2.00  
% 11.99/2.00  ------                               Statistics
% 11.99/2.00  
% 11.99/2.00  ------ General
% 11.99/2.00  
% 11.99/2.00  abstr_ref_over_cycles:                  0
% 11.99/2.00  abstr_ref_under_cycles:                 0
% 11.99/2.00  gc_basic_clause_elim:                   0
% 11.99/2.00  forced_gc_time:                         0
% 11.99/2.00  parsing_time:                           0.01
% 11.99/2.00  unif_index_cands_time:                  0.
% 11.99/2.00  unif_index_add_time:                    0.
% 11.99/2.00  orderings_time:                         0.
% 11.99/2.00  out_proof_time:                         0.035
% 11.99/2.00  total_time:                             1.432
% 11.99/2.00  num_of_symbols:                         47
% 11.99/2.00  num_of_terms:                           24403
% 11.99/2.00  
% 11.99/2.00  ------ Preprocessing
% 11.99/2.00  
% 11.99/2.00  num_of_splits:                          0
% 11.99/2.00  num_of_split_atoms:                     0
% 11.99/2.00  num_of_reused_defs:                     0
% 11.99/2.00  num_eq_ax_congr_red:                    5
% 11.99/2.00  num_of_sem_filtered_clauses:            1
% 11.99/2.00  num_of_subtypes:                        0
% 11.99/2.00  monotx_restored_types:                  0
% 11.99/2.00  sat_num_of_epr_types:                   0
% 11.99/2.00  sat_num_of_non_cyclic_types:            0
% 11.99/2.00  sat_guarded_non_collapsed_types:        0
% 11.99/2.00  num_pure_diseq_elim:                    0
% 11.99/2.00  simp_replaced_by:                       0
% 11.99/2.00  res_preprocessed:                       158
% 11.99/2.00  prep_upred:                             0
% 11.99/2.00  prep_unflattend:                        33
% 11.99/2.00  smt_new_axioms:                         0
% 11.99/2.00  pred_elim_cands:                        4
% 11.99/2.00  pred_elim:                              1
% 11.99/2.00  pred_elim_cl:                           1
% 11.99/2.00  pred_elim_cycles:                       3
% 11.99/2.00  merged_defs:                            8
% 11.99/2.00  merged_defs_ncl:                        0
% 11.99/2.00  bin_hyper_res:                          8
% 11.99/2.00  prep_cycles:                            4
% 11.99/2.00  pred_elim_time:                         0.005
% 11.99/2.00  splitting_time:                         0.
% 11.99/2.00  sem_filter_time:                        0.
% 11.99/2.00  monotx_time:                            0.001
% 11.99/2.00  subtype_inf_time:                       0.
% 11.99/2.00  
% 11.99/2.00  ------ Problem properties
% 11.99/2.00  
% 11.99/2.00  clauses:                                33
% 11.99/2.00  conjectures:                            4
% 11.99/2.00  epr:                                    7
% 11.99/2.00  horn:                                   30
% 11.99/2.00  ground:                                 11
% 11.99/2.00  unary:                                  8
% 11.99/2.00  binary:                                 10
% 11.99/2.00  lits:                                   80
% 11.99/2.00  lits_eq:                                29
% 11.99/2.00  fd_pure:                                0
% 11.99/2.00  fd_pseudo:                              0
% 11.99/2.00  fd_cond:                                1
% 11.99/2.00  fd_pseudo_cond:                         1
% 11.99/2.00  ac_symbols:                             0
% 11.99/2.00  
% 11.99/2.00  ------ Propositional Solver
% 11.99/2.00  
% 11.99/2.00  prop_solver_calls:                      46
% 11.99/2.00  prop_fast_solver_calls:                 3048
% 11.99/2.00  smt_solver_calls:                       0
% 11.99/2.00  smt_fast_solver_calls:                  0
% 11.99/2.00  prop_num_of_clauses:                    22689
% 11.99/2.00  prop_preprocess_simplified:             37030
% 11.99/2.00  prop_fo_subsumed:                       177
% 11.99/2.00  prop_solver_time:                       0.
% 11.99/2.00  smt_solver_time:                        0.
% 11.99/2.00  smt_fast_solver_time:                   0.
% 11.99/2.00  prop_fast_solver_time:                  0.
% 11.99/2.00  prop_unsat_core_time:                   0.
% 11.99/2.00  
% 11.99/2.00  ------ QBF
% 11.99/2.00  
% 11.99/2.00  qbf_q_res:                              0
% 11.99/2.00  qbf_num_tautologies:                    0
% 11.99/2.00  qbf_prep_cycles:                        0
% 11.99/2.00  
% 11.99/2.00  ------ BMC1
% 11.99/2.00  
% 11.99/2.00  bmc1_current_bound:                     -1
% 11.99/2.00  bmc1_last_solved_bound:                 -1
% 11.99/2.00  bmc1_unsat_core_size:                   -1
% 11.99/2.00  bmc1_unsat_core_parents_size:           -1
% 11.99/2.00  bmc1_merge_next_fun:                    0
% 11.99/2.00  bmc1_unsat_core_clauses_time:           0.
% 11.99/2.00  
% 11.99/2.00  ------ Instantiation
% 11.99/2.00  
% 11.99/2.00  inst_num_of_clauses:                    668
% 11.99/2.00  inst_num_in_passive:                    114
% 11.99/2.00  inst_num_in_active:                     2424
% 11.99/2.00  inst_num_in_unprocessed:                224
% 11.99/2.00  inst_num_of_loops:                      3379
% 11.99/2.00  inst_num_of_learning_restarts:          1
% 11.99/2.00  inst_num_moves_active_passive:          946
% 11.99/2.00  inst_lit_activity:                      0
% 11.99/2.00  inst_lit_activity_moves:                0
% 11.99/2.00  inst_num_tautologies:                   0
% 11.99/2.00  inst_num_prop_implied:                  0
% 11.99/2.00  inst_num_existing_simplified:           0
% 11.99/2.00  inst_num_eq_res_simplified:             0
% 11.99/2.00  inst_num_child_elim:                    0
% 11.99/2.00  inst_num_of_dismatching_blockings:      2564
% 11.99/2.00  inst_num_of_non_proper_insts:           9342
% 11.99/2.00  inst_num_of_duplicates:                 0
% 11.99/2.00  inst_inst_num_from_inst_to_res:         0
% 11.99/2.00  inst_dismatching_checking_time:         0.
% 11.99/2.00  
% 11.99/2.00  ------ Resolution
% 11.99/2.00  
% 11.99/2.00  res_num_of_clauses:                     45
% 11.99/2.00  res_num_in_passive:                     45
% 11.99/2.00  res_num_in_active:                      0
% 11.99/2.00  res_num_of_loops:                       162
% 11.99/2.00  res_forward_subset_subsumed:            507
% 11.99/2.00  res_backward_subset_subsumed:           6
% 11.99/2.00  res_forward_subsumed:                   0
% 11.99/2.00  res_backward_subsumed:                  0
% 11.99/2.00  res_forward_subsumption_resolution:     1
% 11.99/2.00  res_backward_subsumption_resolution:    0
% 11.99/2.00  res_clause_to_clause_subsumption:       12262
% 11.99/2.00  res_orphan_elimination:                 0
% 11.99/2.00  res_tautology_del:                      1062
% 11.99/2.00  res_num_eq_res_simplified:              1
% 11.99/2.00  res_num_sel_changes:                    0
% 11.99/2.00  res_moves_from_active_to_pass:          0
% 11.99/2.00  
% 11.99/2.00  ------ Superposition
% 11.99/2.00  
% 11.99/2.00  sup_time_total:                         0.
% 11.99/2.00  sup_time_generating:                    0.
% 11.99/2.00  sup_time_sim_full:                      0.
% 11.99/2.00  sup_time_sim_immed:                     0.
% 11.99/2.00  
% 11.99/2.00  sup_num_of_clauses:                     1895
% 11.99/2.00  sup_num_in_active:                      493
% 11.99/2.00  sup_num_in_passive:                     1402
% 11.99/2.00  sup_num_of_loops:                       675
% 11.99/2.00  sup_fw_superposition:                   2264
% 11.99/2.00  sup_bw_superposition:                   1512
% 11.99/2.00  sup_immediate_simplified:               1164
% 11.99/2.00  sup_given_eliminated:                   1
% 11.99/2.00  comparisons_done:                       0
% 11.99/2.00  comparisons_avoided:                    87
% 11.99/2.00  
% 11.99/2.00  ------ Simplifications
% 11.99/2.00  
% 11.99/2.00  
% 11.99/2.00  sim_fw_subset_subsumed:                 354
% 11.99/2.00  sim_bw_subset_subsumed:                 79
% 11.99/2.00  sim_fw_subsumed:                        518
% 11.99/2.00  sim_bw_subsumed:                        185
% 11.99/2.00  sim_fw_subsumption_res:                 0
% 11.99/2.00  sim_bw_subsumption_res:                 0
% 11.99/2.00  sim_tautology_del:                      56
% 11.99/2.00  sim_eq_tautology_del:                   158
% 11.99/2.00  sim_eq_res_simp:                        0
% 11.99/2.00  sim_fw_demodulated:                     121
% 11.99/2.00  sim_bw_demodulated:                     11
% 11.99/2.00  sim_light_normalised:                   203
% 11.99/2.00  sim_joinable_taut:                      0
% 11.99/2.00  sim_joinable_simp:                      0
% 11.99/2.00  sim_ac_normalised:                      0
% 11.99/2.00  sim_smt_subsumption:                    0
% 11.99/2.00  
%------------------------------------------------------------------------------
