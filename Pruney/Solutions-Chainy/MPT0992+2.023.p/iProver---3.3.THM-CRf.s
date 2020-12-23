%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:51 EST 2020

% Result     : Theorem 3.36s
% Output     : CNFRefutation 3.36s
% Verified   : 
% Statistics : Number of formulae       :  194 (3970 expanded)
%              Number of clauses        :  126 (1320 expanded)
%              Number of leaves         :   21 ( 750 expanded)
%              Depth                    :   27
%              Number of atoms          :  559 (21678 expanded)
%              Number of equality atoms :  266 (5725 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   2 average)

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
    inference(ennf_transformation,[],[f21])).

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

fof(f49,plain,
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

fof(f50,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f46,f49])).

fof(f83,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f50])).

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
    inference(ennf_transformation,[],[f16])).

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

fof(f48,plain,(
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

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f81,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f82,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f50])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f43])).

fof(f79,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f18,axiom,(
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
    inference(ennf_transformation,[],[f18])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f80,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f17,axiom,(
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
    inference(ennf_transformation,[],[f17])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f78,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f85,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f50])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f84,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f50])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f52,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

cnf(c_31,negated_conjecture,
    ( r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1635,plain,
    ( r1_tarski(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_33,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_644,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X0
    | sK1 != X2
    | sK0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_33])).

cnf(c_645,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_644])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_647,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_645,c_32])).

cnf(c_1634,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1640,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2941,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1634,c_1640])).

cnf(c_2949,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_647,c_2941])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1644,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3591,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2949,c_1644])).

cnf(c_37,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1920,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1921,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1920])).

cnf(c_3839,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | sK1 = k1_xboole_0
    | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3591,c_37,c_1921])).

cnf(c_3840,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3839])).

cnf(c_3848,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1635,c_3840])).

cnf(c_26,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1636,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_5352,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3848,c_1636])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1637,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_4601,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1634,c_1637])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2005,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_2141,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_2005])).

cnf(c_4686,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4601,c_34,c_32,c_2141])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1638,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4482,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1634,c_1638])).

cnf(c_35,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_1969,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(k2_partfun1(X0,X1,sK3,X2))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_2133,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1969])).

cnf(c_2134,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2133])).

cnf(c_4618,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4482,c_35,c_37,c_2134])).

cnf(c_4695,plain,
    ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4686,c_4618])).

cnf(c_6318,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5352,c_4695])).

cnf(c_27,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_29,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_655,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_relat_1(X0)
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_relat_1(X0) != sK2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_29])).

cnf(c_656,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
    inference(unflattening,[status(thm)],[c_655])).

cnf(c_13,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_6,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_370,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_13,c_6])).

cnf(c_374,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_370,c_12])).

cnf(c_375,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_374])).

cnf(c_668,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_656,c_12,c_375])).

cnf(c_1622,plain,
    ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_668])).

cnf(c_4691,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4686,c_1622])).

cnf(c_4727,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4691,c_4695])).

cnf(c_4815,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3848,c_4727])).

cnf(c_6329,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6318,c_4815])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1639,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_5259,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4686,c_1639])).

cnf(c_5956,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5259,c_35,c_37])).

cnf(c_1642,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_5968,plain,
    ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5956,c_1642])).

cnf(c_1631,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_375])).

cnf(c_5964,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_5956,c_1631])).

cnf(c_7017,plain,
    ( sK1 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6329,c_5968,c_5964])).

cnf(c_673,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != sK3
    | sK2 != sK0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_33])).

cnf(c_869,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != sK3
    | sK2 != sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_673])).

cnf(c_1621,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != sK3
    | sK2 != sK0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_869])).

cnf(c_4692,plain,
    ( k7_relat_1(sK3,sK2) != sK3
    | sK2 != sK0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4686,c_1621])).

cnf(c_4720,plain,
    ( k7_relat_1(sK3,sK2) != sK3
    | sK2 != sK0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4692,c_4695])).

cnf(c_7026,plain,
    ( k7_relat_1(sK3,sK2) != sK3
    | sK2 != sK0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7017,c_4720])).

cnf(c_30,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_7037,plain,
    ( sK0 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7017,c_30])).

cnf(c_7038,plain,
    ( sK0 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_7037])).

cnf(c_7061,plain,
    ( k7_relat_1(sK3,sK2) != sK3
    | sK2 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7026,c_7038])).

cnf(c_7114,plain,
    ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7038,c_1635])).

cnf(c_4,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1645,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_14,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_7,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_350,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_14,c_7])).

cnf(c_354,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_350,c_14,c_12,c_7])).

cnf(c_1632,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_354])).

cnf(c_3074,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1645,c_1632])).

cnf(c_9,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_3590,plain,
    ( k1_relat_1(k7_relat_1(k1_xboole_0,X0)) = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_1644])).

cnf(c_1912,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1914,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1912])).

cnf(c_1913,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1916,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1913])).

cnf(c_3613,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | k1_relat_1(k7_relat_1(k1_xboole_0,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3590,c_1914,c_1916])).

cnf(c_3614,plain,
    ( k1_relat_1(k7_relat_1(k1_xboole_0,X0)) = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3613])).

cnf(c_4215,plain,
    ( k1_relat_1(k1_xboole_0) = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3074,c_3614])).

cnf(c_4222,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4215,c_9])).

cnf(c_7616,plain,
    ( sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7114,c_4222])).

cnf(c_8077,plain,
    ( k7_relat_1(sK3,sK2) != sK3
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7061,c_7616])).

cnf(c_3075,plain,
    ( k7_relat_1(sK3,sK0) = sK3 ),
    inference(superposition,[status(thm)],[c_1634,c_1632])).

cnf(c_7112,plain,
    ( k7_relat_1(sK3,k1_xboole_0) = sK3 ),
    inference(demodulation,[status(thm)],[c_7038,c_3075])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1641,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_5966,plain,
    ( v1_xboole_0(k7_relat_1(sK3,X0)) = iProver_top
    | v1_xboole_0(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5956,c_1641])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1648,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_6748,plain,
    ( k7_relat_1(sK3,X0) = k1_xboole_0
    | v1_xboole_0(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5966,c_1648])).

cnf(c_3,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_106,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1129,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2166,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK0)
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_1129])).

cnf(c_2168,plain,
    ( v1_xboole_0(sK0)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2166])).

cnf(c_1128,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1956,plain,
    ( sK0 != X0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1128])).

cnf(c_2269,plain,
    ( sK0 != sK0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1956])).

cnf(c_1127,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2270,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1127])).

cnf(c_2333,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1128])).

cnf(c_2334,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2333])).

cnf(c_6760,plain,
    ( ~ v1_xboole_0(sK0)
    | k7_relat_1(sK3,X0) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6748])).

cnf(c_7679,plain,
    ( k7_relat_1(sK3,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6748,c_30,c_106,c_0,c_2168,c_2269,c_2270,c_2334,c_6760,c_7017])).

cnf(c_7920,plain,
    ( sK3 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7112,c_7679])).

cnf(c_8081,plain,
    ( k7_relat_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | m1_subset_1(k7_relat_1(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8077,c_7616,c_7920])).

cnf(c_8082,plain,
    ( k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8081,c_3074])).

cnf(c_8083,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_8082])).

cnf(c_8085,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8083,c_1645])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:53:31 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.36/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/1.00  
% 3.36/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.36/1.00  
% 3.36/1.00  ------  iProver source info
% 3.36/1.00  
% 3.36/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.36/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.36/1.00  git: non_committed_changes: false
% 3.36/1.00  git: last_make_outside_of_git: false
% 3.36/1.00  
% 3.36/1.00  ------ 
% 3.36/1.00  
% 3.36/1.00  ------ Input Options
% 3.36/1.00  
% 3.36/1.00  --out_options                           all
% 3.36/1.00  --tptp_safe_out                         true
% 3.36/1.00  --problem_path                          ""
% 3.36/1.00  --include_path                          ""
% 3.36/1.00  --clausifier                            res/vclausify_rel
% 3.36/1.00  --clausifier_options                    --mode clausify
% 3.36/1.00  --stdin                                 false
% 3.36/1.00  --stats_out                             all
% 3.36/1.00  
% 3.36/1.00  ------ General Options
% 3.36/1.00  
% 3.36/1.00  --fof                                   false
% 3.36/1.00  --time_out_real                         305.
% 3.36/1.00  --time_out_virtual                      -1.
% 3.36/1.00  --symbol_type_check                     false
% 3.36/1.00  --clausify_out                          false
% 3.36/1.00  --sig_cnt_out                           false
% 3.36/1.00  --trig_cnt_out                          false
% 3.36/1.00  --trig_cnt_out_tolerance                1.
% 3.36/1.00  --trig_cnt_out_sk_spl                   false
% 3.36/1.00  --abstr_cl_out                          false
% 3.36/1.00  
% 3.36/1.00  ------ Global Options
% 3.36/1.00  
% 3.36/1.00  --schedule                              default
% 3.36/1.00  --add_important_lit                     false
% 3.36/1.00  --prop_solver_per_cl                    1000
% 3.36/1.00  --min_unsat_core                        false
% 3.36/1.00  --soft_assumptions                      false
% 3.36/1.00  --soft_lemma_size                       3
% 3.36/1.00  --prop_impl_unit_size                   0
% 3.36/1.00  --prop_impl_unit                        []
% 3.36/1.00  --share_sel_clauses                     true
% 3.36/1.00  --reset_solvers                         false
% 3.36/1.00  --bc_imp_inh                            [conj_cone]
% 3.36/1.00  --conj_cone_tolerance                   3.
% 3.36/1.00  --extra_neg_conj                        none
% 3.36/1.00  --large_theory_mode                     true
% 3.36/1.00  --prolific_symb_bound                   200
% 3.36/1.00  --lt_threshold                          2000
% 3.36/1.00  --clause_weak_htbl                      true
% 3.36/1.00  --gc_record_bc_elim                     false
% 3.36/1.00  
% 3.36/1.00  ------ Preprocessing Options
% 3.36/1.00  
% 3.36/1.00  --preprocessing_flag                    true
% 3.36/1.00  --time_out_prep_mult                    0.1
% 3.36/1.00  --splitting_mode                        input
% 3.36/1.00  --splitting_grd                         true
% 3.36/1.00  --splitting_cvd                         false
% 3.36/1.00  --splitting_cvd_svl                     false
% 3.36/1.00  --splitting_nvd                         32
% 3.36/1.00  --sub_typing                            true
% 3.36/1.00  --prep_gs_sim                           true
% 3.36/1.00  --prep_unflatten                        true
% 3.36/1.00  --prep_res_sim                          true
% 3.36/1.00  --prep_upred                            true
% 3.36/1.00  --prep_sem_filter                       exhaustive
% 3.36/1.00  --prep_sem_filter_out                   false
% 3.36/1.00  --pred_elim                             true
% 3.36/1.00  --res_sim_input                         true
% 3.36/1.00  --eq_ax_congr_red                       true
% 3.36/1.00  --pure_diseq_elim                       true
% 3.36/1.00  --brand_transform                       false
% 3.36/1.00  --non_eq_to_eq                          false
% 3.36/1.00  --prep_def_merge                        true
% 3.36/1.00  --prep_def_merge_prop_impl              false
% 3.36/1.00  --prep_def_merge_mbd                    true
% 3.36/1.00  --prep_def_merge_tr_red                 false
% 3.36/1.00  --prep_def_merge_tr_cl                  false
% 3.36/1.00  --smt_preprocessing                     true
% 3.36/1.00  --smt_ac_axioms                         fast
% 3.36/1.00  --preprocessed_out                      false
% 3.36/1.00  --preprocessed_stats                    false
% 3.36/1.00  
% 3.36/1.00  ------ Abstraction refinement Options
% 3.36/1.00  
% 3.36/1.00  --abstr_ref                             []
% 3.36/1.00  --abstr_ref_prep                        false
% 3.36/1.00  --abstr_ref_until_sat                   false
% 3.36/1.00  --abstr_ref_sig_restrict                funpre
% 3.36/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.36/1.00  --abstr_ref_under                       []
% 3.36/1.00  
% 3.36/1.00  ------ SAT Options
% 3.36/1.00  
% 3.36/1.00  --sat_mode                              false
% 3.36/1.00  --sat_fm_restart_options                ""
% 3.36/1.00  --sat_gr_def                            false
% 3.36/1.00  --sat_epr_types                         true
% 3.36/1.00  --sat_non_cyclic_types                  false
% 3.36/1.00  --sat_finite_models                     false
% 3.36/1.00  --sat_fm_lemmas                         false
% 3.36/1.00  --sat_fm_prep                           false
% 3.36/1.00  --sat_fm_uc_incr                        true
% 3.36/1.00  --sat_out_model                         small
% 3.36/1.00  --sat_out_clauses                       false
% 3.36/1.00  
% 3.36/1.00  ------ QBF Options
% 3.36/1.00  
% 3.36/1.00  --qbf_mode                              false
% 3.36/1.00  --qbf_elim_univ                         false
% 3.36/1.00  --qbf_dom_inst                          none
% 3.36/1.00  --qbf_dom_pre_inst                      false
% 3.36/1.00  --qbf_sk_in                             false
% 3.36/1.00  --qbf_pred_elim                         true
% 3.36/1.00  --qbf_split                             512
% 3.36/1.00  
% 3.36/1.00  ------ BMC1 Options
% 3.36/1.00  
% 3.36/1.00  --bmc1_incremental                      false
% 3.36/1.00  --bmc1_axioms                           reachable_all
% 3.36/1.00  --bmc1_min_bound                        0
% 3.36/1.00  --bmc1_max_bound                        -1
% 3.36/1.00  --bmc1_max_bound_default                -1
% 3.36/1.00  --bmc1_symbol_reachability              true
% 3.36/1.00  --bmc1_property_lemmas                  false
% 3.36/1.00  --bmc1_k_induction                      false
% 3.36/1.00  --bmc1_non_equiv_states                 false
% 3.36/1.00  --bmc1_deadlock                         false
% 3.36/1.00  --bmc1_ucm                              false
% 3.36/1.00  --bmc1_add_unsat_core                   none
% 3.36/1.00  --bmc1_unsat_core_children              false
% 3.36/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.36/1.00  --bmc1_out_stat                         full
% 3.36/1.00  --bmc1_ground_init                      false
% 3.36/1.00  --bmc1_pre_inst_next_state              false
% 3.36/1.00  --bmc1_pre_inst_state                   false
% 3.36/1.00  --bmc1_pre_inst_reach_state             false
% 3.36/1.00  --bmc1_out_unsat_core                   false
% 3.36/1.00  --bmc1_aig_witness_out                  false
% 3.36/1.00  --bmc1_verbose                          false
% 3.36/1.00  --bmc1_dump_clauses_tptp                false
% 3.36/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.36/1.00  --bmc1_dump_file                        -
% 3.36/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.36/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.36/1.00  --bmc1_ucm_extend_mode                  1
% 3.36/1.00  --bmc1_ucm_init_mode                    2
% 3.36/1.00  --bmc1_ucm_cone_mode                    none
% 3.36/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.36/1.00  --bmc1_ucm_relax_model                  4
% 3.36/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.36/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.36/1.00  --bmc1_ucm_layered_model                none
% 3.36/1.00  --bmc1_ucm_max_lemma_size               10
% 3.36/1.00  
% 3.36/1.00  ------ AIG Options
% 3.36/1.00  
% 3.36/1.00  --aig_mode                              false
% 3.36/1.00  
% 3.36/1.00  ------ Instantiation Options
% 3.36/1.00  
% 3.36/1.00  --instantiation_flag                    true
% 3.36/1.00  --inst_sos_flag                         false
% 3.36/1.00  --inst_sos_phase                        true
% 3.36/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.36/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.36/1.00  --inst_lit_sel_side                     num_symb
% 3.36/1.00  --inst_solver_per_active                1400
% 3.36/1.00  --inst_solver_calls_frac                1.
% 3.36/1.00  --inst_passive_queue_type               priority_queues
% 3.36/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.36/1.00  --inst_passive_queues_freq              [25;2]
% 3.36/1.00  --inst_dismatching                      true
% 3.36/1.00  --inst_eager_unprocessed_to_passive     true
% 3.36/1.00  --inst_prop_sim_given                   true
% 3.36/1.00  --inst_prop_sim_new                     false
% 3.36/1.00  --inst_subs_new                         false
% 3.36/1.00  --inst_eq_res_simp                      false
% 3.36/1.00  --inst_subs_given                       false
% 3.36/1.00  --inst_orphan_elimination               true
% 3.36/1.00  --inst_learning_loop_flag               true
% 3.36/1.00  --inst_learning_start                   3000
% 3.36/1.00  --inst_learning_factor                  2
% 3.36/1.00  --inst_start_prop_sim_after_learn       3
% 3.36/1.00  --inst_sel_renew                        solver
% 3.36/1.00  --inst_lit_activity_flag                true
% 3.36/1.00  --inst_restr_to_given                   false
% 3.36/1.00  --inst_activity_threshold               500
% 3.36/1.00  --inst_out_proof                        true
% 3.36/1.00  
% 3.36/1.00  ------ Resolution Options
% 3.36/1.00  
% 3.36/1.00  --resolution_flag                       true
% 3.36/1.00  --res_lit_sel                           adaptive
% 3.36/1.00  --res_lit_sel_side                      none
% 3.36/1.00  --res_ordering                          kbo
% 3.36/1.00  --res_to_prop_solver                    active
% 3.36/1.00  --res_prop_simpl_new                    false
% 3.36/1.00  --res_prop_simpl_given                  true
% 3.36/1.00  --res_passive_queue_type                priority_queues
% 3.36/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.36/1.00  --res_passive_queues_freq               [15;5]
% 3.36/1.00  --res_forward_subs                      full
% 3.36/1.00  --res_backward_subs                     full
% 3.36/1.00  --res_forward_subs_resolution           true
% 3.36/1.00  --res_backward_subs_resolution          true
% 3.36/1.00  --res_orphan_elimination                true
% 3.36/1.00  --res_time_limit                        2.
% 3.36/1.00  --res_out_proof                         true
% 3.36/1.00  
% 3.36/1.00  ------ Superposition Options
% 3.36/1.00  
% 3.36/1.00  --superposition_flag                    true
% 3.36/1.00  --sup_passive_queue_type                priority_queues
% 3.36/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.36/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.36/1.00  --demod_completeness_check              fast
% 3.36/1.00  --demod_use_ground                      true
% 3.36/1.00  --sup_to_prop_solver                    passive
% 3.36/1.00  --sup_prop_simpl_new                    true
% 3.36/1.00  --sup_prop_simpl_given                  true
% 3.36/1.00  --sup_fun_splitting                     false
% 3.36/1.00  --sup_smt_interval                      50000
% 3.36/1.00  
% 3.36/1.00  ------ Superposition Simplification Setup
% 3.36/1.00  
% 3.36/1.00  --sup_indices_passive                   []
% 3.36/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.36/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.36/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.36/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.36/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.36/1.00  --sup_full_bw                           [BwDemod]
% 3.36/1.00  --sup_immed_triv                        [TrivRules]
% 3.36/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.36/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.36/1.00  --sup_immed_bw_main                     []
% 3.36/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.36/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.36/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.36/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.36/1.00  
% 3.36/1.00  ------ Combination Options
% 3.36/1.00  
% 3.36/1.00  --comb_res_mult                         3
% 3.36/1.00  --comb_sup_mult                         2
% 3.36/1.00  --comb_inst_mult                        10
% 3.36/1.00  
% 3.36/1.00  ------ Debug Options
% 3.36/1.00  
% 3.36/1.00  --dbg_backtrace                         false
% 3.36/1.00  --dbg_dump_prop_clauses                 false
% 3.36/1.00  --dbg_dump_prop_clauses_file            -
% 3.36/1.00  --dbg_out_stat                          false
% 3.36/1.00  ------ Parsing...
% 3.36/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.36/1.00  
% 3.36/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.36/1.00  
% 3.36/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.36/1.00  
% 3.36/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.36/1.00  ------ Proving...
% 3.36/1.00  ------ Problem Properties 
% 3.36/1.00  
% 3.36/1.00  
% 3.36/1.00  clauses                                 33
% 3.36/1.00  conjectures                             4
% 3.36/1.00  EPR                                     7
% 3.36/1.00  Horn                                    29
% 3.36/1.00  unary                                   7
% 3.36/1.00  binary                                  8
% 3.36/1.00  lits                                    90
% 3.36/1.00  lits eq                                 33
% 3.36/1.00  fd_pure                                 0
% 3.36/1.00  fd_pseudo                               0
% 3.36/1.00  fd_cond                                 3
% 3.36/1.00  fd_pseudo_cond                          1
% 3.36/1.00  AC symbols                              0
% 3.36/1.00  
% 3.36/1.00  ------ Schedule dynamic 5 is on 
% 3.36/1.00  
% 3.36/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.36/1.00  
% 3.36/1.00  
% 3.36/1.00  ------ 
% 3.36/1.00  Current options:
% 3.36/1.00  ------ 
% 3.36/1.00  
% 3.36/1.00  ------ Input Options
% 3.36/1.00  
% 3.36/1.00  --out_options                           all
% 3.36/1.00  --tptp_safe_out                         true
% 3.36/1.00  --problem_path                          ""
% 3.36/1.00  --include_path                          ""
% 3.36/1.00  --clausifier                            res/vclausify_rel
% 3.36/1.00  --clausifier_options                    --mode clausify
% 3.36/1.00  --stdin                                 false
% 3.36/1.00  --stats_out                             all
% 3.36/1.00  
% 3.36/1.00  ------ General Options
% 3.36/1.00  
% 3.36/1.00  --fof                                   false
% 3.36/1.00  --time_out_real                         305.
% 3.36/1.00  --time_out_virtual                      -1.
% 3.36/1.00  --symbol_type_check                     false
% 3.36/1.00  --clausify_out                          false
% 3.36/1.00  --sig_cnt_out                           false
% 3.36/1.00  --trig_cnt_out                          false
% 3.36/1.00  --trig_cnt_out_tolerance                1.
% 3.36/1.00  --trig_cnt_out_sk_spl                   false
% 3.36/1.00  --abstr_cl_out                          false
% 3.36/1.00  
% 3.36/1.00  ------ Global Options
% 3.36/1.00  
% 3.36/1.00  --schedule                              default
% 3.36/1.00  --add_important_lit                     false
% 3.36/1.00  --prop_solver_per_cl                    1000
% 3.36/1.00  --min_unsat_core                        false
% 3.36/1.00  --soft_assumptions                      false
% 3.36/1.00  --soft_lemma_size                       3
% 3.36/1.00  --prop_impl_unit_size                   0
% 3.36/1.00  --prop_impl_unit                        []
% 3.36/1.00  --share_sel_clauses                     true
% 3.36/1.00  --reset_solvers                         false
% 3.36/1.00  --bc_imp_inh                            [conj_cone]
% 3.36/1.00  --conj_cone_tolerance                   3.
% 3.36/1.00  --extra_neg_conj                        none
% 3.36/1.00  --large_theory_mode                     true
% 3.36/1.00  --prolific_symb_bound                   200
% 3.36/1.00  --lt_threshold                          2000
% 3.36/1.00  --clause_weak_htbl                      true
% 3.36/1.00  --gc_record_bc_elim                     false
% 3.36/1.00  
% 3.36/1.00  ------ Preprocessing Options
% 3.36/1.00  
% 3.36/1.00  --preprocessing_flag                    true
% 3.36/1.00  --time_out_prep_mult                    0.1
% 3.36/1.00  --splitting_mode                        input
% 3.36/1.00  --splitting_grd                         true
% 3.36/1.00  --splitting_cvd                         false
% 3.36/1.00  --splitting_cvd_svl                     false
% 3.36/1.00  --splitting_nvd                         32
% 3.36/1.00  --sub_typing                            true
% 3.36/1.00  --prep_gs_sim                           true
% 3.36/1.00  --prep_unflatten                        true
% 3.36/1.00  --prep_res_sim                          true
% 3.36/1.00  --prep_upred                            true
% 3.36/1.00  --prep_sem_filter                       exhaustive
% 3.36/1.00  --prep_sem_filter_out                   false
% 3.36/1.00  --pred_elim                             true
% 3.36/1.00  --res_sim_input                         true
% 3.36/1.00  --eq_ax_congr_red                       true
% 3.36/1.00  --pure_diseq_elim                       true
% 3.36/1.00  --brand_transform                       false
% 3.36/1.00  --non_eq_to_eq                          false
% 3.36/1.00  --prep_def_merge                        true
% 3.36/1.00  --prep_def_merge_prop_impl              false
% 3.36/1.00  --prep_def_merge_mbd                    true
% 3.36/1.00  --prep_def_merge_tr_red                 false
% 3.36/1.00  --prep_def_merge_tr_cl                  false
% 3.36/1.00  --smt_preprocessing                     true
% 3.36/1.00  --smt_ac_axioms                         fast
% 3.36/1.00  --preprocessed_out                      false
% 3.36/1.00  --preprocessed_stats                    false
% 3.36/1.00  
% 3.36/1.00  ------ Abstraction refinement Options
% 3.36/1.00  
% 3.36/1.00  --abstr_ref                             []
% 3.36/1.00  --abstr_ref_prep                        false
% 3.36/1.00  --abstr_ref_until_sat                   false
% 3.36/1.00  --abstr_ref_sig_restrict                funpre
% 3.36/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.36/1.00  --abstr_ref_under                       []
% 3.36/1.00  
% 3.36/1.00  ------ SAT Options
% 3.36/1.00  
% 3.36/1.00  --sat_mode                              false
% 3.36/1.00  --sat_fm_restart_options                ""
% 3.36/1.00  --sat_gr_def                            false
% 3.36/1.00  --sat_epr_types                         true
% 3.36/1.00  --sat_non_cyclic_types                  false
% 3.36/1.00  --sat_finite_models                     false
% 3.36/1.00  --sat_fm_lemmas                         false
% 3.36/1.00  --sat_fm_prep                           false
% 3.36/1.00  --sat_fm_uc_incr                        true
% 3.36/1.00  --sat_out_model                         small
% 3.36/1.00  --sat_out_clauses                       false
% 3.36/1.00  
% 3.36/1.00  ------ QBF Options
% 3.36/1.00  
% 3.36/1.00  --qbf_mode                              false
% 3.36/1.00  --qbf_elim_univ                         false
% 3.36/1.00  --qbf_dom_inst                          none
% 3.36/1.00  --qbf_dom_pre_inst                      false
% 3.36/1.00  --qbf_sk_in                             false
% 3.36/1.00  --qbf_pred_elim                         true
% 3.36/1.00  --qbf_split                             512
% 3.36/1.00  
% 3.36/1.00  ------ BMC1 Options
% 3.36/1.00  
% 3.36/1.00  --bmc1_incremental                      false
% 3.36/1.00  --bmc1_axioms                           reachable_all
% 3.36/1.00  --bmc1_min_bound                        0
% 3.36/1.00  --bmc1_max_bound                        -1
% 3.36/1.00  --bmc1_max_bound_default                -1
% 3.36/1.00  --bmc1_symbol_reachability              true
% 3.36/1.00  --bmc1_property_lemmas                  false
% 3.36/1.00  --bmc1_k_induction                      false
% 3.36/1.00  --bmc1_non_equiv_states                 false
% 3.36/1.00  --bmc1_deadlock                         false
% 3.36/1.00  --bmc1_ucm                              false
% 3.36/1.00  --bmc1_add_unsat_core                   none
% 3.36/1.00  --bmc1_unsat_core_children              false
% 3.36/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.36/1.00  --bmc1_out_stat                         full
% 3.36/1.00  --bmc1_ground_init                      false
% 3.36/1.00  --bmc1_pre_inst_next_state              false
% 3.36/1.00  --bmc1_pre_inst_state                   false
% 3.36/1.00  --bmc1_pre_inst_reach_state             false
% 3.36/1.00  --bmc1_out_unsat_core                   false
% 3.36/1.00  --bmc1_aig_witness_out                  false
% 3.36/1.00  --bmc1_verbose                          false
% 3.36/1.00  --bmc1_dump_clauses_tptp                false
% 3.36/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.36/1.00  --bmc1_dump_file                        -
% 3.36/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.36/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.36/1.00  --bmc1_ucm_extend_mode                  1
% 3.36/1.00  --bmc1_ucm_init_mode                    2
% 3.36/1.00  --bmc1_ucm_cone_mode                    none
% 3.36/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.36/1.00  --bmc1_ucm_relax_model                  4
% 3.36/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.36/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.36/1.00  --bmc1_ucm_layered_model                none
% 3.36/1.00  --bmc1_ucm_max_lemma_size               10
% 3.36/1.00  
% 3.36/1.00  ------ AIG Options
% 3.36/1.00  
% 3.36/1.00  --aig_mode                              false
% 3.36/1.00  
% 3.36/1.00  ------ Instantiation Options
% 3.36/1.00  
% 3.36/1.00  --instantiation_flag                    true
% 3.36/1.00  --inst_sos_flag                         false
% 3.36/1.00  --inst_sos_phase                        true
% 3.36/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.36/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.36/1.00  --inst_lit_sel_side                     none
% 3.36/1.00  --inst_solver_per_active                1400
% 3.36/1.00  --inst_solver_calls_frac                1.
% 3.36/1.00  --inst_passive_queue_type               priority_queues
% 3.36/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.36/1.00  --inst_passive_queues_freq              [25;2]
% 3.36/1.00  --inst_dismatching                      true
% 3.36/1.00  --inst_eager_unprocessed_to_passive     true
% 3.36/1.00  --inst_prop_sim_given                   true
% 3.36/1.00  --inst_prop_sim_new                     false
% 3.36/1.00  --inst_subs_new                         false
% 3.36/1.00  --inst_eq_res_simp                      false
% 3.36/1.00  --inst_subs_given                       false
% 3.36/1.00  --inst_orphan_elimination               true
% 3.36/1.00  --inst_learning_loop_flag               true
% 3.36/1.00  --inst_learning_start                   3000
% 3.36/1.00  --inst_learning_factor                  2
% 3.36/1.00  --inst_start_prop_sim_after_learn       3
% 3.36/1.00  --inst_sel_renew                        solver
% 3.36/1.00  --inst_lit_activity_flag                true
% 3.36/1.00  --inst_restr_to_given                   false
% 3.36/1.00  --inst_activity_threshold               500
% 3.36/1.00  --inst_out_proof                        true
% 3.36/1.00  
% 3.36/1.00  ------ Resolution Options
% 3.36/1.00  
% 3.36/1.00  --resolution_flag                       false
% 3.36/1.00  --res_lit_sel                           adaptive
% 3.36/1.00  --res_lit_sel_side                      none
% 3.36/1.00  --res_ordering                          kbo
% 3.36/1.00  --res_to_prop_solver                    active
% 3.36/1.00  --res_prop_simpl_new                    false
% 3.36/1.00  --res_prop_simpl_given                  true
% 3.36/1.00  --res_passive_queue_type                priority_queues
% 3.36/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.36/1.00  --res_passive_queues_freq               [15;5]
% 3.36/1.00  --res_forward_subs                      full
% 3.36/1.00  --res_backward_subs                     full
% 3.36/1.00  --res_forward_subs_resolution           true
% 3.36/1.00  --res_backward_subs_resolution          true
% 3.36/1.00  --res_orphan_elimination                true
% 3.36/1.00  --res_time_limit                        2.
% 3.36/1.00  --res_out_proof                         true
% 3.36/1.00  
% 3.36/1.00  ------ Superposition Options
% 3.36/1.00  
% 3.36/1.00  --superposition_flag                    true
% 3.36/1.00  --sup_passive_queue_type                priority_queues
% 3.36/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.36/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.36/1.00  --demod_completeness_check              fast
% 3.36/1.00  --demod_use_ground                      true
% 3.36/1.00  --sup_to_prop_solver                    passive
% 3.36/1.00  --sup_prop_simpl_new                    true
% 3.36/1.00  --sup_prop_simpl_given                  true
% 3.36/1.00  --sup_fun_splitting                     false
% 3.36/1.00  --sup_smt_interval                      50000
% 3.36/1.00  
% 3.36/1.00  ------ Superposition Simplification Setup
% 3.36/1.00  
% 3.36/1.00  --sup_indices_passive                   []
% 3.36/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.36/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.36/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.36/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.36/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.36/1.00  --sup_full_bw                           [BwDemod]
% 3.36/1.00  --sup_immed_triv                        [TrivRules]
% 3.36/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.36/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.36/1.00  --sup_immed_bw_main                     []
% 3.36/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.36/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.36/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.36/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.36/1.00  
% 3.36/1.00  ------ Combination Options
% 3.36/1.00  
% 3.36/1.00  --comb_res_mult                         3
% 3.36/1.00  --comb_sup_mult                         2
% 3.36/1.00  --comb_inst_mult                        10
% 3.36/1.00  
% 3.36/1.00  ------ Debug Options
% 3.36/1.00  
% 3.36/1.00  --dbg_backtrace                         false
% 3.36/1.00  --dbg_dump_prop_clauses                 false
% 3.36/1.00  --dbg_dump_prop_clauses_file            -
% 3.36/1.00  --dbg_out_stat                          false
% 3.36/1.00  
% 3.36/1.00  
% 3.36/1.00  
% 3.36/1.00  
% 3.36/1.00  ------ Proving...
% 3.36/1.00  
% 3.36/1.00  
% 3.36/1.00  % SZS status Theorem for theBenchmark.p
% 3.36/1.00  
% 3.36/1.00   Resolution empty clause
% 3.36/1.00  
% 3.36/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.36/1.00  
% 3.36/1.00  fof(f20,conjecture,(
% 3.36/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.00  
% 3.36/1.00  fof(f21,negated_conjecture,(
% 3.36/1.00    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.36/1.00    inference(negated_conjecture,[],[f20])).
% 3.36/1.00  
% 3.36/1.00  fof(f45,plain,(
% 3.36/1.00    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.36/1.00    inference(ennf_transformation,[],[f21])).
% 3.36/1.00  
% 3.36/1.00  fof(f46,plain,(
% 3.36/1.00    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.36/1.00    inference(flattening,[],[f45])).
% 3.36/1.00  
% 3.36/1.00  fof(f49,plain,(
% 3.36/1.00    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 3.36/1.00    introduced(choice_axiom,[])).
% 3.36/1.00  
% 3.36/1.00  fof(f50,plain,(
% 3.36/1.00    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 3.36/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f46,f49])).
% 3.36/1.00  
% 3.36/1.00  fof(f83,plain,(
% 3.36/1.00    r1_tarski(sK2,sK0)),
% 3.36/1.00    inference(cnf_transformation,[],[f50])).
% 3.36/1.00  
% 3.36/1.00  fof(f16,axiom,(
% 3.36/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.00  
% 3.36/1.00  fof(f37,plain,(
% 3.36/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.36/1.00    inference(ennf_transformation,[],[f16])).
% 3.36/1.00  
% 3.36/1.00  fof(f38,plain,(
% 3.36/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.36/1.00    inference(flattening,[],[f37])).
% 3.36/1.00  
% 3.36/1.00  fof(f48,plain,(
% 3.36/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.36/1.00    inference(nnf_transformation,[],[f38])).
% 3.36/1.00  
% 3.36/1.00  fof(f68,plain,(
% 3.36/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.36/1.00    inference(cnf_transformation,[],[f48])).
% 3.36/1.00  
% 3.36/1.00  fof(f81,plain,(
% 3.36/1.00    v1_funct_2(sK3,sK0,sK1)),
% 3.36/1.00    inference(cnf_transformation,[],[f50])).
% 3.36/1.00  
% 3.36/1.00  fof(f82,plain,(
% 3.36/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.36/1.00    inference(cnf_transformation,[],[f50])).
% 3.36/1.00  
% 3.36/1.00  fof(f15,axiom,(
% 3.36/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.00  
% 3.36/1.00  fof(f36,plain,(
% 3.36/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.36/1.00    inference(ennf_transformation,[],[f15])).
% 3.36/1.00  
% 3.36/1.00  fof(f67,plain,(
% 3.36/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.36/1.00    inference(cnf_transformation,[],[f36])).
% 3.36/1.00  
% 3.36/1.00  fof(f10,axiom,(
% 3.36/1.00    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 3.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.00  
% 3.36/1.00  fof(f30,plain,(
% 3.36/1.00    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 3.36/1.00    inference(ennf_transformation,[],[f10])).
% 3.36/1.00  
% 3.36/1.00  fof(f31,plain,(
% 3.36/1.00    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.36/1.00    inference(flattening,[],[f30])).
% 3.36/1.00  
% 3.36/1.00  fof(f61,plain,(
% 3.36/1.00    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.36/1.00    inference(cnf_transformation,[],[f31])).
% 3.36/1.00  
% 3.36/1.00  fof(f12,axiom,(
% 3.36/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.00  
% 3.36/1.00  fof(f33,plain,(
% 3.36/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.36/1.00    inference(ennf_transformation,[],[f12])).
% 3.36/1.00  
% 3.36/1.00  fof(f63,plain,(
% 3.36/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.36/1.00    inference(cnf_transformation,[],[f33])).
% 3.36/1.00  
% 3.36/1.00  fof(f19,axiom,(
% 3.36/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 3.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.00  
% 3.36/1.00  fof(f43,plain,(
% 3.36/1.00    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.36/1.00    inference(ennf_transformation,[],[f19])).
% 3.36/1.00  
% 3.36/1.00  fof(f44,plain,(
% 3.36/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.36/1.00    inference(flattening,[],[f43])).
% 3.36/1.00  
% 3.36/1.00  fof(f79,plain,(
% 3.36/1.00    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.36/1.00    inference(cnf_transformation,[],[f44])).
% 3.36/1.00  
% 3.36/1.00  fof(f18,axiom,(
% 3.36/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 3.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.00  
% 3.36/1.00  fof(f41,plain,(
% 3.36/1.00    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.36/1.00    inference(ennf_transformation,[],[f18])).
% 3.36/1.00  
% 3.36/1.00  fof(f42,plain,(
% 3.36/1.00    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.36/1.00    inference(flattening,[],[f41])).
% 3.36/1.00  
% 3.36/1.00  fof(f76,plain,(
% 3.36/1.00    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.36/1.00    inference(cnf_transformation,[],[f42])).
% 3.36/1.00  
% 3.36/1.00  fof(f80,plain,(
% 3.36/1.00    v1_funct_1(sK3)),
% 3.36/1.00    inference(cnf_transformation,[],[f50])).
% 3.36/1.00  
% 3.36/1.00  fof(f17,axiom,(
% 3.36/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 3.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.00  
% 3.36/1.00  fof(f39,plain,(
% 3.36/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.36/1.00    inference(ennf_transformation,[],[f17])).
% 3.36/1.00  
% 3.36/1.00  fof(f40,plain,(
% 3.36/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.36/1.00    inference(flattening,[],[f39])).
% 3.36/1.00  
% 3.36/1.00  fof(f74,plain,(
% 3.36/1.00    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.36/1.00    inference(cnf_transformation,[],[f40])).
% 3.36/1.00  
% 3.36/1.00  fof(f78,plain,(
% 3.36/1.00    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.36/1.00    inference(cnf_transformation,[],[f44])).
% 3.36/1.00  
% 3.36/1.00  fof(f85,plain,(
% 3.36/1.00    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 3.36/1.00    inference(cnf_transformation,[],[f50])).
% 3.36/1.00  
% 3.36/1.00  fof(f13,axiom,(
% 3.36/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.00  
% 3.36/1.00  fof(f34,plain,(
% 3.36/1.00    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.36/1.00    inference(ennf_transformation,[],[f13])).
% 3.36/1.00  
% 3.36/1.00  fof(f65,plain,(
% 3.36/1.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.36/1.00    inference(cnf_transformation,[],[f34])).
% 3.36/1.00  
% 3.36/1.00  fof(f7,axiom,(
% 3.36/1.00    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.00  
% 3.36/1.00  fof(f27,plain,(
% 3.36/1.00    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.36/1.00    inference(ennf_transformation,[],[f7])).
% 3.36/1.00  
% 3.36/1.00  fof(f47,plain,(
% 3.36/1.00    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.36/1.00    inference(nnf_transformation,[],[f27])).
% 3.36/1.00  
% 3.36/1.00  fof(f56,plain,(
% 3.36/1.00    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.36/1.00    inference(cnf_transformation,[],[f47])).
% 3.36/1.00  
% 3.36/1.00  fof(f75,plain,(
% 3.36/1.00    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.36/1.00    inference(cnf_transformation,[],[f40])).
% 3.36/1.00  
% 3.36/1.00  fof(f84,plain,(
% 3.36/1.00    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 3.36/1.00    inference(cnf_transformation,[],[f50])).
% 3.36/1.00  
% 3.36/1.00  fof(f5,axiom,(
% 3.36/1.00    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.00  
% 3.36/1.00  fof(f55,plain,(
% 3.36/1.00    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.36/1.00    inference(cnf_transformation,[],[f5])).
% 3.36/1.00  
% 3.36/1.00  fof(f64,plain,(
% 3.36/1.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.36/1.00    inference(cnf_transformation,[],[f34])).
% 3.36/1.00  
% 3.36/1.00  fof(f8,axiom,(
% 3.36/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 3.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.00  
% 3.36/1.00  fof(f28,plain,(
% 3.36/1.00    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.36/1.00    inference(ennf_transformation,[],[f8])).
% 3.36/1.00  
% 3.36/1.00  fof(f29,plain,(
% 3.36/1.00    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.36/1.00    inference(flattening,[],[f28])).
% 3.36/1.00  
% 3.36/1.00  fof(f58,plain,(
% 3.36/1.00    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.36/1.00    inference(cnf_transformation,[],[f29])).
% 3.36/1.00  
% 3.36/1.00  fof(f9,axiom,(
% 3.36/1.00    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.00  
% 3.36/1.00  fof(f59,plain,(
% 3.36/1.00    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.36/1.00    inference(cnf_transformation,[],[f9])).
% 3.36/1.00  
% 3.36/1.00  fof(f14,axiom,(
% 3.36/1.00    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 3.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.00  
% 3.36/1.00  fof(f35,plain,(
% 3.36/1.00    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 3.36/1.00    inference(ennf_transformation,[],[f14])).
% 3.36/1.00  
% 3.36/1.00  fof(f66,plain,(
% 3.36/1.00    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 3.36/1.00    inference(cnf_transformation,[],[f35])).
% 3.36/1.00  
% 3.36/1.00  fof(f2,axiom,(
% 3.36/1.00    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.00  
% 3.36/1.00  fof(f23,plain,(
% 3.36/1.00    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.36/1.00    inference(ennf_transformation,[],[f2])).
% 3.36/1.00  
% 3.36/1.00  fof(f52,plain,(
% 3.36/1.00    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.36/1.00    inference(cnf_transformation,[],[f23])).
% 3.36/1.00  
% 3.36/1.00  fof(f4,axiom,(
% 3.36/1.00    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 3.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.00  
% 3.36/1.00  fof(f26,plain,(
% 3.36/1.00    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 3.36/1.00    inference(ennf_transformation,[],[f4])).
% 3.36/1.00  
% 3.36/1.00  fof(f54,plain,(
% 3.36/1.00    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 3.36/1.00    inference(cnf_transformation,[],[f26])).
% 3.36/1.00  
% 3.36/1.00  fof(f1,axiom,(
% 3.36/1.00    v1_xboole_0(k1_xboole_0)),
% 3.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.00  
% 3.36/1.00  fof(f51,plain,(
% 3.36/1.00    v1_xboole_0(k1_xboole_0)),
% 3.36/1.00    inference(cnf_transformation,[],[f1])).
% 3.36/1.00  
% 3.36/1.00  cnf(c_31,negated_conjecture,
% 3.36/1.00      ( r1_tarski(sK2,sK0) ),
% 3.36/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_1635,plain,
% 3.36/1.00      ( r1_tarski(sK2,sK0) = iProver_top ),
% 3.36/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_22,plain,
% 3.36/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.36/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.36/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.36/1.00      | k1_xboole_0 = X2 ),
% 3.36/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_33,negated_conjecture,
% 3.36/1.00      ( v1_funct_2(sK3,sK0,sK1) ),
% 3.36/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_644,plain,
% 3.36/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.36/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.36/1.00      | sK3 != X0
% 3.36/1.00      | sK1 != X2
% 3.36/1.00      | sK0 != X1
% 3.36/1.00      | k1_xboole_0 = X2 ),
% 3.36/1.00      inference(resolution_lifted,[status(thm)],[c_22,c_33]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_645,plain,
% 3.36/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.36/1.00      | k1_relset_1(sK0,sK1,sK3) = sK0
% 3.36/1.00      | k1_xboole_0 = sK1 ),
% 3.36/1.00      inference(unflattening,[status(thm)],[c_644]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_32,negated_conjecture,
% 3.36/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.36/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_647,plain,
% 3.36/1.00      ( k1_relset_1(sK0,sK1,sK3) = sK0 | k1_xboole_0 = sK1 ),
% 3.36/1.00      inference(global_propositional_subsumption,[status(thm)],[c_645,c_32]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_1634,plain,
% 3.36/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.36/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_16,plain,
% 3.36/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.36/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.36/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_1640,plain,
% 3.36/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.36/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.36/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_2941,plain,
% 3.36/1.00      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 3.36/1.00      inference(superposition,[status(thm)],[c_1634,c_1640]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_2949,plain,
% 3.36/1.00      ( k1_relat_1(sK3) = sK0 | sK1 = k1_xboole_0 ),
% 3.36/1.00      inference(superposition,[status(thm)],[c_647,c_2941]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_10,plain,
% 3.36/1.00      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 3.36/1.00      | ~ v1_relat_1(X1)
% 3.36/1.00      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 3.36/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_1644,plain,
% 3.36/1.00      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 3.36/1.00      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 3.36/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.36/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_3591,plain,
% 3.36/1.00      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 3.36/1.00      | sK1 = k1_xboole_0
% 3.36/1.00      | r1_tarski(X0,sK0) != iProver_top
% 3.36/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.36/1.00      inference(superposition,[status(thm)],[c_2949,c_1644]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_37,plain,
% 3.36/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.36/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_12,plain,
% 3.36/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 3.36/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_1920,plain,
% 3.36/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.36/1.00      | v1_relat_1(sK3) ),
% 3.36/1.00      inference(instantiation,[status(thm)],[c_12]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_1921,plain,
% 3.36/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.36/1.00      | v1_relat_1(sK3) = iProver_top ),
% 3.36/1.00      inference(predicate_to_equality,[status(thm)],[c_1920]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_3839,plain,
% 3.36/1.00      ( r1_tarski(X0,sK0) != iProver_top
% 3.36/1.00      | sK1 = k1_xboole_0
% 3.36/1.00      | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
% 3.36/1.00      inference(global_propositional_subsumption,
% 3.36/1.00                [status(thm)],
% 3.36/1.00                [c_3591,c_37,c_1921]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_3840,plain,
% 3.36/1.00      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 3.36/1.00      | sK1 = k1_xboole_0
% 3.36/1.00      | r1_tarski(X0,sK0) != iProver_top ),
% 3.36/1.00      inference(renaming,[status(thm)],[c_3839]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_3848,plain,
% 3.36/1.00      ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2 | sK1 = k1_xboole_0 ),
% 3.36/1.00      inference(superposition,[status(thm)],[c_1635,c_3840]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_26,plain,
% 3.36/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.36/1.00      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.36/1.00      | ~ v1_funct_1(X0)
% 3.36/1.00      | ~ v1_relat_1(X0) ),
% 3.36/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_1636,plain,
% 3.36/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
% 3.36/1.00      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 3.36/1.00      | v1_funct_1(X0) != iProver_top
% 3.36/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.36/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_5352,plain,
% 3.36/1.00      ( sK1 = k1_xboole_0
% 3.36/1.00      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 3.36/1.00      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
% 3.36/1.00      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
% 3.36/1.00      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.36/1.00      inference(superposition,[status(thm)],[c_3848,c_1636]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_25,plain,
% 3.36/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.36/1.00      | ~ v1_funct_1(X0)
% 3.36/1.00      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 3.36/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_1637,plain,
% 3.36/1.00      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 3.36/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.36/1.00      | v1_funct_1(X2) != iProver_top ),
% 3.36/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_4601,plain,
% 3.36/1.00      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
% 3.36/1.00      | v1_funct_1(sK3) != iProver_top ),
% 3.36/1.00      inference(superposition,[status(thm)],[c_1634,c_1637]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_34,negated_conjecture,
% 3.36/1.00      ( v1_funct_1(sK3) ),
% 3.36/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_2005,plain,
% 3.36/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.36/1.00      | ~ v1_funct_1(sK3)
% 3.36/1.00      | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
% 3.36/1.00      inference(instantiation,[status(thm)],[c_25]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_2141,plain,
% 3.36/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.36/1.00      | ~ v1_funct_1(sK3)
% 3.36/1.00      | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 3.36/1.00      inference(instantiation,[status(thm)],[c_2005]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_4686,plain,
% 3.36/1.00      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 3.36/1.00      inference(global_propositional_subsumption,
% 3.36/1.00                [status(thm)],
% 3.36/1.00                [c_4601,c_34,c_32,c_2141]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_24,plain,
% 3.36/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.36/1.00      | ~ v1_funct_1(X0)
% 3.36/1.00      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
% 3.36/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_1638,plain,
% 3.36/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.36/1.00      | v1_funct_1(X0) != iProver_top
% 3.36/1.00      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
% 3.36/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_4482,plain,
% 3.36/1.00      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
% 3.36/1.00      | v1_funct_1(sK3) != iProver_top ),
% 3.36/1.00      inference(superposition,[status(thm)],[c_1634,c_1638]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_35,plain,
% 3.36/1.00      ( v1_funct_1(sK3) = iProver_top ),
% 3.36/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_1969,plain,
% 3.36/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.36/1.00      | v1_funct_1(k2_partfun1(X0,X1,sK3,X2))
% 3.36/1.00      | ~ v1_funct_1(sK3) ),
% 3.36/1.00      inference(instantiation,[status(thm)],[c_24]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_2133,plain,
% 3.36/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.36/1.00      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
% 3.36/1.00      | ~ v1_funct_1(sK3) ),
% 3.36/1.00      inference(instantiation,[status(thm)],[c_1969]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_2134,plain,
% 3.36/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.36/1.00      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
% 3.36/1.00      | v1_funct_1(sK3) != iProver_top ),
% 3.36/1.00      inference(predicate_to_equality,[status(thm)],[c_2133]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_4618,plain,
% 3.36/1.00      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
% 3.36/1.00      inference(global_propositional_subsumption,
% 3.36/1.00                [status(thm)],
% 3.36/1.00                [c_4482,c_35,c_37,c_2134]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_4695,plain,
% 3.36/1.00      ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 3.36/1.00      inference(demodulation,[status(thm)],[c_4686,c_4618]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_6318,plain,
% 3.36/1.00      ( sK1 = k1_xboole_0
% 3.36/1.00      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 3.36/1.00      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
% 3.36/1.00      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.36/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_5352,c_4695]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_27,plain,
% 3.36/1.00      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 3.36/1.00      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.36/1.00      | ~ v1_funct_1(X0)
% 3.36/1.00      | ~ v1_relat_1(X0) ),
% 3.36/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_29,negated_conjecture,
% 3.36/1.00      ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
% 3.36/1.00      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.36/1.00      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
% 3.36/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_655,plain,
% 3.36/1.00      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.36/1.00      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.36/1.00      | ~ v1_funct_1(X0)
% 3.36/1.00      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.36/1.00      | ~ v1_relat_1(X0)
% 3.36/1.00      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 3.36/1.00      | k1_relat_1(X0) != sK2
% 3.36/1.00      | sK1 != X1 ),
% 3.36/1.00      inference(resolution_lifted,[status(thm)],[c_27,c_29]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_656,plain,
% 3.36/1.00      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.36/1.00      | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
% 3.36/1.00      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.36/1.00      | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.36/1.00      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
% 3.36/1.00      inference(unflattening,[status(thm)],[c_655]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_13,plain,
% 3.36/1.00      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.36/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_6,plain,
% 3.36/1.00      ( ~ v5_relat_1(X0,X1) | r1_tarski(k2_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 3.36/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_370,plain,
% 3.36/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.36/1.00      | r1_tarski(k2_relat_1(X0),X2)
% 3.36/1.00      | ~ v1_relat_1(X0) ),
% 3.36/1.00      inference(resolution,[status(thm)],[c_13,c_6]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_374,plain,
% 3.36/1.00      ( r1_tarski(k2_relat_1(X0),X2)
% 3.36/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.36/1.00      inference(global_propositional_subsumption,[status(thm)],[c_370,c_12]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_375,plain,
% 3.36/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.36/1.00      | r1_tarski(k2_relat_1(X0),X2) ),
% 3.36/1.00      inference(renaming,[status(thm)],[c_374]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_668,plain,
% 3.36/1.00      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.36/1.00      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.36/1.00      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
% 3.36/1.00      inference(forward_subsumption_resolution,
% 3.36/1.00                [status(thm)],
% 3.36/1.00                [c_656,c_12,c_375]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_1622,plain,
% 3.36/1.00      ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 3.36/1.00      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.36/1.00      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.36/1.00      inference(predicate_to_equality,[status(thm)],[c_668]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_4691,plain,
% 3.36/1.00      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 3.36/1.00      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.36/1.00      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.36/1.00      inference(demodulation,[status(thm)],[c_4686,c_1622]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_4727,plain,
% 3.36/1.00      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 3.36/1.00      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.36/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_4691,c_4695]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_4815,plain,
% 3.36/1.00      ( sK1 = k1_xboole_0
% 3.36/1.00      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.36/1.00      inference(superposition,[status(thm)],[c_3848,c_4727]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_6329,plain,
% 3.36/1.00      ( sK1 = k1_xboole_0
% 3.36/1.00      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
% 3.36/1.00      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.36/1.00      inference(superposition,[status(thm)],[c_6318,c_4815]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_23,plain,
% 3.36/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.36/1.00      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.36/1.00      | ~ v1_funct_1(X0) ),
% 3.36/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_1639,plain,
% 3.36/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.36/1.00      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 3.36/1.00      | v1_funct_1(X0) != iProver_top ),
% 3.36/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_5259,plain,
% 3.36/1.00      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 3.36/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.36/1.00      | v1_funct_1(sK3) != iProver_top ),
% 3.36/1.00      inference(superposition,[status(thm)],[c_4686,c_1639]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_5956,plain,
% 3.36/1.00      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.36/1.00      inference(global_propositional_subsumption,
% 3.36/1.00                [status(thm)],
% 3.36/1.00                [c_5259,c_35,c_37]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_1642,plain,
% 3.36/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.36/1.00      | v1_relat_1(X0) = iProver_top ),
% 3.36/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_5968,plain,
% 3.36/1.00      ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 3.36/1.00      inference(superposition,[status(thm)],[c_5956,c_1642]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_1631,plain,
% 3.36/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.36/1.00      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 3.36/1.00      inference(predicate_to_equality,[status(thm)],[c_375]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_5964,plain,
% 3.36/1.00      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) = iProver_top ),
% 3.36/1.00      inference(superposition,[status(thm)],[c_5956,c_1631]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_7017,plain,
% 3.36/1.00      ( sK1 = k1_xboole_0 ),
% 3.36/1.00      inference(forward_subsumption_resolution,
% 3.36/1.00                [status(thm)],
% 3.36/1.00                [c_6329,c_5968,c_5964]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_673,plain,
% 3.36/1.00      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.36/1.00      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.36/1.00      | k2_partfun1(sK0,sK1,sK3,sK2) != sK3
% 3.36/1.00      | sK2 != sK0
% 3.36/1.00      | sK1 != sK1 ),
% 3.36/1.00      inference(resolution_lifted,[status(thm)],[c_29,c_33]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_869,plain,
% 3.36/1.00      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.36/1.00      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.36/1.00      | k2_partfun1(sK0,sK1,sK3,sK2) != sK3
% 3.36/1.00      | sK2 != sK0 ),
% 3.36/1.00      inference(equality_resolution_simp,[status(thm)],[c_673]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_1621,plain,
% 3.36/1.00      ( k2_partfun1(sK0,sK1,sK3,sK2) != sK3
% 3.36/1.00      | sK2 != sK0
% 3.36/1.00      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.36/1.00      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.36/1.00      inference(predicate_to_equality,[status(thm)],[c_869]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_4692,plain,
% 3.36/1.00      ( k7_relat_1(sK3,sK2) != sK3
% 3.36/1.00      | sK2 != sK0
% 3.36/1.00      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.36/1.00      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.36/1.00      inference(demodulation,[status(thm)],[c_4686,c_1621]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_4720,plain,
% 3.36/1.00      ( k7_relat_1(sK3,sK2) != sK3
% 3.36/1.00      | sK2 != sK0
% 3.36/1.00      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.36/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_4692,c_4695]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_7026,plain,
% 3.36/1.00      ( k7_relat_1(sK3,sK2) != sK3
% 3.36/1.00      | sK2 != sK0
% 3.36/1.00      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
% 3.36/1.00      inference(demodulation,[status(thm)],[c_7017,c_4720]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_30,negated_conjecture,
% 3.36/1.00      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 3.36/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_7037,plain,
% 3.36/1.00      ( sK0 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.36/1.00      inference(demodulation,[status(thm)],[c_7017,c_30]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_7038,plain,
% 3.36/1.00      ( sK0 = k1_xboole_0 ),
% 3.36/1.00      inference(equality_resolution_simp,[status(thm)],[c_7037]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_7061,plain,
% 3.36/1.00      ( k7_relat_1(sK3,sK2) != sK3
% 3.36/1.00      | sK2 != k1_xboole_0
% 3.36/1.00      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
% 3.36/1.00      inference(light_normalisation,[status(thm)],[c_7026,c_7038]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_7114,plain,
% 3.36/1.00      ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
% 3.36/1.00      inference(demodulation,[status(thm)],[c_7038,c_1635]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_4,plain,
% 3.36/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.36/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_1645,plain,
% 3.36/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.36/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_14,plain,
% 3.36/1.00      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.36/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_7,plain,
% 3.36/1.00      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 3.36/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_350,plain,
% 3.36/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.36/1.00      | ~ v1_relat_1(X0)
% 3.36/1.00      | k7_relat_1(X0,X1) = X0 ),
% 3.36/1.00      inference(resolution,[status(thm)],[c_14,c_7]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_354,plain,
% 3.36/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.36/1.00      | k7_relat_1(X0,X1) = X0 ),
% 3.36/1.00      inference(global_propositional_subsumption,
% 3.36/1.00                [status(thm)],
% 3.36/1.00                [c_350,c_14,c_12,c_7]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_1632,plain,
% 3.36/1.00      ( k7_relat_1(X0,X1) = X0
% 3.36/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 3.36/1.00      inference(predicate_to_equality,[status(thm)],[c_354]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_3074,plain,
% 3.36/1.00      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.36/1.00      inference(superposition,[status(thm)],[c_1645,c_1632]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_9,plain,
% 3.36/1.00      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.36/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_3590,plain,
% 3.36/1.00      ( k1_relat_1(k7_relat_1(k1_xboole_0,X0)) = X0
% 3.36/1.00      | r1_tarski(X0,k1_xboole_0) != iProver_top
% 3.36/1.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.36/1.00      inference(superposition,[status(thm)],[c_9,c_1644]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_1912,plain,
% 3.36/1.00      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.36/1.00      | v1_relat_1(k1_xboole_0) ),
% 3.36/1.00      inference(instantiation,[status(thm)],[c_12]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_1914,plain,
% 3.36/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.36/1.00      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.36/1.00      inference(predicate_to_equality,[status(thm)],[c_1912]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_1913,plain,
% 3.36/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.36/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_1916,plain,
% 3.36/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
% 3.36/1.00      inference(predicate_to_equality,[status(thm)],[c_1913]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_3613,plain,
% 3.36/1.00      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 3.36/1.00      | k1_relat_1(k7_relat_1(k1_xboole_0,X0)) = X0 ),
% 3.36/1.00      inference(global_propositional_subsumption,
% 3.36/1.00                [status(thm)],
% 3.36/1.00                [c_3590,c_1914,c_1916]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_3614,plain,
% 3.36/1.00      ( k1_relat_1(k7_relat_1(k1_xboole_0,X0)) = X0
% 3.36/1.00      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.36/1.00      inference(renaming,[status(thm)],[c_3613]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_4215,plain,
% 3.36/1.00      ( k1_relat_1(k1_xboole_0) = X0
% 3.36/1.00      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.36/1.00      inference(demodulation,[status(thm)],[c_3074,c_3614]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_4222,plain,
% 3.36/1.00      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.36/1.00      inference(demodulation,[status(thm)],[c_4215,c_9]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_7616,plain,
% 3.36/1.00      ( sK2 = k1_xboole_0 ),
% 3.36/1.00      inference(superposition,[status(thm)],[c_7114,c_4222]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_8077,plain,
% 3.36/1.00      ( k7_relat_1(sK3,sK2) != sK3
% 3.36/1.00      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
% 3.36/1.00      inference(global_propositional_subsumption,[status(thm)],[c_7061,c_7616]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_3075,plain,
% 3.36/1.00      ( k7_relat_1(sK3,sK0) = sK3 ),
% 3.36/1.00      inference(superposition,[status(thm)],[c_1634,c_1632]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_7112,plain,
% 3.36/1.00      ( k7_relat_1(sK3,k1_xboole_0) = sK3 ),
% 3.36/1.00      inference(demodulation,[status(thm)],[c_7038,c_3075]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_15,plain,
% 3.36/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.36/1.00      | ~ v1_xboole_0(X1)
% 3.36/1.00      | v1_xboole_0(X0) ),
% 3.36/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_1641,plain,
% 3.36/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.36/1.00      | v1_xboole_0(X1) != iProver_top
% 3.36/1.00      | v1_xboole_0(X0) = iProver_top ),
% 3.36/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_5966,plain,
% 3.36/1.00      ( v1_xboole_0(k7_relat_1(sK3,X0)) = iProver_top
% 3.36/1.00      | v1_xboole_0(sK0) != iProver_top ),
% 3.36/1.00      inference(superposition,[status(thm)],[c_5956,c_1641]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_1,plain,
% 3.36/1.00      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.36/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_1648,plain,
% 3.36/1.00      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.36/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_6748,plain,
% 3.36/1.00      ( k7_relat_1(sK3,X0) = k1_xboole_0 | v1_xboole_0(sK0) != iProver_top ),
% 3.36/1.00      inference(superposition,[status(thm)],[c_5966,c_1648]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_3,plain,
% 3.36/1.00      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X1 = X0 ),
% 3.36/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_106,plain,
% 3.36/1.00      ( ~ v1_xboole_0(k1_xboole_0) | k1_xboole_0 = k1_xboole_0 ),
% 3.36/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_0,plain,
% 3.36/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 3.36/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_1129,plain,
% 3.36/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.36/1.00      theory(equality) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_2166,plain,
% 3.36/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK0) | sK0 != X0 ),
% 3.36/1.00      inference(instantiation,[status(thm)],[c_1129]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_2168,plain,
% 3.36/1.00      ( v1_xboole_0(sK0) | ~ v1_xboole_0(k1_xboole_0) | sK0 != k1_xboole_0 ),
% 3.36/1.00      inference(instantiation,[status(thm)],[c_2166]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_1128,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_1956,plain,
% 3.36/1.00      ( sK0 != X0 | sK0 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 3.36/1.00      inference(instantiation,[status(thm)],[c_1128]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_2269,plain,
% 3.36/1.00      ( sK0 != sK0 | sK0 = k1_xboole_0 | k1_xboole_0 != sK0 ),
% 3.36/1.00      inference(instantiation,[status(thm)],[c_1956]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_1127,plain,( X0 = X0 ),theory(equality) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_2270,plain,
% 3.36/1.00      ( sK0 = sK0 ),
% 3.36/1.00      inference(instantiation,[status(thm)],[c_1127]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_2333,plain,
% 3.36/1.00      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 3.36/1.00      inference(instantiation,[status(thm)],[c_1128]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_2334,plain,
% 3.36/1.00      ( sK1 != k1_xboole_0 | k1_xboole_0 = sK1 | k1_xboole_0 != k1_xboole_0 ),
% 3.36/1.00      inference(instantiation,[status(thm)],[c_2333]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_6760,plain,
% 3.36/1.00      ( ~ v1_xboole_0(sK0) | k7_relat_1(sK3,X0) = k1_xboole_0 ),
% 3.36/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_6748]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_7679,plain,
% 3.36/1.00      ( k7_relat_1(sK3,X0) = k1_xboole_0 ),
% 3.36/1.00      inference(global_propositional_subsumption,
% 3.36/1.00                [status(thm)],
% 3.36/1.00                [c_6748,c_30,c_106,c_0,c_2168,c_2269,c_2270,c_2334,c_6760,
% 3.36/1.00                 c_7017]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_7920,plain,
% 3.36/1.00      ( sK3 = k1_xboole_0 ),
% 3.36/1.00      inference(demodulation,[status(thm)],[c_7112,c_7679]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_8081,plain,
% 3.36/1.00      ( k7_relat_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.36/1.00      | m1_subset_1(k7_relat_1(k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 3.36/1.00      inference(light_normalisation,[status(thm)],[c_8077,c_7616,c_7920]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_8082,plain,
% 3.36/1.00      ( k1_xboole_0 != k1_xboole_0
% 3.36/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 3.36/1.00      inference(demodulation,[status(thm)],[c_8081,c_3074]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_8083,plain,
% 3.36/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 3.36/1.00      inference(equality_resolution_simp,[status(thm)],[c_8082]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_8085,plain,
% 3.36/1.00      ( $false ),
% 3.36/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_8083,c_1645]) ).
% 3.36/1.00  
% 3.36/1.00  
% 3.36/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.36/1.00  
% 3.36/1.00  ------                               Statistics
% 3.36/1.00  
% 3.36/1.00  ------ General
% 3.36/1.00  
% 3.36/1.00  abstr_ref_over_cycles:                  0
% 3.36/1.00  abstr_ref_under_cycles:                 0
% 3.36/1.00  gc_basic_clause_elim:                   0
% 3.36/1.00  forced_gc_time:                         0
% 3.36/1.00  parsing_time:                           0.01
% 3.36/1.00  unif_index_cands_time:                  0.
% 3.36/1.00  unif_index_add_time:                    0.
% 3.36/1.00  orderings_time:                         0.
% 3.36/1.00  out_proof_time:                         0.012
% 3.36/1.00  total_time:                             0.272
% 3.36/1.00  num_of_symbols:                         51
% 3.36/1.00  num_of_terms:                           5242
% 3.36/1.00  
% 3.36/1.00  ------ Preprocessing
% 3.36/1.00  
% 3.36/1.00  num_of_splits:                          0
% 3.36/1.00  num_of_split_atoms:                     0
% 3.36/1.00  num_of_reused_defs:                     0
% 3.36/1.00  num_eq_ax_congr_red:                    15
% 3.36/1.00  num_of_sem_filtered_clauses:            1
% 3.36/1.00  num_of_subtypes:                        0
% 3.36/1.00  monotx_restored_types:                  0
% 3.36/1.00  sat_num_of_epr_types:                   0
% 3.36/1.00  sat_num_of_non_cyclic_types:            0
% 3.36/1.00  sat_guarded_non_collapsed_types:        0
% 3.36/1.00  num_pure_diseq_elim:                    0
% 3.36/1.00  simp_replaced_by:                       0
% 3.36/1.00  res_preprocessed:                       158
% 3.36/1.00  prep_upred:                             0
% 3.36/1.00  prep_unflattend:                        46
% 3.36/1.00  smt_new_axioms:                         0
% 3.36/1.00  pred_elim_cands:                        5
% 3.36/1.00  pred_elim:                              3
% 3.36/1.00  pred_elim_cl:                           1
% 3.36/1.00  pred_elim_cycles:                       6
% 3.36/1.00  merged_defs:                            0
% 3.36/1.00  merged_defs_ncl:                        0
% 3.36/1.00  bin_hyper_res:                          0
% 3.36/1.00  prep_cycles:                            4
% 3.36/1.00  pred_elim_time:                         0.015
% 3.36/1.00  splitting_time:                         0.
% 3.36/1.00  sem_filter_time:                        0.
% 3.36/1.00  monotx_time:                            0.
% 3.36/1.00  subtype_inf_time:                       0.
% 3.36/1.00  
% 3.36/1.00  ------ Problem properties
% 3.36/1.00  
% 3.36/1.00  clauses:                                33
% 3.36/1.00  conjectures:                            4
% 3.36/1.00  epr:                                    7
% 3.36/1.00  horn:                                   29
% 3.36/1.00  ground:                                 15
% 3.36/1.00  unary:                                  7
% 3.36/1.00  binary:                                 8
% 3.36/1.00  lits:                                   90
% 3.36/1.00  lits_eq:                                33
% 3.36/1.00  fd_pure:                                0
% 3.36/1.00  fd_pseudo:                              0
% 3.36/1.00  fd_cond:                                3
% 3.36/1.00  fd_pseudo_cond:                         1
% 3.36/1.00  ac_symbols:                             0
% 3.36/1.00  
% 3.36/1.00  ------ Propositional Solver
% 3.36/1.00  
% 3.36/1.00  prop_solver_calls:                      27
% 3.36/1.00  prop_fast_solver_calls:                 1272
% 3.36/1.00  smt_solver_calls:                       0
% 3.36/1.00  smt_fast_solver_calls:                  0
% 3.36/1.00  prop_num_of_clauses:                    2935
% 3.36/1.00  prop_preprocess_simplified:             9042
% 3.36/1.00  prop_fo_subsumed:                       34
% 3.36/1.00  prop_solver_time:                       0.
% 3.36/1.00  smt_solver_time:                        0.
% 3.36/1.00  smt_fast_solver_time:                   0.
% 3.36/1.00  prop_fast_solver_time:                  0.
% 3.36/1.00  prop_unsat_core_time:                   0.
% 3.36/1.00  
% 3.36/1.00  ------ QBF
% 3.36/1.00  
% 3.36/1.00  qbf_q_res:                              0
% 3.36/1.00  qbf_num_tautologies:                    0
% 3.36/1.00  qbf_prep_cycles:                        0
% 3.36/1.00  
% 3.36/1.00  ------ BMC1
% 3.36/1.00  
% 3.36/1.00  bmc1_current_bound:                     -1
% 3.36/1.00  bmc1_last_solved_bound:                 -1
% 3.36/1.00  bmc1_unsat_core_size:                   -1
% 3.36/1.00  bmc1_unsat_core_parents_size:           -1
% 3.36/1.00  bmc1_merge_next_fun:                    0
% 3.36/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.36/1.00  
% 3.36/1.00  ------ Instantiation
% 3.36/1.00  
% 3.36/1.00  inst_num_of_clauses:                    848
% 3.36/1.00  inst_num_in_passive:                    439
% 3.36/1.00  inst_num_in_active:                     364
% 3.36/1.00  inst_num_in_unprocessed:                45
% 3.36/1.00  inst_num_of_loops:                      450
% 3.36/1.00  inst_num_of_learning_restarts:          0
% 3.36/1.00  inst_num_moves_active_passive:          85
% 3.36/1.00  inst_lit_activity:                      0
% 3.36/1.00  inst_lit_activity_moves:                0
% 3.36/1.00  inst_num_tautologies:                   0
% 3.36/1.00  inst_num_prop_implied:                  0
% 3.36/1.00  inst_num_existing_simplified:           0
% 3.36/1.00  inst_num_eq_res_simplified:             0
% 3.36/1.00  inst_num_child_elim:                    0
% 3.36/1.00  inst_num_of_dismatching_blockings:      254
% 3.36/1.00  inst_num_of_non_proper_insts:           684
% 3.36/1.00  inst_num_of_duplicates:                 0
% 3.36/1.00  inst_inst_num_from_inst_to_res:         0
% 3.36/1.00  inst_dismatching_checking_time:         0.
% 3.36/1.00  
% 3.36/1.00  ------ Resolution
% 3.36/1.00  
% 3.36/1.00  res_num_of_clauses:                     0
% 3.36/1.00  res_num_in_passive:                     0
% 3.36/1.00  res_num_in_active:                      0
% 3.36/1.00  res_num_of_loops:                       162
% 3.36/1.00  res_forward_subset_subsumed:            29
% 3.36/1.00  res_backward_subset_subsumed:           0
% 3.36/1.00  res_forward_subsumed:                   0
% 3.36/1.00  res_backward_subsumed:                  0
% 3.36/1.00  res_forward_subsumption_resolution:     6
% 3.36/1.00  res_backward_subsumption_resolution:    0
% 3.36/1.00  res_clause_to_clause_subsumption:       284
% 3.36/1.00  res_orphan_elimination:                 0
% 3.36/1.00  res_tautology_del:                      55
% 3.36/1.00  res_num_eq_res_simplified:              1
% 3.36/1.00  res_num_sel_changes:                    0
% 3.36/1.00  res_moves_from_active_to_pass:          0
% 3.36/1.00  
% 3.36/1.00  ------ Superposition
% 3.36/1.00  
% 3.36/1.00  sup_time_total:                         0.
% 3.36/1.00  sup_time_generating:                    0.
% 3.36/1.00  sup_time_sim_full:                      0.
% 3.36/1.00  sup_time_sim_immed:                     0.
% 3.36/1.00  
% 3.36/1.00  sup_num_of_clauses:                     86
% 3.36/1.00  sup_num_in_active:                      37
% 3.36/1.00  sup_num_in_passive:                     49
% 3.36/1.00  sup_num_of_loops:                       89
% 3.36/1.00  sup_fw_superposition:                   59
% 3.36/1.00  sup_bw_superposition:                   74
% 3.36/1.00  sup_immediate_simplified:               49
% 3.36/1.00  sup_given_eliminated:                   1
% 3.36/1.00  comparisons_done:                       0
% 3.36/1.00  comparisons_avoided:                    28
% 3.36/1.00  
% 3.36/1.00  ------ Simplifications
% 3.36/1.00  
% 3.36/1.00  
% 3.36/1.00  sim_fw_subset_subsumed:                 13
% 3.36/1.00  sim_bw_subset_subsumed:                 9
% 3.36/1.00  sim_fw_subsumed:                        11
% 3.36/1.00  sim_bw_subsumed:                        0
% 3.36/1.00  sim_fw_subsumption_res:                 10
% 3.36/1.00  sim_bw_subsumption_res:                 0
% 3.36/1.00  sim_tautology_del:                      10
% 3.36/1.00  sim_eq_tautology_del:                   11
% 3.36/1.00  sim_eq_res_simp:                        4
% 3.36/1.00  sim_fw_demodulated:                     11
% 3.36/1.00  sim_bw_demodulated:                     48
% 3.36/1.00  sim_light_normalised:                   38
% 3.36/1.00  sim_joinable_taut:                      0
% 3.36/1.00  sim_joinable_simp:                      0
% 3.36/1.00  sim_ac_normalised:                      0
% 3.36/1.00  sim_smt_subsumption:                    0
% 3.36/1.00  
%------------------------------------------------------------------------------
