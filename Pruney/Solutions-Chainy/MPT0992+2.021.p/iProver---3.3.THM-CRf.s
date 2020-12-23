%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:50 EST 2020

% Result     : Theorem 3.13s
% Output     : CNFRefutation 3.13s
% Verified   : 
% Statistics : Number of formulae       :  192 (3793 expanded)
%              Number of clauses        :  122 (1260 expanded)
%              Number of leaves         :   21 ( 714 expanded)
%              Depth                    :   26
%              Number of atoms          :  556 (20853 expanded)
%              Number of equality atoms :  265 (5509 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,conjecture,(
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

fof(f22,negated_conjecture,(
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
    inference(negated_conjecture,[],[f21])).

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
    inference(ennf_transformation,[],[f22])).

fof(f47,plain,(
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
    inference(flattening,[],[f46])).

fof(f52,plain,
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

fof(f53,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f47,f52])).

fof(f88,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f53])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f42])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f86,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f91,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f53])).

fof(f87,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f90,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f53])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f48])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f93,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f56])).

fof(f58,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f89,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f53])).

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
    inference(ennf_transformation,[],[f17])).

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
    inference(flattening,[],[f38])).

fof(f51,plain,(
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
    inference(nnf_transformation,[],[f39])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f44])).

fof(f85,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f84,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

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

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f9,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f63,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f55,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1464,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1467,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_5257,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1464,c_1467])).

cnf(c_37,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1867,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_2030,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_1867])).

cnf(c_5386,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5257,c_37,c_35,c_2030])).

cnf(c_32,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_36,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_611,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != sK3
    | sK2 != sK0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_36])).

cnf(c_716,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != sK3
    | sK2 != sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_611])).

cnf(c_1452,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != sK3
    | sK2 != sK0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_716])).

cnf(c_5392,plain,
    ( k7_relat_1(sK3,sK2) != sK3
    | sK2 != sK0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5386,c_1452])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1468,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_4460,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1464,c_1468])).

cnf(c_38,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_40,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_1847,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(k2_partfun1(X0,X1,sK3,X2))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_2025,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1847])).

cnf(c_2026,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2025])).

cnf(c_4476,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4460,c_38,c_40,c_2026])).

cnf(c_5395,plain,
    ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5386,c_4476])).

cnf(c_5420,plain,
    ( k7_relat_1(sK3,sK2) != sK3
    | sK2 != sK0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5392,c_5395])).

cnf(c_33,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_115,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_119,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_900,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1824,plain,
    ( sK2 != X0
    | sK2 = sK0
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_900])).

cnf(c_1825,plain,
    ( sK2 = sK0
    | sK2 != k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1824])).

cnf(c_1823,plain,
    ( sK0 != X0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_900])).

cnf(c_2175,plain,
    ( sK0 != sK0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1823])).

cnf(c_899,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2176,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_899])).

cnf(c_2760,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_900])).

cnf(c_2761,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2760])).

cnf(c_34,negated_conjecture,
    ( r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1465,plain,
    ( r1_tarski(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_582,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X0
    | sK1 != X2
    | sK0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_36])).

cnf(c_583,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_582])).

cnf(c_585,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_583,c_35])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1470,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2769,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1464,c_1470])).

cnf(c_2805,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_585,c_2769])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1476,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4359,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2805,c_1476])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1785,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1786,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1785])).

cnf(c_4595,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | sK1 = k1_xboole_0
    | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4359,c_40,c_1786])).

cnf(c_4596,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4595])).

cnf(c_4605,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1465,c_4596])).

cnf(c_29,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1466,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_4988,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4605,c_1466])).

cnf(c_5909,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4988,c_5395])).

cnf(c_30,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_593,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_relat_1(X0)
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_relat_1(X0) != sK2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_32])).

cnf(c_594,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
    inference(unflattening,[status(thm)],[c_593])).

cnf(c_17,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_8,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_381,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_17,c_8])).

cnf(c_385,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_381,c_16])).

cnf(c_386,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_385])).

cnf(c_606,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_594,c_16,c_386])).

cnf(c_1453,plain,
    ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_606])).

cnf(c_5391,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5386,c_1453])).

cnf(c_5427,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5391,c_5395])).

cnf(c_6741,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4605,c_5427])).

cnf(c_6746,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5909,c_6741])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1469,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_5448,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5386,c_1469])).

cnf(c_5647,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5448,c_38,c_40])).

cnf(c_1472,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_5660,plain,
    ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5647,c_1472])).

cnf(c_1462,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_386])).

cnf(c_5658,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_5647,c_1462])).

cnf(c_7514,plain,
    ( sK1 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6746,c_5660,c_5658])).

cnf(c_7532,plain,
    ( sK0 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7514,c_33])).

cnf(c_7533,plain,
    ( sK0 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_7532])).

cnf(c_7596,plain,
    ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7533,c_1465])).

cnf(c_6,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1478,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3868,plain,
    ( r1_tarski(k2_relat_1(k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1478,c_1462])).

cnf(c_10,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_3873,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3868,c_10])).

cnf(c_1481,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4250,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3873,c_1481])).

cnf(c_7755,plain,
    ( sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7596,c_4250])).

cnf(c_9563,plain,
    ( k7_relat_1(sK3,sK2) != sK3
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5420,c_33,c_115,c_119,c_1825,c_2175,c_2176,c_2761,c_7514,c_7755])).

cnf(c_2371,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1478,c_1472])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1477,plain,
    ( k7_relat_1(X0,k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2917,plain,
    ( k7_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2371,c_1477])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1471,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3418,plain,
    ( v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1464,c_1471])).

cnf(c_7593,plain,
    ( v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7533,c_3418])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_122,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_901,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2055,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK0)
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_901])).

cnf(c_2056,plain,
    ( sK0 != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2055])).

cnf(c_2058,plain,
    ( sK0 != k1_xboole_0
    | v1_xboole_0(sK0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2056])).

cnf(c_2084,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_2906,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_xboole_0(sK3)
    | ~ v1_xboole_0(sK0) ),
    inference(instantiation,[status(thm)],[c_2084])).

cnf(c_2907,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2906])).

cnf(c_9135,plain,
    ( v1_xboole_0(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7593,c_40,c_33,c_115,c_119,c_122,c_2058,c_2175,c_2176,c_2761,c_2907,c_7514])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1482,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_9140,plain,
    ( sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9135,c_1482])).

cnf(c_9567,plain,
    ( k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9563,c_2917,c_7514,c_7755,c_9140])).

cnf(c_9568,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_9567])).

cnf(c_9570,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_9568,c_1478])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 16:54:06 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running in FOF mode
% 3.13/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.13/1.01  
% 3.13/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.13/1.01  
% 3.13/1.01  ------  iProver source info
% 3.13/1.01  
% 3.13/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.13/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.13/1.01  git: non_committed_changes: false
% 3.13/1.01  git: last_make_outside_of_git: false
% 3.13/1.01  
% 3.13/1.01  ------ 
% 3.13/1.01  
% 3.13/1.01  ------ Input Options
% 3.13/1.01  
% 3.13/1.01  --out_options                           all
% 3.13/1.01  --tptp_safe_out                         true
% 3.13/1.01  --problem_path                          ""
% 3.13/1.01  --include_path                          ""
% 3.13/1.01  --clausifier                            res/vclausify_rel
% 3.13/1.01  --clausifier_options                    --mode clausify
% 3.13/1.01  --stdin                                 false
% 3.13/1.01  --stats_out                             all
% 3.13/1.01  
% 3.13/1.01  ------ General Options
% 3.13/1.01  
% 3.13/1.01  --fof                                   false
% 3.13/1.01  --time_out_real                         305.
% 3.13/1.01  --time_out_virtual                      -1.
% 3.13/1.01  --symbol_type_check                     false
% 3.13/1.01  --clausify_out                          false
% 3.13/1.01  --sig_cnt_out                           false
% 3.13/1.01  --trig_cnt_out                          false
% 3.13/1.01  --trig_cnt_out_tolerance                1.
% 3.13/1.01  --trig_cnt_out_sk_spl                   false
% 3.13/1.01  --abstr_cl_out                          false
% 3.13/1.01  
% 3.13/1.01  ------ Global Options
% 3.13/1.01  
% 3.13/1.01  --schedule                              default
% 3.13/1.01  --add_important_lit                     false
% 3.13/1.01  --prop_solver_per_cl                    1000
% 3.13/1.01  --min_unsat_core                        false
% 3.13/1.01  --soft_assumptions                      false
% 3.13/1.01  --soft_lemma_size                       3
% 3.13/1.01  --prop_impl_unit_size                   0
% 3.13/1.01  --prop_impl_unit                        []
% 3.13/1.01  --share_sel_clauses                     true
% 3.13/1.01  --reset_solvers                         false
% 3.13/1.01  --bc_imp_inh                            [conj_cone]
% 3.13/1.01  --conj_cone_tolerance                   3.
% 3.13/1.01  --extra_neg_conj                        none
% 3.13/1.01  --large_theory_mode                     true
% 3.13/1.01  --prolific_symb_bound                   200
% 3.13/1.01  --lt_threshold                          2000
% 3.13/1.01  --clause_weak_htbl                      true
% 3.13/1.01  --gc_record_bc_elim                     false
% 3.13/1.01  
% 3.13/1.01  ------ Preprocessing Options
% 3.13/1.01  
% 3.13/1.01  --preprocessing_flag                    true
% 3.13/1.01  --time_out_prep_mult                    0.1
% 3.13/1.01  --splitting_mode                        input
% 3.13/1.01  --splitting_grd                         true
% 3.13/1.01  --splitting_cvd                         false
% 3.13/1.01  --splitting_cvd_svl                     false
% 3.13/1.01  --splitting_nvd                         32
% 3.13/1.01  --sub_typing                            true
% 3.13/1.01  --prep_gs_sim                           true
% 3.13/1.01  --prep_unflatten                        true
% 3.13/1.01  --prep_res_sim                          true
% 3.13/1.01  --prep_upred                            true
% 3.13/1.01  --prep_sem_filter                       exhaustive
% 3.13/1.01  --prep_sem_filter_out                   false
% 3.13/1.01  --pred_elim                             true
% 3.13/1.01  --res_sim_input                         true
% 3.13/1.01  --eq_ax_congr_red                       true
% 3.13/1.01  --pure_diseq_elim                       true
% 3.13/1.01  --brand_transform                       false
% 3.13/1.01  --non_eq_to_eq                          false
% 3.13/1.01  --prep_def_merge                        true
% 3.13/1.01  --prep_def_merge_prop_impl              false
% 3.13/1.01  --prep_def_merge_mbd                    true
% 3.13/1.01  --prep_def_merge_tr_red                 false
% 3.13/1.01  --prep_def_merge_tr_cl                  false
% 3.13/1.01  --smt_preprocessing                     true
% 3.13/1.01  --smt_ac_axioms                         fast
% 3.13/1.01  --preprocessed_out                      false
% 3.13/1.01  --preprocessed_stats                    false
% 3.13/1.01  
% 3.13/1.01  ------ Abstraction refinement Options
% 3.13/1.01  
% 3.13/1.01  --abstr_ref                             []
% 3.13/1.01  --abstr_ref_prep                        false
% 3.13/1.01  --abstr_ref_until_sat                   false
% 3.13/1.01  --abstr_ref_sig_restrict                funpre
% 3.13/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.13/1.01  --abstr_ref_under                       []
% 3.13/1.01  
% 3.13/1.01  ------ SAT Options
% 3.13/1.01  
% 3.13/1.01  --sat_mode                              false
% 3.13/1.01  --sat_fm_restart_options                ""
% 3.13/1.01  --sat_gr_def                            false
% 3.13/1.01  --sat_epr_types                         true
% 3.13/1.01  --sat_non_cyclic_types                  false
% 3.13/1.01  --sat_finite_models                     false
% 3.13/1.01  --sat_fm_lemmas                         false
% 3.13/1.01  --sat_fm_prep                           false
% 3.13/1.01  --sat_fm_uc_incr                        true
% 3.13/1.01  --sat_out_model                         small
% 3.13/1.01  --sat_out_clauses                       false
% 3.13/1.01  
% 3.13/1.01  ------ QBF Options
% 3.13/1.01  
% 3.13/1.01  --qbf_mode                              false
% 3.13/1.01  --qbf_elim_univ                         false
% 3.13/1.01  --qbf_dom_inst                          none
% 3.13/1.01  --qbf_dom_pre_inst                      false
% 3.13/1.01  --qbf_sk_in                             false
% 3.13/1.01  --qbf_pred_elim                         true
% 3.13/1.01  --qbf_split                             512
% 3.13/1.01  
% 3.13/1.01  ------ BMC1 Options
% 3.13/1.01  
% 3.13/1.01  --bmc1_incremental                      false
% 3.13/1.01  --bmc1_axioms                           reachable_all
% 3.13/1.01  --bmc1_min_bound                        0
% 3.13/1.01  --bmc1_max_bound                        -1
% 3.13/1.01  --bmc1_max_bound_default                -1
% 3.13/1.01  --bmc1_symbol_reachability              true
% 3.13/1.01  --bmc1_property_lemmas                  false
% 3.13/1.01  --bmc1_k_induction                      false
% 3.13/1.01  --bmc1_non_equiv_states                 false
% 3.13/1.01  --bmc1_deadlock                         false
% 3.13/1.01  --bmc1_ucm                              false
% 3.13/1.01  --bmc1_add_unsat_core                   none
% 3.13/1.01  --bmc1_unsat_core_children              false
% 3.13/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.13/1.01  --bmc1_out_stat                         full
% 3.13/1.01  --bmc1_ground_init                      false
% 3.13/1.01  --bmc1_pre_inst_next_state              false
% 3.13/1.01  --bmc1_pre_inst_state                   false
% 3.13/1.01  --bmc1_pre_inst_reach_state             false
% 3.13/1.01  --bmc1_out_unsat_core                   false
% 3.13/1.01  --bmc1_aig_witness_out                  false
% 3.13/1.01  --bmc1_verbose                          false
% 3.13/1.01  --bmc1_dump_clauses_tptp                false
% 3.13/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.13/1.01  --bmc1_dump_file                        -
% 3.13/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.13/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.13/1.01  --bmc1_ucm_extend_mode                  1
% 3.13/1.01  --bmc1_ucm_init_mode                    2
% 3.13/1.01  --bmc1_ucm_cone_mode                    none
% 3.13/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.13/1.01  --bmc1_ucm_relax_model                  4
% 3.13/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.13/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.13/1.01  --bmc1_ucm_layered_model                none
% 3.13/1.01  --bmc1_ucm_max_lemma_size               10
% 3.13/1.01  
% 3.13/1.01  ------ AIG Options
% 3.13/1.01  
% 3.13/1.01  --aig_mode                              false
% 3.13/1.01  
% 3.13/1.01  ------ Instantiation Options
% 3.13/1.01  
% 3.13/1.01  --instantiation_flag                    true
% 3.13/1.01  --inst_sos_flag                         false
% 3.13/1.01  --inst_sos_phase                        true
% 3.13/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.13/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.13/1.01  --inst_lit_sel_side                     num_symb
% 3.13/1.01  --inst_solver_per_active                1400
% 3.13/1.01  --inst_solver_calls_frac                1.
% 3.13/1.01  --inst_passive_queue_type               priority_queues
% 3.13/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.13/1.01  --inst_passive_queues_freq              [25;2]
% 3.13/1.01  --inst_dismatching                      true
% 3.13/1.01  --inst_eager_unprocessed_to_passive     true
% 3.13/1.01  --inst_prop_sim_given                   true
% 3.13/1.01  --inst_prop_sim_new                     false
% 3.13/1.01  --inst_subs_new                         false
% 3.13/1.01  --inst_eq_res_simp                      false
% 3.13/1.01  --inst_subs_given                       false
% 3.13/1.01  --inst_orphan_elimination               true
% 3.13/1.01  --inst_learning_loop_flag               true
% 3.13/1.01  --inst_learning_start                   3000
% 3.13/1.01  --inst_learning_factor                  2
% 3.13/1.01  --inst_start_prop_sim_after_learn       3
% 3.13/1.01  --inst_sel_renew                        solver
% 3.13/1.01  --inst_lit_activity_flag                true
% 3.13/1.01  --inst_restr_to_given                   false
% 3.13/1.01  --inst_activity_threshold               500
% 3.13/1.01  --inst_out_proof                        true
% 3.13/1.01  
% 3.13/1.01  ------ Resolution Options
% 3.13/1.01  
% 3.13/1.01  --resolution_flag                       true
% 3.13/1.01  --res_lit_sel                           adaptive
% 3.13/1.01  --res_lit_sel_side                      none
% 3.13/1.01  --res_ordering                          kbo
% 3.13/1.01  --res_to_prop_solver                    active
% 3.13/1.01  --res_prop_simpl_new                    false
% 3.13/1.01  --res_prop_simpl_given                  true
% 3.13/1.01  --res_passive_queue_type                priority_queues
% 3.13/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.13/1.01  --res_passive_queues_freq               [15;5]
% 3.13/1.01  --res_forward_subs                      full
% 3.13/1.01  --res_backward_subs                     full
% 3.13/1.01  --res_forward_subs_resolution           true
% 3.13/1.01  --res_backward_subs_resolution          true
% 3.13/1.01  --res_orphan_elimination                true
% 3.13/1.01  --res_time_limit                        2.
% 3.13/1.01  --res_out_proof                         true
% 3.13/1.01  
% 3.13/1.01  ------ Superposition Options
% 3.13/1.01  
% 3.13/1.01  --superposition_flag                    true
% 3.13/1.01  --sup_passive_queue_type                priority_queues
% 3.13/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.13/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.13/1.01  --demod_completeness_check              fast
% 3.13/1.01  --demod_use_ground                      true
% 3.13/1.01  --sup_to_prop_solver                    passive
% 3.13/1.01  --sup_prop_simpl_new                    true
% 3.13/1.01  --sup_prop_simpl_given                  true
% 3.13/1.01  --sup_fun_splitting                     false
% 3.13/1.01  --sup_smt_interval                      50000
% 3.13/1.01  
% 3.13/1.01  ------ Superposition Simplification Setup
% 3.13/1.01  
% 3.13/1.01  --sup_indices_passive                   []
% 3.13/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.13/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.13/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.13/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.13/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.13/1.01  --sup_full_bw                           [BwDemod]
% 3.13/1.01  --sup_immed_triv                        [TrivRules]
% 3.13/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.13/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.13/1.01  --sup_immed_bw_main                     []
% 3.13/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.13/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.13/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.13/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.13/1.01  
% 3.13/1.01  ------ Combination Options
% 3.13/1.01  
% 3.13/1.01  --comb_res_mult                         3
% 3.13/1.01  --comb_sup_mult                         2
% 3.13/1.01  --comb_inst_mult                        10
% 3.13/1.01  
% 3.13/1.01  ------ Debug Options
% 3.13/1.01  
% 3.13/1.01  --dbg_backtrace                         false
% 3.13/1.01  --dbg_dump_prop_clauses                 false
% 3.13/1.01  --dbg_dump_prop_clauses_file            -
% 3.13/1.01  --dbg_out_stat                          false
% 3.13/1.01  ------ Parsing...
% 3.13/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.13/1.01  
% 3.13/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.13/1.01  
% 3.13/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.13/1.01  
% 3.13/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.13/1.01  ------ Proving...
% 3.13/1.01  ------ Problem Properties 
% 3.13/1.01  
% 3.13/1.01  
% 3.13/1.01  clauses                                 36
% 3.13/1.01  conjectures                             4
% 3.13/1.01  EPR                                     8
% 3.13/1.01  Horn                                    32
% 3.13/1.01  unary                                   8
% 3.13/1.01  binary                                  8
% 3.13/1.01  lits                                    97
% 3.13/1.01  lits eq                                 34
% 3.13/1.01  fd_pure                                 0
% 3.13/1.01  fd_pseudo                               0
% 3.13/1.01  fd_cond                                 3
% 3.13/1.01  fd_pseudo_cond                          2
% 3.13/1.01  AC symbols                              0
% 3.13/1.01  
% 3.13/1.01  ------ Schedule dynamic 5 is on 
% 3.13/1.01  
% 3.13/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.13/1.01  
% 3.13/1.01  
% 3.13/1.01  ------ 
% 3.13/1.01  Current options:
% 3.13/1.01  ------ 
% 3.13/1.01  
% 3.13/1.01  ------ Input Options
% 3.13/1.01  
% 3.13/1.01  --out_options                           all
% 3.13/1.01  --tptp_safe_out                         true
% 3.13/1.01  --problem_path                          ""
% 3.13/1.01  --include_path                          ""
% 3.13/1.01  --clausifier                            res/vclausify_rel
% 3.13/1.01  --clausifier_options                    --mode clausify
% 3.13/1.01  --stdin                                 false
% 3.13/1.01  --stats_out                             all
% 3.13/1.01  
% 3.13/1.01  ------ General Options
% 3.13/1.01  
% 3.13/1.01  --fof                                   false
% 3.13/1.01  --time_out_real                         305.
% 3.13/1.01  --time_out_virtual                      -1.
% 3.13/1.01  --symbol_type_check                     false
% 3.13/1.01  --clausify_out                          false
% 3.13/1.01  --sig_cnt_out                           false
% 3.13/1.01  --trig_cnt_out                          false
% 3.13/1.01  --trig_cnt_out_tolerance                1.
% 3.13/1.01  --trig_cnt_out_sk_spl                   false
% 3.13/1.01  --abstr_cl_out                          false
% 3.13/1.01  
% 3.13/1.01  ------ Global Options
% 3.13/1.01  
% 3.13/1.01  --schedule                              default
% 3.13/1.01  --add_important_lit                     false
% 3.13/1.01  --prop_solver_per_cl                    1000
% 3.13/1.01  --min_unsat_core                        false
% 3.13/1.01  --soft_assumptions                      false
% 3.13/1.01  --soft_lemma_size                       3
% 3.13/1.01  --prop_impl_unit_size                   0
% 3.13/1.01  --prop_impl_unit                        []
% 3.13/1.01  --share_sel_clauses                     true
% 3.13/1.01  --reset_solvers                         false
% 3.13/1.01  --bc_imp_inh                            [conj_cone]
% 3.13/1.01  --conj_cone_tolerance                   3.
% 3.13/1.01  --extra_neg_conj                        none
% 3.13/1.01  --large_theory_mode                     true
% 3.13/1.01  --prolific_symb_bound                   200
% 3.13/1.01  --lt_threshold                          2000
% 3.13/1.01  --clause_weak_htbl                      true
% 3.13/1.01  --gc_record_bc_elim                     false
% 3.13/1.01  
% 3.13/1.01  ------ Preprocessing Options
% 3.13/1.01  
% 3.13/1.01  --preprocessing_flag                    true
% 3.13/1.01  --time_out_prep_mult                    0.1
% 3.13/1.01  --splitting_mode                        input
% 3.13/1.01  --splitting_grd                         true
% 3.13/1.01  --splitting_cvd                         false
% 3.13/1.01  --splitting_cvd_svl                     false
% 3.13/1.01  --splitting_nvd                         32
% 3.13/1.01  --sub_typing                            true
% 3.13/1.01  --prep_gs_sim                           true
% 3.13/1.01  --prep_unflatten                        true
% 3.13/1.01  --prep_res_sim                          true
% 3.13/1.01  --prep_upred                            true
% 3.13/1.01  --prep_sem_filter                       exhaustive
% 3.13/1.01  --prep_sem_filter_out                   false
% 3.13/1.01  --pred_elim                             true
% 3.13/1.01  --res_sim_input                         true
% 3.13/1.01  --eq_ax_congr_red                       true
% 3.13/1.01  --pure_diseq_elim                       true
% 3.13/1.01  --brand_transform                       false
% 3.13/1.01  --non_eq_to_eq                          false
% 3.13/1.01  --prep_def_merge                        true
% 3.13/1.01  --prep_def_merge_prop_impl              false
% 3.13/1.01  --prep_def_merge_mbd                    true
% 3.13/1.01  --prep_def_merge_tr_red                 false
% 3.13/1.01  --prep_def_merge_tr_cl                  false
% 3.13/1.01  --smt_preprocessing                     true
% 3.13/1.01  --smt_ac_axioms                         fast
% 3.13/1.01  --preprocessed_out                      false
% 3.13/1.01  --preprocessed_stats                    false
% 3.13/1.01  
% 3.13/1.01  ------ Abstraction refinement Options
% 3.13/1.01  
% 3.13/1.01  --abstr_ref                             []
% 3.13/1.01  --abstr_ref_prep                        false
% 3.13/1.01  --abstr_ref_until_sat                   false
% 3.13/1.01  --abstr_ref_sig_restrict                funpre
% 3.13/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.13/1.01  --abstr_ref_under                       []
% 3.13/1.01  
% 3.13/1.01  ------ SAT Options
% 3.13/1.01  
% 3.13/1.01  --sat_mode                              false
% 3.13/1.01  --sat_fm_restart_options                ""
% 3.13/1.01  --sat_gr_def                            false
% 3.13/1.01  --sat_epr_types                         true
% 3.13/1.01  --sat_non_cyclic_types                  false
% 3.13/1.01  --sat_finite_models                     false
% 3.13/1.01  --sat_fm_lemmas                         false
% 3.13/1.01  --sat_fm_prep                           false
% 3.13/1.01  --sat_fm_uc_incr                        true
% 3.13/1.01  --sat_out_model                         small
% 3.13/1.01  --sat_out_clauses                       false
% 3.13/1.01  
% 3.13/1.01  ------ QBF Options
% 3.13/1.01  
% 3.13/1.01  --qbf_mode                              false
% 3.13/1.01  --qbf_elim_univ                         false
% 3.13/1.01  --qbf_dom_inst                          none
% 3.13/1.01  --qbf_dom_pre_inst                      false
% 3.13/1.01  --qbf_sk_in                             false
% 3.13/1.01  --qbf_pred_elim                         true
% 3.13/1.01  --qbf_split                             512
% 3.13/1.01  
% 3.13/1.01  ------ BMC1 Options
% 3.13/1.01  
% 3.13/1.01  --bmc1_incremental                      false
% 3.13/1.01  --bmc1_axioms                           reachable_all
% 3.13/1.01  --bmc1_min_bound                        0
% 3.13/1.01  --bmc1_max_bound                        -1
% 3.13/1.01  --bmc1_max_bound_default                -1
% 3.13/1.01  --bmc1_symbol_reachability              true
% 3.13/1.01  --bmc1_property_lemmas                  false
% 3.13/1.01  --bmc1_k_induction                      false
% 3.13/1.01  --bmc1_non_equiv_states                 false
% 3.13/1.01  --bmc1_deadlock                         false
% 3.13/1.01  --bmc1_ucm                              false
% 3.13/1.01  --bmc1_add_unsat_core                   none
% 3.13/1.01  --bmc1_unsat_core_children              false
% 3.13/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.13/1.01  --bmc1_out_stat                         full
% 3.13/1.01  --bmc1_ground_init                      false
% 3.13/1.01  --bmc1_pre_inst_next_state              false
% 3.13/1.01  --bmc1_pre_inst_state                   false
% 3.13/1.01  --bmc1_pre_inst_reach_state             false
% 3.13/1.01  --bmc1_out_unsat_core                   false
% 3.13/1.01  --bmc1_aig_witness_out                  false
% 3.13/1.01  --bmc1_verbose                          false
% 3.13/1.01  --bmc1_dump_clauses_tptp                false
% 3.13/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.13/1.01  --bmc1_dump_file                        -
% 3.13/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.13/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.13/1.01  --bmc1_ucm_extend_mode                  1
% 3.13/1.01  --bmc1_ucm_init_mode                    2
% 3.13/1.01  --bmc1_ucm_cone_mode                    none
% 3.13/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.13/1.01  --bmc1_ucm_relax_model                  4
% 3.13/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.13/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.13/1.01  --bmc1_ucm_layered_model                none
% 3.13/1.01  --bmc1_ucm_max_lemma_size               10
% 3.13/1.01  
% 3.13/1.01  ------ AIG Options
% 3.13/1.01  
% 3.13/1.01  --aig_mode                              false
% 3.13/1.01  
% 3.13/1.01  ------ Instantiation Options
% 3.13/1.01  
% 3.13/1.01  --instantiation_flag                    true
% 3.13/1.01  --inst_sos_flag                         false
% 3.13/1.01  --inst_sos_phase                        true
% 3.13/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.13/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.13/1.01  --inst_lit_sel_side                     none
% 3.13/1.01  --inst_solver_per_active                1400
% 3.13/1.01  --inst_solver_calls_frac                1.
% 3.13/1.01  --inst_passive_queue_type               priority_queues
% 3.13/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.13/1.01  --inst_passive_queues_freq              [25;2]
% 3.13/1.01  --inst_dismatching                      true
% 3.13/1.01  --inst_eager_unprocessed_to_passive     true
% 3.13/1.01  --inst_prop_sim_given                   true
% 3.13/1.01  --inst_prop_sim_new                     false
% 3.13/1.01  --inst_subs_new                         false
% 3.13/1.01  --inst_eq_res_simp                      false
% 3.13/1.01  --inst_subs_given                       false
% 3.13/1.01  --inst_orphan_elimination               true
% 3.13/1.01  --inst_learning_loop_flag               true
% 3.13/1.01  --inst_learning_start                   3000
% 3.13/1.01  --inst_learning_factor                  2
% 3.13/1.01  --inst_start_prop_sim_after_learn       3
% 3.13/1.01  --inst_sel_renew                        solver
% 3.13/1.01  --inst_lit_activity_flag                true
% 3.13/1.01  --inst_restr_to_given                   false
% 3.13/1.01  --inst_activity_threshold               500
% 3.13/1.01  --inst_out_proof                        true
% 3.13/1.01  
% 3.13/1.01  ------ Resolution Options
% 3.13/1.01  
% 3.13/1.01  --resolution_flag                       false
% 3.13/1.01  --res_lit_sel                           adaptive
% 3.13/1.01  --res_lit_sel_side                      none
% 3.13/1.01  --res_ordering                          kbo
% 3.13/1.01  --res_to_prop_solver                    active
% 3.13/1.01  --res_prop_simpl_new                    false
% 3.13/1.01  --res_prop_simpl_given                  true
% 3.13/1.01  --res_passive_queue_type                priority_queues
% 3.13/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.13/1.01  --res_passive_queues_freq               [15;5]
% 3.13/1.01  --res_forward_subs                      full
% 3.13/1.01  --res_backward_subs                     full
% 3.13/1.01  --res_forward_subs_resolution           true
% 3.13/1.01  --res_backward_subs_resolution          true
% 3.13/1.01  --res_orphan_elimination                true
% 3.13/1.01  --res_time_limit                        2.
% 3.13/1.01  --res_out_proof                         true
% 3.13/1.01  
% 3.13/1.01  ------ Superposition Options
% 3.13/1.01  
% 3.13/1.01  --superposition_flag                    true
% 3.13/1.01  --sup_passive_queue_type                priority_queues
% 3.13/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.13/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.13/1.01  --demod_completeness_check              fast
% 3.13/1.01  --demod_use_ground                      true
% 3.13/1.01  --sup_to_prop_solver                    passive
% 3.13/1.01  --sup_prop_simpl_new                    true
% 3.13/1.01  --sup_prop_simpl_given                  true
% 3.13/1.01  --sup_fun_splitting                     false
% 3.13/1.01  --sup_smt_interval                      50000
% 3.13/1.01  
% 3.13/1.01  ------ Superposition Simplification Setup
% 3.13/1.01  
% 3.13/1.01  --sup_indices_passive                   []
% 3.13/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.13/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.13/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.13/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.13/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.13/1.01  --sup_full_bw                           [BwDemod]
% 3.13/1.01  --sup_immed_triv                        [TrivRules]
% 3.13/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.13/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.13/1.01  --sup_immed_bw_main                     []
% 3.13/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.13/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.13/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.13/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.13/1.01  
% 3.13/1.01  ------ Combination Options
% 3.13/1.01  
% 3.13/1.01  --comb_res_mult                         3
% 3.13/1.01  --comb_sup_mult                         2
% 3.13/1.01  --comb_inst_mult                        10
% 3.13/1.01  
% 3.13/1.01  ------ Debug Options
% 3.13/1.01  
% 3.13/1.01  --dbg_backtrace                         false
% 3.13/1.01  --dbg_dump_prop_clauses                 false
% 3.13/1.01  --dbg_dump_prop_clauses_file            -
% 3.13/1.01  --dbg_out_stat                          false
% 3.13/1.01  
% 3.13/1.01  
% 3.13/1.01  
% 3.13/1.01  
% 3.13/1.01  ------ Proving...
% 3.13/1.01  
% 3.13/1.01  
% 3.13/1.01  % SZS status Theorem for theBenchmark.p
% 3.13/1.01  
% 3.13/1.01   Resolution empty clause
% 3.13/1.01  
% 3.13/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.13/1.01  
% 3.13/1.01  fof(f21,conjecture,(
% 3.13/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.13/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.01  
% 3.13/1.01  fof(f22,negated_conjecture,(
% 3.13/1.01    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.13/1.01    inference(negated_conjecture,[],[f21])).
% 3.13/1.01  
% 3.13/1.01  fof(f46,plain,(
% 3.13/1.01    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.13/1.01    inference(ennf_transformation,[],[f22])).
% 3.13/1.01  
% 3.13/1.01  fof(f47,plain,(
% 3.13/1.01    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.13/1.01    inference(flattening,[],[f46])).
% 3.13/1.01  
% 3.13/1.01  fof(f52,plain,(
% 3.13/1.01    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 3.13/1.01    introduced(choice_axiom,[])).
% 3.13/1.01  
% 3.13/1.01  fof(f53,plain,(
% 3.13/1.01    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 3.13/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f47,f52])).
% 3.13/1.01  
% 3.13/1.01  fof(f88,plain,(
% 3.13/1.01    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.13/1.01    inference(cnf_transformation,[],[f53])).
% 3.13/1.01  
% 3.13/1.01  fof(f19,axiom,(
% 3.13/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 3.13/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.01  
% 3.13/1.01  fof(f42,plain,(
% 3.13/1.01    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.13/1.01    inference(ennf_transformation,[],[f19])).
% 3.13/1.01  
% 3.13/1.01  fof(f43,plain,(
% 3.13/1.01    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.13/1.01    inference(flattening,[],[f42])).
% 3.13/1.01  
% 3.13/1.01  fof(f82,plain,(
% 3.13/1.01    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.13/1.01    inference(cnf_transformation,[],[f43])).
% 3.13/1.01  
% 3.13/1.01  fof(f86,plain,(
% 3.13/1.01    v1_funct_1(sK3)),
% 3.13/1.01    inference(cnf_transformation,[],[f53])).
% 3.13/1.01  
% 3.13/1.01  fof(f91,plain,(
% 3.13/1.01    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 3.13/1.01    inference(cnf_transformation,[],[f53])).
% 3.13/1.01  
% 3.13/1.01  fof(f87,plain,(
% 3.13/1.01    v1_funct_2(sK3,sK0,sK1)),
% 3.13/1.01    inference(cnf_transformation,[],[f53])).
% 3.13/1.01  
% 3.13/1.01  fof(f18,axiom,(
% 3.13/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 3.13/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.01  
% 3.13/1.01  fof(f40,plain,(
% 3.13/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.13/1.01    inference(ennf_transformation,[],[f18])).
% 3.13/1.01  
% 3.13/1.01  fof(f41,plain,(
% 3.13/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.13/1.01    inference(flattening,[],[f40])).
% 3.13/1.01  
% 3.13/1.01  fof(f80,plain,(
% 3.13/1.01    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.13/1.01    inference(cnf_transformation,[],[f41])).
% 3.13/1.01  
% 3.13/1.01  fof(f90,plain,(
% 3.13/1.01    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 3.13/1.01    inference(cnf_transformation,[],[f53])).
% 3.13/1.01  
% 3.13/1.01  fof(f3,axiom,(
% 3.13/1.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.13/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.01  
% 3.13/1.01  fof(f48,plain,(
% 3.13/1.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.13/1.01    inference(nnf_transformation,[],[f3])).
% 3.13/1.01  
% 3.13/1.01  fof(f49,plain,(
% 3.13/1.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.13/1.01    inference(flattening,[],[f48])).
% 3.13/1.01  
% 3.13/1.01  fof(f56,plain,(
% 3.13/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.13/1.01    inference(cnf_transformation,[],[f49])).
% 3.13/1.01  
% 3.13/1.01  fof(f93,plain,(
% 3.13/1.01    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.13/1.01    inference(equality_resolution,[],[f56])).
% 3.13/1.01  
% 3.13/1.01  fof(f58,plain,(
% 3.13/1.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.13/1.01    inference(cnf_transformation,[],[f49])).
% 3.13/1.01  
% 3.13/1.01  fof(f89,plain,(
% 3.13/1.01    r1_tarski(sK2,sK0)),
% 3.13/1.01    inference(cnf_transformation,[],[f53])).
% 3.13/1.01  
% 3.13/1.01  fof(f17,axiom,(
% 3.13/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.13/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.01  
% 3.13/1.01  fof(f38,plain,(
% 3.13/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.13/1.01    inference(ennf_transformation,[],[f17])).
% 3.13/1.01  
% 3.13/1.01  fof(f39,plain,(
% 3.13/1.01    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.13/1.01    inference(flattening,[],[f38])).
% 3.13/1.01  
% 3.13/1.01  fof(f51,plain,(
% 3.13/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.13/1.01    inference(nnf_transformation,[],[f39])).
% 3.13/1.01  
% 3.13/1.01  fof(f74,plain,(
% 3.13/1.01    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.13/1.01    inference(cnf_transformation,[],[f51])).
% 3.13/1.01  
% 3.13/1.01  fof(f16,axiom,(
% 3.13/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.13/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.01  
% 3.13/1.01  fof(f37,plain,(
% 3.13/1.01    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.13/1.01    inference(ennf_transformation,[],[f16])).
% 3.13/1.01  
% 3.13/1.01  fof(f73,plain,(
% 3.13/1.01    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.13/1.01    inference(cnf_transformation,[],[f37])).
% 3.13/1.01  
% 3.13/1.01  fof(f10,axiom,(
% 3.13/1.01    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 3.13/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.01  
% 3.13/1.01  fof(f29,plain,(
% 3.13/1.01    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 3.13/1.01    inference(ennf_transformation,[],[f10])).
% 3.13/1.01  
% 3.13/1.01  fof(f30,plain,(
% 3.13/1.01    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.13/1.01    inference(flattening,[],[f29])).
% 3.13/1.01  
% 3.13/1.01  fof(f66,plain,(
% 3.13/1.01    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.13/1.01    inference(cnf_transformation,[],[f30])).
% 3.13/1.01  
% 3.13/1.01  fof(f13,axiom,(
% 3.13/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.13/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.01  
% 3.13/1.01  fof(f34,plain,(
% 3.13/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.13/1.01    inference(ennf_transformation,[],[f13])).
% 3.13/1.01  
% 3.13/1.01  fof(f70,plain,(
% 3.13/1.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.13/1.01    inference(cnf_transformation,[],[f34])).
% 3.13/1.01  
% 3.13/1.01  fof(f20,axiom,(
% 3.13/1.01    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 3.13/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.01  
% 3.13/1.01  fof(f44,plain,(
% 3.13/1.01    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.13/1.01    inference(ennf_transformation,[],[f20])).
% 3.13/1.01  
% 3.13/1.01  fof(f45,plain,(
% 3.13/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.13/1.01    inference(flattening,[],[f44])).
% 3.13/1.01  
% 3.13/1.01  fof(f85,plain,(
% 3.13/1.01    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.13/1.01    inference(cnf_transformation,[],[f45])).
% 3.13/1.01  
% 3.13/1.01  fof(f84,plain,(
% 3.13/1.01    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.13/1.01    inference(cnf_transformation,[],[f45])).
% 3.13/1.01  
% 3.13/1.01  fof(f14,axiom,(
% 3.13/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.13/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.01  
% 3.13/1.01  fof(f23,plain,(
% 3.13/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.13/1.01    inference(pure_predicate_removal,[],[f14])).
% 3.13/1.01  
% 3.13/1.01  fof(f35,plain,(
% 3.13/1.01    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.13/1.01    inference(ennf_transformation,[],[f23])).
% 3.13/1.01  
% 3.13/1.01  fof(f71,plain,(
% 3.13/1.01    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.13/1.01    inference(cnf_transformation,[],[f35])).
% 3.13/1.01  
% 3.13/1.01  fof(f7,axiom,(
% 3.13/1.01    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.13/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.01  
% 3.13/1.01  fof(f27,plain,(
% 3.13/1.01    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.13/1.01    inference(ennf_transformation,[],[f7])).
% 3.13/1.01  
% 3.13/1.01  fof(f50,plain,(
% 3.13/1.01    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.13/1.01    inference(nnf_transformation,[],[f27])).
% 3.13/1.01  
% 3.13/1.01  fof(f61,plain,(
% 3.13/1.01    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.13/1.01    inference(cnf_transformation,[],[f50])).
% 3.13/1.01  
% 3.13/1.01  fof(f81,plain,(
% 3.13/1.01    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.13/1.01    inference(cnf_transformation,[],[f41])).
% 3.13/1.01  
% 3.13/1.01  fof(f5,axiom,(
% 3.13/1.01    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.13/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.01  
% 3.13/1.01  fof(f60,plain,(
% 3.13/1.01    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.13/1.01    inference(cnf_transformation,[],[f5])).
% 3.13/1.01  
% 3.13/1.01  fof(f9,axiom,(
% 3.13/1.01    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.13/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.01  
% 3.13/1.01  fof(f65,plain,(
% 3.13/1.01    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 3.13/1.01    inference(cnf_transformation,[],[f9])).
% 3.13/1.01  
% 3.13/1.01  fof(f8,axiom,(
% 3.13/1.01    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0))),
% 3.13/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.01  
% 3.13/1.01  fof(f28,plain,(
% 3.13/1.01    ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 3.13/1.01    inference(ennf_transformation,[],[f8])).
% 3.13/1.01  
% 3.13/1.01  fof(f63,plain,(
% 3.13/1.01    ( ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 3.13/1.01    inference(cnf_transformation,[],[f28])).
% 3.13/1.01  
% 3.13/1.01  fof(f15,axiom,(
% 3.13/1.01    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 3.13/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.01  
% 3.13/1.01  fof(f36,plain,(
% 3.13/1.01    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 3.13/1.01    inference(ennf_transformation,[],[f15])).
% 3.13/1.01  
% 3.13/1.01  fof(f72,plain,(
% 3.13/1.01    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 3.13/1.01    inference(cnf_transformation,[],[f36])).
% 3.13/1.01  
% 3.13/1.01  fof(f1,axiom,(
% 3.13/1.01    v1_xboole_0(k1_xboole_0)),
% 3.13/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.01  
% 3.13/1.01  fof(f54,plain,(
% 3.13/1.01    v1_xboole_0(k1_xboole_0)),
% 3.13/1.01    inference(cnf_transformation,[],[f1])).
% 3.13/1.01  
% 3.13/1.01  fof(f2,axiom,(
% 3.13/1.01    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.13/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.01  
% 3.13/1.01  fof(f25,plain,(
% 3.13/1.01    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.13/1.01    inference(ennf_transformation,[],[f2])).
% 3.13/1.01  
% 3.13/1.01  fof(f55,plain,(
% 3.13/1.01    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.13/1.01    inference(cnf_transformation,[],[f25])).
% 3.13/1.01  
% 3.13/1.01  cnf(c_35,negated_conjecture,
% 3.13/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.13/1.01      inference(cnf_transformation,[],[f88]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_1464,plain,
% 3.13/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.13/1.01      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_28,plain,
% 3.13/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.13/1.01      | ~ v1_funct_1(X0)
% 3.13/1.01      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 3.13/1.01      inference(cnf_transformation,[],[f82]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_1467,plain,
% 3.13/1.01      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 3.13/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.13/1.01      | v1_funct_1(X2) != iProver_top ),
% 3.13/1.01      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_5257,plain,
% 3.13/1.01      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
% 3.13/1.01      | v1_funct_1(sK3) != iProver_top ),
% 3.13/1.01      inference(superposition,[status(thm)],[c_1464,c_1467]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_37,negated_conjecture,
% 3.13/1.01      ( v1_funct_1(sK3) ),
% 3.13/1.01      inference(cnf_transformation,[],[f86]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_1867,plain,
% 3.13/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.13/1.01      | ~ v1_funct_1(sK3)
% 3.13/1.01      | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_28]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_2030,plain,
% 3.13/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.13/1.01      | ~ v1_funct_1(sK3)
% 3.13/1.01      | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_1867]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_5386,plain,
% 3.13/1.01      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 3.13/1.01      inference(global_propositional_subsumption,
% 3.13/1.01                [status(thm)],
% 3.13/1.01                [c_5257,c_37,c_35,c_2030]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_32,negated_conjecture,
% 3.13/1.01      ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
% 3.13/1.01      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.13/1.01      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
% 3.13/1.01      inference(cnf_transformation,[],[f91]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_36,negated_conjecture,
% 3.13/1.01      ( v1_funct_2(sK3,sK0,sK1) ),
% 3.13/1.01      inference(cnf_transformation,[],[f87]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_611,plain,
% 3.13/1.01      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.13/1.01      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.13/1.01      | k2_partfun1(sK0,sK1,sK3,sK2) != sK3
% 3.13/1.01      | sK2 != sK0
% 3.13/1.01      | sK1 != sK1 ),
% 3.13/1.01      inference(resolution_lifted,[status(thm)],[c_32,c_36]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_716,plain,
% 3.13/1.01      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.13/1.01      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.13/1.01      | k2_partfun1(sK0,sK1,sK3,sK2) != sK3
% 3.13/1.01      | sK2 != sK0 ),
% 3.13/1.01      inference(equality_resolution_simp,[status(thm)],[c_611]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_1452,plain,
% 3.13/1.01      ( k2_partfun1(sK0,sK1,sK3,sK2) != sK3
% 3.13/1.01      | sK2 != sK0
% 3.13/1.01      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.13/1.01      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.13/1.01      inference(predicate_to_equality,[status(thm)],[c_716]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_5392,plain,
% 3.13/1.01      ( k7_relat_1(sK3,sK2) != sK3
% 3.13/1.01      | sK2 != sK0
% 3.13/1.01      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.13/1.01      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.13/1.01      inference(demodulation,[status(thm)],[c_5386,c_1452]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_27,plain,
% 3.13/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.13/1.01      | ~ v1_funct_1(X0)
% 3.13/1.01      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
% 3.13/1.01      inference(cnf_transformation,[],[f80]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_1468,plain,
% 3.13/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.13/1.01      | v1_funct_1(X0) != iProver_top
% 3.13/1.01      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
% 3.13/1.01      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_4460,plain,
% 3.13/1.01      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
% 3.13/1.01      | v1_funct_1(sK3) != iProver_top ),
% 3.13/1.01      inference(superposition,[status(thm)],[c_1464,c_1468]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_38,plain,
% 3.13/1.01      ( v1_funct_1(sK3) = iProver_top ),
% 3.13/1.01      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_40,plain,
% 3.13/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.13/1.01      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_1847,plain,
% 3.13/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.13/1.01      | v1_funct_1(k2_partfun1(X0,X1,sK3,X2))
% 3.13/1.01      | ~ v1_funct_1(sK3) ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_27]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_2025,plain,
% 3.13/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.13/1.01      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
% 3.13/1.01      | ~ v1_funct_1(sK3) ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_1847]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_2026,plain,
% 3.13/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.13/1.01      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
% 3.13/1.01      | v1_funct_1(sK3) != iProver_top ),
% 3.13/1.01      inference(predicate_to_equality,[status(thm)],[c_2025]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_4476,plain,
% 3.13/1.01      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
% 3.13/1.01      inference(global_propositional_subsumption,
% 3.13/1.01                [status(thm)],
% 3.13/1.01                [c_4460,c_38,c_40,c_2026]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_5395,plain,
% 3.13/1.01      ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 3.13/1.01      inference(demodulation,[status(thm)],[c_5386,c_4476]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_5420,plain,
% 3.13/1.01      ( k7_relat_1(sK3,sK2) != sK3
% 3.13/1.01      | sK2 != sK0
% 3.13/1.01      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.13/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_5392,c_5395]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_33,negated_conjecture,
% 3.13/1.01      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 3.13/1.01      inference(cnf_transformation,[],[f90]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_4,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f93]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_115,plain,
% 3.13/1.01      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_4]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_2,plain,
% 3.13/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.13/1.01      inference(cnf_transformation,[],[f58]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_119,plain,
% 3.13/1.01      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k1_xboole_0 ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_2]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_900,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_1824,plain,
% 3.13/1.01      ( sK2 != X0 | sK2 = sK0 | sK0 != X0 ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_900]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_1825,plain,
% 3.13/1.01      ( sK2 = sK0 | sK2 != k1_xboole_0 | sK0 != k1_xboole_0 ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_1824]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_1823,plain,
% 3.13/1.01      ( sK0 != X0 | sK0 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_900]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_2175,plain,
% 3.13/1.01      ( sK0 != sK0 | sK0 = k1_xboole_0 | k1_xboole_0 != sK0 ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_1823]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_899,plain,( X0 = X0 ),theory(equality) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_2176,plain,
% 3.13/1.01      ( sK0 = sK0 ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_899]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_2760,plain,
% 3.13/1.01      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_900]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_2761,plain,
% 3.13/1.01      ( sK1 != k1_xboole_0 | k1_xboole_0 = sK1 | k1_xboole_0 != k1_xboole_0 ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_2760]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_34,negated_conjecture,
% 3.13/1.01      ( r1_tarski(sK2,sK0) ),
% 3.13/1.01      inference(cnf_transformation,[],[f89]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_1465,plain,
% 3.13/1.01      ( r1_tarski(sK2,sK0) = iProver_top ),
% 3.13/1.01      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_25,plain,
% 3.13/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 3.13/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.13/1.01      | k1_relset_1(X1,X2,X0) = X1
% 3.13/1.01      | k1_xboole_0 = X2 ),
% 3.13/1.01      inference(cnf_transformation,[],[f74]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_582,plain,
% 3.13/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.13/1.01      | k1_relset_1(X1,X2,X0) = X1
% 3.13/1.01      | sK3 != X0
% 3.13/1.01      | sK1 != X2
% 3.13/1.01      | sK0 != X1
% 3.13/1.01      | k1_xboole_0 = X2 ),
% 3.13/1.01      inference(resolution_lifted,[status(thm)],[c_25,c_36]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_583,plain,
% 3.13/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.13/1.01      | k1_relset_1(sK0,sK1,sK3) = sK0
% 3.13/1.01      | k1_xboole_0 = sK1 ),
% 3.13/1.01      inference(unflattening,[status(thm)],[c_582]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_585,plain,
% 3.13/1.01      ( k1_relset_1(sK0,sK1,sK3) = sK0 | k1_xboole_0 = sK1 ),
% 3.13/1.01      inference(global_propositional_subsumption,[status(thm)],[c_583,c_35]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_19,plain,
% 3.13/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.13/1.01      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.13/1.01      inference(cnf_transformation,[],[f73]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_1470,plain,
% 3.13/1.01      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.13/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.13/1.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_2769,plain,
% 3.13/1.01      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 3.13/1.01      inference(superposition,[status(thm)],[c_1464,c_1470]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_2805,plain,
% 3.13/1.01      ( k1_relat_1(sK3) = sK0 | sK1 = k1_xboole_0 ),
% 3.13/1.01      inference(superposition,[status(thm)],[c_585,c_2769]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_12,plain,
% 3.13/1.01      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 3.13/1.01      | ~ v1_relat_1(X1)
% 3.13/1.01      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 3.13/1.01      inference(cnf_transformation,[],[f66]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_1476,plain,
% 3.13/1.01      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 3.13/1.01      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 3.13/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.13/1.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_4359,plain,
% 3.13/1.01      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 3.13/1.01      | sK1 = k1_xboole_0
% 3.13/1.01      | r1_tarski(X0,sK0) != iProver_top
% 3.13/1.01      | v1_relat_1(sK3) != iProver_top ),
% 3.13/1.01      inference(superposition,[status(thm)],[c_2805,c_1476]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_16,plain,
% 3.13/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 3.13/1.01      inference(cnf_transformation,[],[f70]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_1785,plain,
% 3.13/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.13/1.01      | v1_relat_1(sK3) ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_16]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_1786,plain,
% 3.13/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.13/1.01      | v1_relat_1(sK3) = iProver_top ),
% 3.13/1.01      inference(predicate_to_equality,[status(thm)],[c_1785]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_4595,plain,
% 3.13/1.01      ( r1_tarski(X0,sK0) != iProver_top
% 3.13/1.01      | sK1 = k1_xboole_0
% 3.13/1.01      | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
% 3.13/1.01      inference(global_propositional_subsumption,
% 3.13/1.01                [status(thm)],
% 3.13/1.01                [c_4359,c_40,c_1786]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_4596,plain,
% 3.13/1.01      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 3.13/1.01      | sK1 = k1_xboole_0
% 3.13/1.01      | r1_tarski(X0,sK0) != iProver_top ),
% 3.13/1.01      inference(renaming,[status(thm)],[c_4595]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_4605,plain,
% 3.13/1.01      ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2 | sK1 = k1_xboole_0 ),
% 3.13/1.01      inference(superposition,[status(thm)],[c_1465,c_4596]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_29,plain,
% 3.13/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.13/1.01      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.13/1.01      | ~ v1_funct_1(X0)
% 3.13/1.01      | ~ v1_relat_1(X0) ),
% 3.13/1.01      inference(cnf_transformation,[],[f85]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_1466,plain,
% 3.13/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
% 3.13/1.01      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 3.13/1.01      | v1_funct_1(X0) != iProver_top
% 3.13/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.13/1.01      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_4988,plain,
% 3.13/1.01      ( sK1 = k1_xboole_0
% 3.13/1.01      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 3.13/1.01      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
% 3.13/1.01      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
% 3.13/1.01      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.13/1.01      inference(superposition,[status(thm)],[c_4605,c_1466]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_5909,plain,
% 3.13/1.01      ( sK1 = k1_xboole_0
% 3.13/1.01      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 3.13/1.01      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
% 3.13/1.01      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.13/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_4988,c_5395]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_30,plain,
% 3.13/1.01      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 3.13/1.01      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.13/1.01      | ~ v1_funct_1(X0)
% 3.13/1.01      | ~ v1_relat_1(X0) ),
% 3.13/1.01      inference(cnf_transformation,[],[f84]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_593,plain,
% 3.13/1.01      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.13/1.01      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.13/1.01      | ~ v1_funct_1(X0)
% 3.13/1.01      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.13/1.01      | ~ v1_relat_1(X0)
% 3.13/1.01      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 3.13/1.01      | k1_relat_1(X0) != sK2
% 3.13/1.01      | sK1 != X1 ),
% 3.13/1.01      inference(resolution_lifted,[status(thm)],[c_30,c_32]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_594,plain,
% 3.13/1.01      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.13/1.01      | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
% 3.13/1.01      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.13/1.01      | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.13/1.01      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
% 3.13/1.01      inference(unflattening,[status(thm)],[c_593]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_17,plain,
% 3.13/1.01      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.13/1.01      inference(cnf_transformation,[],[f71]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_8,plain,
% 3.13/1.01      ( ~ v5_relat_1(X0,X1) | r1_tarski(k2_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 3.13/1.01      inference(cnf_transformation,[],[f61]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_381,plain,
% 3.13/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.13/1.01      | r1_tarski(k2_relat_1(X0),X2)
% 3.13/1.01      | ~ v1_relat_1(X0) ),
% 3.13/1.01      inference(resolution,[status(thm)],[c_17,c_8]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_385,plain,
% 3.13/1.01      ( r1_tarski(k2_relat_1(X0),X2)
% 3.13/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.13/1.01      inference(global_propositional_subsumption,[status(thm)],[c_381,c_16]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_386,plain,
% 3.13/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.13/1.01      | r1_tarski(k2_relat_1(X0),X2) ),
% 3.13/1.01      inference(renaming,[status(thm)],[c_385]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_606,plain,
% 3.13/1.01      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.13/1.01      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.13/1.01      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
% 3.13/1.01      inference(forward_subsumption_resolution,
% 3.13/1.01                [status(thm)],
% 3.13/1.01                [c_594,c_16,c_386]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_1453,plain,
% 3.13/1.01      ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 3.13/1.01      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.13/1.01      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.13/1.01      inference(predicate_to_equality,[status(thm)],[c_606]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_5391,plain,
% 3.13/1.01      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 3.13/1.01      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.13/1.01      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.13/1.01      inference(demodulation,[status(thm)],[c_5386,c_1453]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_5427,plain,
% 3.13/1.01      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 3.13/1.01      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.13/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_5391,c_5395]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_6741,plain,
% 3.13/1.01      ( sK1 = k1_xboole_0
% 3.13/1.01      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.13/1.01      inference(superposition,[status(thm)],[c_4605,c_5427]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_6746,plain,
% 3.13/1.01      ( sK1 = k1_xboole_0
% 3.13/1.01      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
% 3.13/1.01      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.13/1.01      inference(superposition,[status(thm)],[c_5909,c_6741]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_26,plain,
% 3.13/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.13/1.01      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.13/1.01      | ~ v1_funct_1(X0) ),
% 3.13/1.01      inference(cnf_transformation,[],[f81]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_1469,plain,
% 3.13/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.13/1.01      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 3.13/1.01      | v1_funct_1(X0) != iProver_top ),
% 3.13/1.01      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_5448,plain,
% 3.13/1.01      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 3.13/1.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.13/1.01      | v1_funct_1(sK3) != iProver_top ),
% 3.13/1.01      inference(superposition,[status(thm)],[c_5386,c_1469]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_5647,plain,
% 3.13/1.01      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.13/1.01      inference(global_propositional_subsumption,
% 3.13/1.01                [status(thm)],
% 3.13/1.01                [c_5448,c_38,c_40]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_1472,plain,
% 3.13/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.13/1.01      | v1_relat_1(X0) = iProver_top ),
% 3.13/1.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_5660,plain,
% 3.13/1.01      ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 3.13/1.01      inference(superposition,[status(thm)],[c_5647,c_1472]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_1462,plain,
% 3.13/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.13/1.01      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 3.13/1.01      inference(predicate_to_equality,[status(thm)],[c_386]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_5658,plain,
% 3.13/1.01      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) = iProver_top ),
% 3.13/1.01      inference(superposition,[status(thm)],[c_5647,c_1462]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_7514,plain,
% 3.13/1.01      ( sK1 = k1_xboole_0 ),
% 3.13/1.01      inference(forward_subsumption_resolution,
% 3.13/1.01                [status(thm)],
% 3.13/1.01                [c_6746,c_5660,c_5658]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_7532,plain,
% 3.13/1.01      ( sK0 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.13/1.01      inference(demodulation,[status(thm)],[c_7514,c_33]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_7533,plain,
% 3.13/1.01      ( sK0 = k1_xboole_0 ),
% 3.13/1.01      inference(equality_resolution_simp,[status(thm)],[c_7532]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_7596,plain,
% 3.13/1.01      ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
% 3.13/1.01      inference(demodulation,[status(thm)],[c_7533,c_1465]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_6,plain,
% 3.13/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.13/1.01      inference(cnf_transformation,[],[f60]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_1478,plain,
% 3.13/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.13/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_3868,plain,
% 3.13/1.01      ( r1_tarski(k2_relat_1(k1_xboole_0),X0) = iProver_top ),
% 3.13/1.01      inference(superposition,[status(thm)],[c_1478,c_1462]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_10,plain,
% 3.13/1.01      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.13/1.01      inference(cnf_transformation,[],[f65]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_3873,plain,
% 3.13/1.01      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.13/1.01      inference(light_normalisation,[status(thm)],[c_3868,c_10]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_1481,plain,
% 3.13/1.01      ( X0 = X1
% 3.13/1.01      | r1_tarski(X0,X1) != iProver_top
% 3.13/1.01      | r1_tarski(X1,X0) != iProver_top ),
% 3.13/1.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_4250,plain,
% 3.13/1.01      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.13/1.01      inference(superposition,[status(thm)],[c_3873,c_1481]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_7755,plain,
% 3.13/1.01      ( sK2 = k1_xboole_0 ),
% 3.13/1.01      inference(superposition,[status(thm)],[c_7596,c_4250]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_9563,plain,
% 3.13/1.01      ( k7_relat_1(sK3,sK2) != sK3
% 3.13/1.01      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.13/1.01      inference(global_propositional_subsumption,
% 3.13/1.01                [status(thm)],
% 3.13/1.01                [c_5420,c_33,c_115,c_119,c_1825,c_2175,c_2176,c_2761,c_7514,
% 3.13/1.01                 c_7755]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_2371,plain,
% 3.13/1.01      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.13/1.01      inference(superposition,[status(thm)],[c_1478,c_1472]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_9,plain,
% 3.13/1.01      ( ~ v1_relat_1(X0) | k7_relat_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.13/1.01      inference(cnf_transformation,[],[f63]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_1477,plain,
% 3.13/1.01      ( k7_relat_1(X0,k1_xboole_0) = k1_xboole_0
% 3.13/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.13/1.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_2917,plain,
% 3.13/1.01      ( k7_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.13/1.01      inference(superposition,[status(thm)],[c_2371,c_1477]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_18,plain,
% 3.13/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.13/1.01      | ~ v1_xboole_0(X1)
% 3.13/1.01      | v1_xboole_0(X0) ),
% 3.13/1.01      inference(cnf_transformation,[],[f72]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_1471,plain,
% 3.13/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.13/1.01      | v1_xboole_0(X1) != iProver_top
% 3.13/1.01      | v1_xboole_0(X0) = iProver_top ),
% 3.13/1.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_3418,plain,
% 3.13/1.01      ( v1_xboole_0(sK3) = iProver_top | v1_xboole_0(sK0) != iProver_top ),
% 3.13/1.01      inference(superposition,[status(thm)],[c_1464,c_1471]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_7593,plain,
% 3.13/1.01      ( v1_xboole_0(sK3) = iProver_top
% 3.13/1.01      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.13/1.01      inference(demodulation,[status(thm)],[c_7533,c_3418]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_0,plain,
% 3.13/1.01      ( v1_xboole_0(k1_xboole_0) ),
% 3.13/1.01      inference(cnf_transformation,[],[f54]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_122,plain,
% 3.13/1.01      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.13/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_901,plain,
% 3.13/1.01      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.13/1.01      theory(equality) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_2055,plain,
% 3.13/1.01      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK0) | sK0 != X0 ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_901]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_2056,plain,
% 3.13/1.01      ( sK0 != X0
% 3.13/1.01      | v1_xboole_0(X0) != iProver_top
% 3.13/1.01      | v1_xboole_0(sK0) = iProver_top ),
% 3.13/1.01      inference(predicate_to_equality,[status(thm)],[c_2055]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_2058,plain,
% 3.13/1.01      ( sK0 != k1_xboole_0
% 3.13/1.01      | v1_xboole_0(sK0) = iProver_top
% 3.13/1.01      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_2056]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_2084,plain,
% 3.13/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.13/1.01      | ~ v1_xboole_0(X0)
% 3.13/1.01      | v1_xboole_0(sK3) ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_18]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_2906,plain,
% 3.13/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.13/1.01      | v1_xboole_0(sK3)
% 3.13/1.01      | ~ v1_xboole_0(sK0) ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_2084]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_2907,plain,
% 3.13/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.13/1.01      | v1_xboole_0(sK3) = iProver_top
% 3.13/1.01      | v1_xboole_0(sK0) != iProver_top ),
% 3.13/1.01      inference(predicate_to_equality,[status(thm)],[c_2906]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_9135,plain,
% 3.13/1.01      ( v1_xboole_0(sK3) = iProver_top ),
% 3.13/1.01      inference(global_propositional_subsumption,
% 3.13/1.01                [status(thm)],
% 3.13/1.01                [c_7593,c_40,c_33,c_115,c_119,c_122,c_2058,c_2175,c_2176,
% 3.13/1.01                 c_2761,c_2907,c_7514]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_1,plain,
% 3.13/1.01      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.13/1.01      inference(cnf_transformation,[],[f55]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_1482,plain,
% 3.13/1.01      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.13/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_9140,plain,
% 3.13/1.01      ( sK3 = k1_xboole_0 ),
% 3.13/1.01      inference(superposition,[status(thm)],[c_9135,c_1482]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_9567,plain,
% 3.13/1.01      ( k1_xboole_0 != k1_xboole_0
% 3.13/1.01      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 3.13/1.01      inference(light_normalisation,
% 3.13/1.01                [status(thm)],
% 3.13/1.01                [c_9563,c_2917,c_7514,c_7755,c_9140]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_9568,plain,
% 3.13/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 3.13/1.01      inference(equality_resolution_simp,[status(thm)],[c_9567]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_9570,plain,
% 3.13/1.01      ( $false ),
% 3.13/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_9568,c_1478]) ).
% 3.13/1.01  
% 3.13/1.01  
% 3.13/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.13/1.01  
% 3.13/1.01  ------                               Statistics
% 3.13/1.01  
% 3.13/1.01  ------ General
% 3.13/1.01  
% 3.13/1.01  abstr_ref_over_cycles:                  0
% 3.13/1.01  abstr_ref_under_cycles:                 0
% 3.13/1.01  gc_basic_clause_elim:                   0
% 3.13/1.01  forced_gc_time:                         0
% 3.13/1.01  parsing_time:                           0.012
% 3.13/1.01  unif_index_cands_time:                  0.
% 3.13/1.01  unif_index_add_time:                    0.
% 3.13/1.01  orderings_time:                         0.
% 3.13/1.01  out_proof_time:                         0.015
% 3.13/1.01  total_time:                             0.272
% 3.13/1.01  num_of_symbols:                         50
% 3.13/1.01  num_of_terms:                           7646
% 3.13/1.01  
% 3.13/1.01  ------ Preprocessing
% 3.13/1.01  
% 3.13/1.01  num_of_splits:                          0
% 3.13/1.01  num_of_split_atoms:                     0
% 3.13/1.01  num_of_reused_defs:                     0
% 3.13/1.01  num_eq_ax_congr_red:                    7
% 3.13/1.01  num_of_sem_filtered_clauses:            1
% 3.13/1.01  num_of_subtypes:                        0
% 3.13/1.01  monotx_restored_types:                  0
% 3.13/1.01  sat_num_of_epr_types:                   0
% 3.13/1.01  sat_num_of_non_cyclic_types:            0
% 3.13/1.01  sat_guarded_non_collapsed_types:        0
% 3.13/1.01  num_pure_diseq_elim:                    0
% 3.13/1.01  simp_replaced_by:                       0
% 3.13/1.01  res_preprocessed:                       173
% 3.13/1.01  prep_upred:                             0
% 3.13/1.01  prep_unflattend:                        43
% 3.13/1.01  smt_new_axioms:                         0
% 3.13/1.01  pred_elim_cands:                        5
% 3.13/1.01  pred_elim:                              2
% 3.13/1.01  pred_elim_cl:                           0
% 3.13/1.01  pred_elim_cycles:                       4
% 3.13/1.01  merged_defs:                            0
% 3.13/1.01  merged_defs_ncl:                        0
% 3.13/1.01  bin_hyper_res:                          0
% 3.13/1.01  prep_cycles:                            4
% 3.13/1.01  pred_elim_time:                         0.009
% 3.13/1.01  splitting_time:                         0.
% 3.13/1.01  sem_filter_time:                        0.
% 3.13/1.01  monotx_time:                            0.001
% 3.13/1.01  subtype_inf_time:                       0.
% 3.13/1.01  
% 3.13/1.01  ------ Problem properties
% 3.13/1.01  
% 3.13/1.01  clauses:                                36
% 3.13/1.01  conjectures:                            4
% 3.13/1.01  epr:                                    8
% 3.13/1.01  horn:                                   32
% 3.13/1.01  ground:                                 15
% 3.13/1.01  unary:                                  8
% 3.13/1.01  binary:                                 8
% 3.13/1.01  lits:                                   97
% 3.13/1.01  lits_eq:                                34
% 3.13/1.01  fd_pure:                                0
% 3.13/1.01  fd_pseudo:                              0
% 3.13/1.01  fd_cond:                                3
% 3.13/1.01  fd_pseudo_cond:                         2
% 3.13/1.01  ac_symbols:                             0
% 3.13/1.01  
% 3.13/1.01  ------ Propositional Solver
% 3.13/1.01  
% 3.13/1.01  prop_solver_calls:                      27
% 3.13/1.01  prop_fast_solver_calls:                 1337
% 3.13/1.01  smt_solver_calls:                       0
% 3.13/1.01  smt_fast_solver_calls:                  0
% 3.13/1.01  prop_num_of_clauses:                    3502
% 3.13/1.01  prop_preprocess_simplified:             10297
% 3.13/1.01  prop_fo_subsumed:                       45
% 3.13/1.01  prop_solver_time:                       0.
% 3.13/1.01  smt_solver_time:                        0.
% 3.13/1.01  smt_fast_solver_time:                   0.
% 3.13/1.01  prop_fast_solver_time:                  0.
% 3.13/1.01  prop_unsat_core_time:                   0.
% 3.13/1.01  
% 3.13/1.01  ------ QBF
% 3.13/1.01  
% 3.13/1.01  qbf_q_res:                              0
% 3.13/1.01  qbf_num_tautologies:                    0
% 3.13/1.01  qbf_prep_cycles:                        0
% 3.13/1.01  
% 3.13/1.01  ------ BMC1
% 3.13/1.01  
% 3.13/1.01  bmc1_current_bound:                     -1
% 3.13/1.01  bmc1_last_solved_bound:                 -1
% 3.13/1.01  bmc1_unsat_core_size:                   -1
% 3.13/1.01  bmc1_unsat_core_parents_size:           -1
% 3.13/1.01  bmc1_merge_next_fun:                    0
% 3.13/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.13/1.01  
% 3.13/1.01  ------ Instantiation
% 3.13/1.01  
% 3.13/1.01  inst_num_of_clauses:                    975
% 3.13/1.01  inst_num_in_passive:                    482
% 3.13/1.01  inst_num_in_active:                     402
% 3.13/1.01  inst_num_in_unprocessed:                91
% 3.13/1.01  inst_num_of_loops:                      550
% 3.13/1.01  inst_num_of_learning_restarts:          0
% 3.13/1.01  inst_num_moves_active_passive:          147
% 3.13/1.01  inst_lit_activity:                      0
% 3.13/1.01  inst_lit_activity_moves:                0
% 3.13/1.01  inst_num_tautologies:                   0
% 3.13/1.01  inst_num_prop_implied:                  0
% 3.13/1.01  inst_num_existing_simplified:           0
% 3.13/1.01  inst_num_eq_res_simplified:             0
% 3.13/1.01  inst_num_child_elim:                    0
% 3.13/1.01  inst_num_of_dismatching_blockings:      511
% 3.13/1.01  inst_num_of_non_proper_insts:           766
% 3.13/1.01  inst_num_of_duplicates:                 0
% 3.13/1.01  inst_inst_num_from_inst_to_res:         0
% 3.13/1.01  inst_dismatching_checking_time:         0.
% 3.13/1.01  
% 3.13/1.01  ------ Resolution
% 3.13/1.01  
% 3.13/1.01  res_num_of_clauses:                     0
% 3.13/1.01  res_num_in_passive:                     0
% 3.13/1.01  res_num_in_active:                      0
% 3.13/1.01  res_num_of_loops:                       177
% 3.13/1.01  res_forward_subset_subsumed:            39
% 3.13/1.01  res_backward_subset_subsumed:           0
% 3.13/1.01  res_forward_subsumed:                   0
% 3.13/1.01  res_backward_subsumed:                  0
% 3.13/1.01  res_forward_subsumption_resolution:     6
% 3.13/1.01  res_backward_subsumption_resolution:    0
% 3.13/1.01  res_clause_to_clause_subsumption:       425
% 3.13/1.01  res_orphan_elimination:                 0
% 3.13/1.01  res_tautology_del:                      45
% 3.13/1.01  res_num_eq_res_simplified:              1
% 3.13/1.01  res_num_sel_changes:                    0
% 3.13/1.01  res_moves_from_active_to_pass:          0
% 3.13/1.01  
% 3.13/1.01  ------ Superposition
% 3.13/1.01  
% 3.13/1.01  sup_time_total:                         0.
% 3.13/1.01  sup_time_generating:                    0.
% 3.13/1.01  sup_time_sim_full:                      0.
% 3.13/1.01  sup_time_sim_immed:                     0.
% 3.13/1.01  
% 3.13/1.01  sup_num_of_clauses:                     108
% 3.13/1.01  sup_num_in_active:                      42
% 3.13/1.01  sup_num_in_passive:                     66
% 3.13/1.01  sup_num_of_loops:                       108
% 3.13/1.01  sup_fw_superposition:                   96
% 3.13/1.01  sup_bw_superposition:                   110
% 3.13/1.01  sup_immediate_simplified:               71
% 3.13/1.01  sup_given_eliminated:                   4
% 3.13/1.01  comparisons_done:                       0
% 3.13/1.01  comparisons_avoided:                    40
% 3.13/1.01  
% 3.13/1.01  ------ Simplifications
% 3.13/1.01  
% 3.13/1.01  
% 3.13/1.01  sim_fw_subset_subsumed:                 23
% 3.13/1.01  sim_bw_subset_subsumed:                 18
% 3.13/1.01  sim_fw_subsumed:                        16
% 3.13/1.01  sim_bw_subsumed:                        0
% 3.13/1.01  sim_fw_subsumption_res:                 10
% 3.13/1.01  sim_bw_subsumption_res:                 0
% 3.13/1.01  sim_tautology_del:                      9
% 3.13/1.01  sim_eq_tautology_del:                   27
% 3.13/1.01  sim_eq_res_simp:                        5
% 3.13/1.01  sim_fw_demodulated:                     8
% 3.13/1.01  sim_bw_demodulated:                     65
% 3.13/1.01  sim_light_normalised:                   53
% 3.13/1.01  sim_joinable_taut:                      0
% 3.13/1.01  sim_joinable_simp:                      0
% 3.13/1.01  sim_ac_normalised:                      0
% 3.13/1.01  sim_smt_subsumption:                    0
% 3.13/1.01  
%------------------------------------------------------------------------------
