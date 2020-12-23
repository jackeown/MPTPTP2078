%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:52 EST 2020

% Result     : Theorem 3.22s
% Output     : CNFRefutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :  219 (6817 expanded)
%              Number of clauses        :  144 (2244 expanded)
%              Number of leaves         :   20 (1274 expanded)
%              Depth                    :   28
%              Number of atoms          :  624 (37670 expanded)
%              Number of equality atoms :  315 (10061 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
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

fof(f19,negated_conjecture,(
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
    inference(negated_conjecture,[],[f18])).

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
    inference(ennf_transformation,[],[f19])).

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
    inference(flattening,[],[f38])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f39,f47])).

fof(f83,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f48])).

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
    inference(ennf_transformation,[],[f14])).

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
    inference(nnf_transformation,[],[f31])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f81,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f82,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f48])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f79,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f16,axiom,(
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
    inference(ennf_transformation,[],[f16])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f80,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f15,axiom,(
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
    inference(ennf_transformation,[],[f15])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f78,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f85,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f48])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f84,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f48])).

fof(f4,axiom,(
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
    inference(nnf_transformation,[],[f4])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f42])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f89,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f55])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f93,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f71])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f88,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f56])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f40])).

fof(f51,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f53,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
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
    inference(nnf_transformation,[],[f5])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_33,negated_conjecture,
    ( r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1701,plain,
    ( r1_tarski(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_35,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_628,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X0
    | sK1 != X2
    | sK0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_35])).

cnf(c_629,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_628])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_631,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_629,c_34])).

cnf(c_1700,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1706,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3257,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1700,c_1706])).

cnf(c_3592,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_631,c_3257])).

cnf(c_15,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1708,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4387,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3592,c_1708])).

cnf(c_39,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1993,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1994,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1993])).

cnf(c_4688,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | sK1 = k1_xboole_0
    | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4387,c_39,c_1994])).

cnf(c_4689,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4688])).

cnf(c_4700,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1701,c_4689])).

cnf(c_28,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1702,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_4987,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4700,c_1702])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1703,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_5396,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1700,c_1703])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2082,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_2280,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_2082])).

cnf(c_5697,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5396,c_36,c_34,c_2280])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1704,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4427,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1700,c_1704])).

cnf(c_37,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_2058,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(k2_partfun1(X0,X1,sK3,X2))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_2195,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2058])).

cnf(c_2196,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2195])).

cnf(c_4596,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4427,c_37,c_39,c_2196])).

cnf(c_5706,plain,
    ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5697,c_4596])).

cnf(c_6058,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4987,c_5706])).

cnf(c_29,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_31,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_639,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_relat_1(X0)
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_relat_1(X0) != sK2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_31])).

cnf(c_640,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
    inference(unflattening,[status(thm)],[c_639])).

cnf(c_17,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_11,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_427,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_17,c_11])).

cnf(c_431,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_427,c_16])).

cnf(c_432,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_431])).

cnf(c_652,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_640,c_16,c_432])).

cnf(c_1689,plain,
    ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_652])).

cnf(c_5704,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5697,c_1689])).

cnf(c_5720,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5704,c_5706])).

cnf(c_6138,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4700,c_5720])).

cnf(c_6144,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6058,c_6138])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1705,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_6226,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5697,c_1705])).

cnf(c_6750,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6226,c_37,c_39])).

cnf(c_1707,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_6762,plain,
    ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6750,c_1707])).

cnf(c_1698,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_432])).

cnf(c_6761,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_6750,c_1698])).

cnf(c_8495,plain,
    ( sK1 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6144,c_6762,c_6761])).

cnf(c_6759,plain,
    ( k1_relset_1(sK0,sK1,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_6750,c_1706])).

cnf(c_8497,plain,
    ( k1_relset_1(sK0,k1_xboole_0,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(demodulation,[status(thm)],[c_8495,c_6759])).

cnf(c_32,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_8518,plain,
    ( sK0 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8495,c_32])).

cnf(c_8519,plain,
    ( sK0 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_8518])).

cnf(c_8599,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(light_normalisation,[status(thm)],[c_8497,c_8519])).

cnf(c_8502,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8495,c_6750])).

cnf(c_8576,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8502,c_8519])).

cnf(c_6,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_8578,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8576,c_6])).

cnf(c_21,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_553,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | sK2 != k1_xboole_0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_31])).

cnf(c_554,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_553])).

cnf(c_1693,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_554])).

cnf(c_1898,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1693,c_6])).

cnf(c_2276,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2195])).

cnf(c_2277,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2276])).

cnf(c_2424,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | sK2 != k1_xboole_0
    | k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1898,c_37,c_39,c_2277])).

cnf(c_2425,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2424])).

cnf(c_5701,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k7_relat_1(sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5697,c_2425])).

cnf(c_8504,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8495,c_5701])).

cnf(c_5,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_8567,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8504,c_5])).

cnf(c_8582,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_8578,c_8567])).

cnf(c_8601,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8599,c_8582])).

cnf(c_7,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_109,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_110,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2025,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK2)
    | sK2 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1001,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2395,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1001])).

cnf(c_1002,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3024,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1002])).

cnf(c_3025,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3024])).

cnf(c_1003,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2308,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_1003])).

cnf(c_3559,plain,
    ( ~ r1_tarski(sK2,X0)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != sK2
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_2308])).

cnf(c_6889,plain,
    ( ~ r1_tarski(sK2,sK0)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != sK2
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_3559])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_7134,plain,
    ( r1_tarski(k1_xboole_0,sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_9811,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8601,c_33,c_32,c_109,c_110,c_2025,c_2395,c_3025,c_6889,c_7134,c_8495])).

cnf(c_8669,plain,
    ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8519,c_1701])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1714,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_8682,plain,
    ( sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8669,c_1714])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1712,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2813,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1700,c_1712])).

cnf(c_8513,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8495,c_2813])).

cnf(c_8533,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8513,c_8519])).

cnf(c_8535,plain,
    ( r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8533,c_6])).

cnf(c_8873,plain,
    ( sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8535,c_1714])).

cnf(c_9813,plain,
    ( k1_relat_1(k7_relat_1(k1_xboole_0,k1_xboole_0)) != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_9811,c_8682,c_8873])).

cnf(c_14,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1709,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2806,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1709,c_1714])).

cnf(c_82,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_84,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_82])).

cnf(c_8,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1988,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1989,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1988])).

cnf(c_1991,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
    | r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1989])).

cnf(c_2184,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2187,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2184])).

cnf(c_2189,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2187])).

cnf(c_2951,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2806,c_84,c_1991,c_2189])).

cnf(c_9814,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9813,c_2951])).

cnf(c_1715,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4698,plain,
    ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1715,c_4689])).

cnf(c_2087,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2089,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2087])).

cnf(c_2449,plain,
    ( r1_tarski(k1_xboole_0,k1_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_8145,plain,
    ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4698,c_34,c_1993,c_2089,c_2449])).

cnf(c_9601,plain,
    ( k1_relat_1(k7_relat_1(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8873,c_8145])).

cnf(c_9613,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9601,c_2951])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9814,c_9613])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:11:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.22/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.00  
% 3.22/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.22/1.00  
% 3.22/1.00  ------  iProver source info
% 3.22/1.00  
% 3.22/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.22/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.22/1.00  git: non_committed_changes: false
% 3.22/1.00  git: last_make_outside_of_git: false
% 3.22/1.00  
% 3.22/1.00  ------ 
% 3.22/1.00  
% 3.22/1.00  ------ Input Options
% 3.22/1.00  
% 3.22/1.00  --out_options                           all
% 3.22/1.00  --tptp_safe_out                         true
% 3.22/1.00  --problem_path                          ""
% 3.22/1.00  --include_path                          ""
% 3.22/1.00  --clausifier                            res/vclausify_rel
% 3.22/1.00  --clausifier_options                    --mode clausify
% 3.22/1.00  --stdin                                 false
% 3.22/1.00  --stats_out                             all
% 3.22/1.00  
% 3.22/1.00  ------ General Options
% 3.22/1.00  
% 3.22/1.00  --fof                                   false
% 3.22/1.00  --time_out_real                         305.
% 3.22/1.00  --time_out_virtual                      -1.
% 3.22/1.00  --symbol_type_check                     false
% 3.22/1.00  --clausify_out                          false
% 3.22/1.00  --sig_cnt_out                           false
% 3.22/1.00  --trig_cnt_out                          false
% 3.22/1.00  --trig_cnt_out_tolerance                1.
% 3.22/1.00  --trig_cnt_out_sk_spl                   false
% 3.22/1.00  --abstr_cl_out                          false
% 3.22/1.00  
% 3.22/1.00  ------ Global Options
% 3.22/1.00  
% 3.22/1.00  --schedule                              default
% 3.22/1.00  --add_important_lit                     false
% 3.22/1.00  --prop_solver_per_cl                    1000
% 3.22/1.00  --min_unsat_core                        false
% 3.22/1.00  --soft_assumptions                      false
% 3.22/1.00  --soft_lemma_size                       3
% 3.22/1.00  --prop_impl_unit_size                   0
% 3.22/1.00  --prop_impl_unit                        []
% 3.22/1.00  --share_sel_clauses                     true
% 3.22/1.00  --reset_solvers                         false
% 3.22/1.00  --bc_imp_inh                            [conj_cone]
% 3.22/1.00  --conj_cone_tolerance                   3.
% 3.22/1.00  --extra_neg_conj                        none
% 3.22/1.00  --large_theory_mode                     true
% 3.22/1.00  --prolific_symb_bound                   200
% 3.22/1.00  --lt_threshold                          2000
% 3.22/1.00  --clause_weak_htbl                      true
% 3.22/1.00  --gc_record_bc_elim                     false
% 3.22/1.00  
% 3.22/1.00  ------ Preprocessing Options
% 3.22/1.00  
% 3.22/1.00  --preprocessing_flag                    true
% 3.22/1.00  --time_out_prep_mult                    0.1
% 3.22/1.00  --splitting_mode                        input
% 3.22/1.00  --splitting_grd                         true
% 3.22/1.00  --splitting_cvd                         false
% 3.22/1.00  --splitting_cvd_svl                     false
% 3.22/1.00  --splitting_nvd                         32
% 3.22/1.00  --sub_typing                            true
% 3.22/1.00  --prep_gs_sim                           true
% 3.22/1.00  --prep_unflatten                        true
% 3.22/1.00  --prep_res_sim                          true
% 3.22/1.00  --prep_upred                            true
% 3.22/1.00  --prep_sem_filter                       exhaustive
% 3.22/1.00  --prep_sem_filter_out                   false
% 3.22/1.00  --pred_elim                             true
% 3.22/1.00  --res_sim_input                         true
% 3.22/1.00  --eq_ax_congr_red                       true
% 3.22/1.00  --pure_diseq_elim                       true
% 3.22/1.00  --brand_transform                       false
% 3.22/1.00  --non_eq_to_eq                          false
% 3.22/1.00  --prep_def_merge                        true
% 3.22/1.00  --prep_def_merge_prop_impl              false
% 3.22/1.00  --prep_def_merge_mbd                    true
% 3.22/1.00  --prep_def_merge_tr_red                 false
% 3.22/1.00  --prep_def_merge_tr_cl                  false
% 3.22/1.00  --smt_preprocessing                     true
% 3.22/1.00  --smt_ac_axioms                         fast
% 3.22/1.00  --preprocessed_out                      false
% 3.22/1.00  --preprocessed_stats                    false
% 3.22/1.00  
% 3.22/1.00  ------ Abstraction refinement Options
% 3.22/1.00  
% 3.22/1.00  --abstr_ref                             []
% 3.22/1.00  --abstr_ref_prep                        false
% 3.22/1.00  --abstr_ref_until_sat                   false
% 3.22/1.00  --abstr_ref_sig_restrict                funpre
% 3.22/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.22/1.00  --abstr_ref_under                       []
% 3.22/1.00  
% 3.22/1.00  ------ SAT Options
% 3.22/1.00  
% 3.22/1.00  --sat_mode                              false
% 3.22/1.00  --sat_fm_restart_options                ""
% 3.22/1.00  --sat_gr_def                            false
% 3.22/1.00  --sat_epr_types                         true
% 3.22/1.00  --sat_non_cyclic_types                  false
% 3.22/1.00  --sat_finite_models                     false
% 3.22/1.00  --sat_fm_lemmas                         false
% 3.22/1.00  --sat_fm_prep                           false
% 3.22/1.00  --sat_fm_uc_incr                        true
% 3.22/1.00  --sat_out_model                         small
% 3.22/1.00  --sat_out_clauses                       false
% 3.22/1.00  
% 3.22/1.00  ------ QBF Options
% 3.22/1.00  
% 3.22/1.00  --qbf_mode                              false
% 3.22/1.00  --qbf_elim_univ                         false
% 3.22/1.00  --qbf_dom_inst                          none
% 3.22/1.00  --qbf_dom_pre_inst                      false
% 3.22/1.00  --qbf_sk_in                             false
% 3.22/1.00  --qbf_pred_elim                         true
% 3.22/1.00  --qbf_split                             512
% 3.22/1.00  
% 3.22/1.00  ------ BMC1 Options
% 3.22/1.00  
% 3.22/1.00  --bmc1_incremental                      false
% 3.22/1.00  --bmc1_axioms                           reachable_all
% 3.22/1.00  --bmc1_min_bound                        0
% 3.22/1.00  --bmc1_max_bound                        -1
% 3.22/1.00  --bmc1_max_bound_default                -1
% 3.22/1.00  --bmc1_symbol_reachability              true
% 3.22/1.00  --bmc1_property_lemmas                  false
% 3.22/1.00  --bmc1_k_induction                      false
% 3.22/1.00  --bmc1_non_equiv_states                 false
% 3.22/1.00  --bmc1_deadlock                         false
% 3.22/1.00  --bmc1_ucm                              false
% 3.22/1.00  --bmc1_add_unsat_core                   none
% 3.22/1.00  --bmc1_unsat_core_children              false
% 3.22/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.22/1.00  --bmc1_out_stat                         full
% 3.22/1.00  --bmc1_ground_init                      false
% 3.22/1.00  --bmc1_pre_inst_next_state              false
% 3.22/1.00  --bmc1_pre_inst_state                   false
% 3.22/1.00  --bmc1_pre_inst_reach_state             false
% 3.22/1.00  --bmc1_out_unsat_core                   false
% 3.22/1.00  --bmc1_aig_witness_out                  false
% 3.22/1.00  --bmc1_verbose                          false
% 3.22/1.00  --bmc1_dump_clauses_tptp                false
% 3.22/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.22/1.00  --bmc1_dump_file                        -
% 3.22/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.22/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.22/1.00  --bmc1_ucm_extend_mode                  1
% 3.22/1.00  --bmc1_ucm_init_mode                    2
% 3.22/1.00  --bmc1_ucm_cone_mode                    none
% 3.22/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.22/1.00  --bmc1_ucm_relax_model                  4
% 3.22/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.22/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.22/1.00  --bmc1_ucm_layered_model                none
% 3.22/1.00  --bmc1_ucm_max_lemma_size               10
% 3.22/1.00  
% 3.22/1.00  ------ AIG Options
% 3.22/1.00  
% 3.22/1.00  --aig_mode                              false
% 3.22/1.00  
% 3.22/1.00  ------ Instantiation Options
% 3.22/1.00  
% 3.22/1.00  --instantiation_flag                    true
% 3.22/1.00  --inst_sos_flag                         false
% 3.22/1.00  --inst_sos_phase                        true
% 3.22/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.22/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.22/1.00  --inst_lit_sel_side                     num_symb
% 3.22/1.00  --inst_solver_per_active                1400
% 3.22/1.00  --inst_solver_calls_frac                1.
% 3.22/1.00  --inst_passive_queue_type               priority_queues
% 3.22/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.22/1.00  --inst_passive_queues_freq              [25;2]
% 3.22/1.00  --inst_dismatching                      true
% 3.22/1.00  --inst_eager_unprocessed_to_passive     true
% 3.22/1.00  --inst_prop_sim_given                   true
% 3.22/1.00  --inst_prop_sim_new                     false
% 3.22/1.00  --inst_subs_new                         false
% 3.22/1.00  --inst_eq_res_simp                      false
% 3.22/1.00  --inst_subs_given                       false
% 3.22/1.00  --inst_orphan_elimination               true
% 3.22/1.00  --inst_learning_loop_flag               true
% 3.22/1.00  --inst_learning_start                   3000
% 3.22/1.00  --inst_learning_factor                  2
% 3.22/1.00  --inst_start_prop_sim_after_learn       3
% 3.22/1.00  --inst_sel_renew                        solver
% 3.22/1.00  --inst_lit_activity_flag                true
% 3.22/1.00  --inst_restr_to_given                   false
% 3.22/1.00  --inst_activity_threshold               500
% 3.22/1.00  --inst_out_proof                        true
% 3.22/1.00  
% 3.22/1.00  ------ Resolution Options
% 3.22/1.00  
% 3.22/1.00  --resolution_flag                       true
% 3.22/1.00  --res_lit_sel                           adaptive
% 3.22/1.00  --res_lit_sel_side                      none
% 3.22/1.00  --res_ordering                          kbo
% 3.22/1.00  --res_to_prop_solver                    active
% 3.22/1.00  --res_prop_simpl_new                    false
% 3.22/1.00  --res_prop_simpl_given                  true
% 3.22/1.00  --res_passive_queue_type                priority_queues
% 3.22/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.22/1.00  --res_passive_queues_freq               [15;5]
% 3.22/1.00  --res_forward_subs                      full
% 3.22/1.00  --res_backward_subs                     full
% 3.22/1.00  --res_forward_subs_resolution           true
% 3.22/1.00  --res_backward_subs_resolution          true
% 3.22/1.00  --res_orphan_elimination                true
% 3.22/1.00  --res_time_limit                        2.
% 3.22/1.00  --res_out_proof                         true
% 3.22/1.00  
% 3.22/1.00  ------ Superposition Options
% 3.22/1.00  
% 3.22/1.00  --superposition_flag                    true
% 3.22/1.00  --sup_passive_queue_type                priority_queues
% 3.22/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.22/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.22/1.00  --demod_completeness_check              fast
% 3.22/1.00  --demod_use_ground                      true
% 3.22/1.00  --sup_to_prop_solver                    passive
% 3.22/1.00  --sup_prop_simpl_new                    true
% 3.22/1.00  --sup_prop_simpl_given                  true
% 3.22/1.00  --sup_fun_splitting                     false
% 3.22/1.00  --sup_smt_interval                      50000
% 3.22/1.00  
% 3.22/1.00  ------ Superposition Simplification Setup
% 3.22/1.00  
% 3.22/1.00  --sup_indices_passive                   []
% 3.22/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.22/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.22/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.22/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.22/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.22/1.00  --sup_full_bw                           [BwDemod]
% 3.22/1.00  --sup_immed_triv                        [TrivRules]
% 3.22/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.22/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.22/1.00  --sup_immed_bw_main                     []
% 3.22/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.22/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.22/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.22/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.22/1.00  
% 3.22/1.00  ------ Combination Options
% 3.22/1.00  
% 3.22/1.00  --comb_res_mult                         3
% 3.22/1.00  --comb_sup_mult                         2
% 3.22/1.00  --comb_inst_mult                        10
% 3.22/1.00  
% 3.22/1.00  ------ Debug Options
% 3.22/1.00  
% 3.22/1.00  --dbg_backtrace                         false
% 3.22/1.00  --dbg_dump_prop_clauses                 false
% 3.22/1.00  --dbg_dump_prop_clauses_file            -
% 3.22/1.00  --dbg_out_stat                          false
% 3.22/1.00  ------ Parsing...
% 3.22/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.22/1.00  
% 3.22/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.22/1.00  
% 3.22/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.22/1.00  
% 3.22/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.22/1.00  ------ Proving...
% 3.22/1.00  ------ Problem Properties 
% 3.22/1.00  
% 3.22/1.00  
% 3.22/1.00  clauses                                 35
% 3.22/1.00  conjectures                             4
% 3.22/1.00  EPR                                     7
% 3.22/1.00  Horn                                    30
% 3.22/1.00  unary                                   8
% 3.22/1.00  binary                                  10
% 3.22/1.00  lits                                    93
% 3.22/1.00  lits eq                                 35
% 3.22/1.00  fd_pure                                 0
% 3.22/1.00  fd_pseudo                               0
% 3.22/1.00  fd_cond                                 4
% 3.22/1.00  fd_pseudo_cond                          1
% 3.22/1.00  AC symbols                              0
% 3.22/1.00  
% 3.22/1.00  ------ Schedule dynamic 5 is on 
% 3.22/1.00  
% 3.22/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.22/1.00  
% 3.22/1.00  
% 3.22/1.00  ------ 
% 3.22/1.00  Current options:
% 3.22/1.00  ------ 
% 3.22/1.00  
% 3.22/1.00  ------ Input Options
% 3.22/1.00  
% 3.22/1.00  --out_options                           all
% 3.22/1.00  --tptp_safe_out                         true
% 3.22/1.00  --problem_path                          ""
% 3.22/1.00  --include_path                          ""
% 3.22/1.00  --clausifier                            res/vclausify_rel
% 3.22/1.00  --clausifier_options                    --mode clausify
% 3.22/1.00  --stdin                                 false
% 3.22/1.00  --stats_out                             all
% 3.22/1.00  
% 3.22/1.00  ------ General Options
% 3.22/1.00  
% 3.22/1.00  --fof                                   false
% 3.22/1.00  --time_out_real                         305.
% 3.22/1.00  --time_out_virtual                      -1.
% 3.22/1.00  --symbol_type_check                     false
% 3.22/1.00  --clausify_out                          false
% 3.22/1.00  --sig_cnt_out                           false
% 3.22/1.00  --trig_cnt_out                          false
% 3.22/1.00  --trig_cnt_out_tolerance                1.
% 3.22/1.00  --trig_cnt_out_sk_spl                   false
% 3.22/1.00  --abstr_cl_out                          false
% 3.22/1.00  
% 3.22/1.00  ------ Global Options
% 3.22/1.00  
% 3.22/1.00  --schedule                              default
% 3.22/1.00  --add_important_lit                     false
% 3.22/1.00  --prop_solver_per_cl                    1000
% 3.22/1.00  --min_unsat_core                        false
% 3.22/1.00  --soft_assumptions                      false
% 3.22/1.00  --soft_lemma_size                       3
% 3.22/1.00  --prop_impl_unit_size                   0
% 3.22/1.00  --prop_impl_unit                        []
% 3.22/1.00  --share_sel_clauses                     true
% 3.22/1.00  --reset_solvers                         false
% 3.22/1.00  --bc_imp_inh                            [conj_cone]
% 3.22/1.00  --conj_cone_tolerance                   3.
% 3.22/1.00  --extra_neg_conj                        none
% 3.22/1.00  --large_theory_mode                     true
% 3.22/1.00  --prolific_symb_bound                   200
% 3.22/1.00  --lt_threshold                          2000
% 3.22/1.00  --clause_weak_htbl                      true
% 3.22/1.00  --gc_record_bc_elim                     false
% 3.22/1.00  
% 3.22/1.00  ------ Preprocessing Options
% 3.22/1.00  
% 3.22/1.00  --preprocessing_flag                    true
% 3.22/1.00  --time_out_prep_mult                    0.1
% 3.22/1.00  --splitting_mode                        input
% 3.22/1.00  --splitting_grd                         true
% 3.22/1.00  --splitting_cvd                         false
% 3.22/1.00  --splitting_cvd_svl                     false
% 3.22/1.00  --splitting_nvd                         32
% 3.22/1.00  --sub_typing                            true
% 3.22/1.00  --prep_gs_sim                           true
% 3.22/1.00  --prep_unflatten                        true
% 3.22/1.00  --prep_res_sim                          true
% 3.22/1.00  --prep_upred                            true
% 3.22/1.00  --prep_sem_filter                       exhaustive
% 3.22/1.00  --prep_sem_filter_out                   false
% 3.22/1.00  --pred_elim                             true
% 3.22/1.00  --res_sim_input                         true
% 3.22/1.00  --eq_ax_congr_red                       true
% 3.22/1.00  --pure_diseq_elim                       true
% 3.22/1.00  --brand_transform                       false
% 3.22/1.00  --non_eq_to_eq                          false
% 3.22/1.00  --prep_def_merge                        true
% 3.22/1.00  --prep_def_merge_prop_impl              false
% 3.22/1.00  --prep_def_merge_mbd                    true
% 3.22/1.00  --prep_def_merge_tr_red                 false
% 3.22/1.00  --prep_def_merge_tr_cl                  false
% 3.22/1.00  --smt_preprocessing                     true
% 3.22/1.00  --smt_ac_axioms                         fast
% 3.22/1.00  --preprocessed_out                      false
% 3.22/1.00  --preprocessed_stats                    false
% 3.22/1.00  
% 3.22/1.00  ------ Abstraction refinement Options
% 3.22/1.00  
% 3.22/1.00  --abstr_ref                             []
% 3.22/1.00  --abstr_ref_prep                        false
% 3.22/1.00  --abstr_ref_until_sat                   false
% 3.22/1.00  --abstr_ref_sig_restrict                funpre
% 3.22/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.22/1.00  --abstr_ref_under                       []
% 3.22/1.00  
% 3.22/1.00  ------ SAT Options
% 3.22/1.00  
% 3.22/1.00  --sat_mode                              false
% 3.22/1.00  --sat_fm_restart_options                ""
% 3.22/1.00  --sat_gr_def                            false
% 3.22/1.00  --sat_epr_types                         true
% 3.22/1.00  --sat_non_cyclic_types                  false
% 3.22/1.00  --sat_finite_models                     false
% 3.22/1.00  --sat_fm_lemmas                         false
% 3.22/1.00  --sat_fm_prep                           false
% 3.22/1.00  --sat_fm_uc_incr                        true
% 3.22/1.00  --sat_out_model                         small
% 3.22/1.00  --sat_out_clauses                       false
% 3.22/1.00  
% 3.22/1.00  ------ QBF Options
% 3.22/1.00  
% 3.22/1.00  --qbf_mode                              false
% 3.22/1.00  --qbf_elim_univ                         false
% 3.22/1.00  --qbf_dom_inst                          none
% 3.22/1.00  --qbf_dom_pre_inst                      false
% 3.22/1.00  --qbf_sk_in                             false
% 3.22/1.00  --qbf_pred_elim                         true
% 3.22/1.00  --qbf_split                             512
% 3.22/1.00  
% 3.22/1.00  ------ BMC1 Options
% 3.22/1.00  
% 3.22/1.00  --bmc1_incremental                      false
% 3.22/1.00  --bmc1_axioms                           reachable_all
% 3.22/1.00  --bmc1_min_bound                        0
% 3.22/1.00  --bmc1_max_bound                        -1
% 3.22/1.00  --bmc1_max_bound_default                -1
% 3.22/1.00  --bmc1_symbol_reachability              true
% 3.22/1.00  --bmc1_property_lemmas                  false
% 3.22/1.00  --bmc1_k_induction                      false
% 3.22/1.00  --bmc1_non_equiv_states                 false
% 3.22/1.00  --bmc1_deadlock                         false
% 3.22/1.00  --bmc1_ucm                              false
% 3.22/1.00  --bmc1_add_unsat_core                   none
% 3.22/1.00  --bmc1_unsat_core_children              false
% 3.22/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.22/1.00  --bmc1_out_stat                         full
% 3.22/1.00  --bmc1_ground_init                      false
% 3.22/1.00  --bmc1_pre_inst_next_state              false
% 3.22/1.00  --bmc1_pre_inst_state                   false
% 3.22/1.00  --bmc1_pre_inst_reach_state             false
% 3.22/1.00  --bmc1_out_unsat_core                   false
% 3.22/1.00  --bmc1_aig_witness_out                  false
% 3.22/1.00  --bmc1_verbose                          false
% 3.22/1.00  --bmc1_dump_clauses_tptp                false
% 3.22/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.22/1.00  --bmc1_dump_file                        -
% 3.22/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.22/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.22/1.00  --bmc1_ucm_extend_mode                  1
% 3.22/1.00  --bmc1_ucm_init_mode                    2
% 3.22/1.00  --bmc1_ucm_cone_mode                    none
% 3.22/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.22/1.00  --bmc1_ucm_relax_model                  4
% 3.22/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.22/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.22/1.00  --bmc1_ucm_layered_model                none
% 3.22/1.00  --bmc1_ucm_max_lemma_size               10
% 3.22/1.00  
% 3.22/1.00  ------ AIG Options
% 3.22/1.00  
% 3.22/1.00  --aig_mode                              false
% 3.22/1.00  
% 3.22/1.00  ------ Instantiation Options
% 3.22/1.00  
% 3.22/1.00  --instantiation_flag                    true
% 3.22/1.00  --inst_sos_flag                         false
% 3.22/1.00  --inst_sos_phase                        true
% 3.22/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.22/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.22/1.00  --inst_lit_sel_side                     none
% 3.22/1.00  --inst_solver_per_active                1400
% 3.22/1.00  --inst_solver_calls_frac                1.
% 3.22/1.00  --inst_passive_queue_type               priority_queues
% 3.22/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.22/1.00  --inst_passive_queues_freq              [25;2]
% 3.22/1.00  --inst_dismatching                      true
% 3.22/1.00  --inst_eager_unprocessed_to_passive     true
% 3.22/1.00  --inst_prop_sim_given                   true
% 3.22/1.00  --inst_prop_sim_new                     false
% 3.22/1.00  --inst_subs_new                         false
% 3.22/1.00  --inst_eq_res_simp                      false
% 3.22/1.00  --inst_subs_given                       false
% 3.22/1.00  --inst_orphan_elimination               true
% 3.22/1.00  --inst_learning_loop_flag               true
% 3.22/1.00  --inst_learning_start                   3000
% 3.22/1.00  --inst_learning_factor                  2
% 3.22/1.00  --inst_start_prop_sim_after_learn       3
% 3.22/1.00  --inst_sel_renew                        solver
% 3.22/1.00  --inst_lit_activity_flag                true
% 3.22/1.00  --inst_restr_to_given                   false
% 3.22/1.00  --inst_activity_threshold               500
% 3.22/1.00  --inst_out_proof                        true
% 3.22/1.00  
% 3.22/1.00  ------ Resolution Options
% 3.22/1.00  
% 3.22/1.00  --resolution_flag                       false
% 3.22/1.00  --res_lit_sel                           adaptive
% 3.22/1.00  --res_lit_sel_side                      none
% 3.22/1.00  --res_ordering                          kbo
% 3.22/1.00  --res_to_prop_solver                    active
% 3.22/1.00  --res_prop_simpl_new                    false
% 3.22/1.00  --res_prop_simpl_given                  true
% 3.22/1.00  --res_passive_queue_type                priority_queues
% 3.22/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.22/1.00  --res_passive_queues_freq               [15;5]
% 3.22/1.00  --res_forward_subs                      full
% 3.22/1.00  --res_backward_subs                     full
% 3.22/1.00  --res_forward_subs_resolution           true
% 3.22/1.00  --res_backward_subs_resolution          true
% 3.22/1.00  --res_orphan_elimination                true
% 3.22/1.00  --res_time_limit                        2.
% 3.22/1.00  --res_out_proof                         true
% 3.22/1.00  
% 3.22/1.00  ------ Superposition Options
% 3.22/1.00  
% 3.22/1.00  --superposition_flag                    true
% 3.22/1.00  --sup_passive_queue_type                priority_queues
% 3.22/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.22/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.22/1.00  --demod_completeness_check              fast
% 3.22/1.00  --demod_use_ground                      true
% 3.22/1.00  --sup_to_prop_solver                    passive
% 3.22/1.00  --sup_prop_simpl_new                    true
% 3.22/1.00  --sup_prop_simpl_given                  true
% 3.22/1.00  --sup_fun_splitting                     false
% 3.22/1.00  --sup_smt_interval                      50000
% 3.22/1.00  
% 3.22/1.00  ------ Superposition Simplification Setup
% 3.22/1.00  
% 3.22/1.00  --sup_indices_passive                   []
% 3.22/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.22/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.22/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.22/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.22/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.22/1.00  --sup_full_bw                           [BwDemod]
% 3.22/1.00  --sup_immed_triv                        [TrivRules]
% 3.22/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.22/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.22/1.00  --sup_immed_bw_main                     []
% 3.22/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.22/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.22/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.22/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.22/1.00  
% 3.22/1.00  ------ Combination Options
% 3.22/1.00  
% 3.22/1.00  --comb_res_mult                         3
% 3.22/1.00  --comb_sup_mult                         2
% 3.22/1.00  --comb_inst_mult                        10
% 3.22/1.00  
% 3.22/1.00  ------ Debug Options
% 3.22/1.00  
% 3.22/1.00  --dbg_backtrace                         false
% 3.22/1.00  --dbg_dump_prop_clauses                 false
% 3.22/1.00  --dbg_dump_prop_clauses_file            -
% 3.22/1.00  --dbg_out_stat                          false
% 3.22/1.00  
% 3.22/1.00  
% 3.22/1.00  
% 3.22/1.00  
% 3.22/1.00  ------ Proving...
% 3.22/1.00  
% 3.22/1.00  
% 3.22/1.00  % SZS status Theorem for theBenchmark.p
% 3.22/1.00  
% 3.22/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.22/1.00  
% 3.22/1.00  fof(f18,conjecture,(
% 3.22/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.22/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/1.00  
% 3.22/1.00  fof(f19,negated_conjecture,(
% 3.22/1.00    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.22/1.00    inference(negated_conjecture,[],[f18])).
% 3.22/1.00  
% 3.22/1.00  fof(f38,plain,(
% 3.22/1.00    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.22/1.00    inference(ennf_transformation,[],[f19])).
% 3.22/1.00  
% 3.22/1.00  fof(f39,plain,(
% 3.22/1.00    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.22/1.00    inference(flattening,[],[f38])).
% 3.22/1.00  
% 3.22/1.00  fof(f47,plain,(
% 3.22/1.00    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 3.22/1.00    introduced(choice_axiom,[])).
% 3.22/1.00  
% 3.22/1.00  fof(f48,plain,(
% 3.22/1.00    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 3.22/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f39,f47])).
% 3.22/1.00  
% 3.22/1.00  fof(f83,plain,(
% 3.22/1.00    r1_tarski(sK2,sK0)),
% 3.22/1.00    inference(cnf_transformation,[],[f48])).
% 3.22/1.00  
% 3.22/1.00  fof(f14,axiom,(
% 3.22/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.22/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/1.00  
% 3.22/1.00  fof(f30,plain,(
% 3.22/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.22/1.00    inference(ennf_transformation,[],[f14])).
% 3.22/1.00  
% 3.22/1.00  fof(f31,plain,(
% 3.22/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.22/1.00    inference(flattening,[],[f30])).
% 3.22/1.00  
% 3.22/1.00  fof(f46,plain,(
% 3.22/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.22/1.00    inference(nnf_transformation,[],[f31])).
% 3.22/1.00  
% 3.22/1.00  fof(f68,plain,(
% 3.22/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.22/1.00    inference(cnf_transformation,[],[f46])).
% 3.22/1.00  
% 3.22/1.00  fof(f81,plain,(
% 3.22/1.00    v1_funct_2(sK3,sK0,sK1)),
% 3.22/1.00    inference(cnf_transformation,[],[f48])).
% 3.22/1.00  
% 3.22/1.00  fof(f82,plain,(
% 3.22/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.22/1.00    inference(cnf_transformation,[],[f48])).
% 3.22/1.00  
% 3.22/1.00  fof(f13,axiom,(
% 3.22/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.22/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/1.00  
% 3.22/1.00  fof(f29,plain,(
% 3.22/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.22/1.00    inference(ennf_transformation,[],[f13])).
% 3.22/1.00  
% 3.22/1.00  fof(f67,plain,(
% 3.22/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.22/1.00    inference(cnf_transformation,[],[f29])).
% 3.22/1.00  
% 3.22/1.00  fof(f10,axiom,(
% 3.22/1.00    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 3.22/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/1.00  
% 3.22/1.00  fof(f25,plain,(
% 3.22/1.00    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 3.22/1.00    inference(ennf_transformation,[],[f10])).
% 3.22/1.00  
% 3.22/1.00  fof(f26,plain,(
% 3.22/1.00    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.22/1.00    inference(flattening,[],[f25])).
% 3.22/1.00  
% 3.22/1.00  fof(f64,plain,(
% 3.22/1.00    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.22/1.00    inference(cnf_transformation,[],[f26])).
% 3.22/1.00  
% 3.22/1.00  fof(f11,axiom,(
% 3.22/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.22/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/1.00  
% 3.22/1.00  fof(f27,plain,(
% 3.22/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.22/1.00    inference(ennf_transformation,[],[f11])).
% 3.22/1.00  
% 3.22/1.00  fof(f65,plain,(
% 3.22/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.22/1.00    inference(cnf_transformation,[],[f27])).
% 3.22/1.00  
% 3.22/1.00  fof(f17,axiom,(
% 3.22/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 3.22/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/1.00  
% 3.22/1.00  fof(f36,plain,(
% 3.22/1.00    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.22/1.00    inference(ennf_transformation,[],[f17])).
% 3.22/1.00  
% 3.22/1.00  fof(f37,plain,(
% 3.22/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.22/1.00    inference(flattening,[],[f36])).
% 3.22/1.00  
% 3.22/1.00  fof(f79,plain,(
% 3.22/1.00    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.22/1.00    inference(cnf_transformation,[],[f37])).
% 3.22/1.00  
% 3.22/1.00  fof(f16,axiom,(
% 3.22/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 3.22/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/1.00  
% 3.22/1.00  fof(f34,plain,(
% 3.22/1.00    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.22/1.00    inference(ennf_transformation,[],[f16])).
% 3.22/1.00  
% 3.22/1.00  fof(f35,plain,(
% 3.22/1.00    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.22/1.00    inference(flattening,[],[f34])).
% 3.22/1.00  
% 3.22/1.00  fof(f76,plain,(
% 3.22/1.00    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.22/1.00    inference(cnf_transformation,[],[f35])).
% 3.22/1.00  
% 3.22/1.00  fof(f80,plain,(
% 3.22/1.00    v1_funct_1(sK3)),
% 3.22/1.00    inference(cnf_transformation,[],[f48])).
% 3.22/1.00  
% 3.22/1.00  fof(f15,axiom,(
% 3.22/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 3.22/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/1.00  
% 3.22/1.00  fof(f32,plain,(
% 3.22/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.22/1.00    inference(ennf_transformation,[],[f15])).
% 3.22/1.00  
% 3.22/1.00  fof(f33,plain,(
% 3.22/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.22/1.00    inference(flattening,[],[f32])).
% 3.22/1.00  
% 3.22/1.00  fof(f74,plain,(
% 3.22/1.00    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.22/1.00    inference(cnf_transformation,[],[f33])).
% 3.22/1.00  
% 3.22/1.00  fof(f78,plain,(
% 3.22/1.00    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.22/1.00    inference(cnf_transformation,[],[f37])).
% 3.22/1.00  
% 3.22/1.00  fof(f85,plain,(
% 3.22/1.00    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 3.22/1.00    inference(cnf_transformation,[],[f48])).
% 3.22/1.00  
% 3.22/1.00  fof(f12,axiom,(
% 3.22/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.22/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/1.00  
% 3.22/1.00  fof(f20,plain,(
% 3.22/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.22/1.00    inference(pure_predicate_removal,[],[f12])).
% 3.22/1.00  
% 3.22/1.00  fof(f28,plain,(
% 3.22/1.00    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.22/1.00    inference(ennf_transformation,[],[f20])).
% 3.22/1.00  
% 3.22/1.00  fof(f66,plain,(
% 3.22/1.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.22/1.00    inference(cnf_transformation,[],[f28])).
% 3.22/1.00  
% 3.22/1.00  fof(f6,axiom,(
% 3.22/1.00    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.22/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/1.00  
% 3.22/1.00  fof(f22,plain,(
% 3.22/1.00    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.22/1.00    inference(ennf_transformation,[],[f6])).
% 3.22/1.00  
% 3.22/1.00  fof(f45,plain,(
% 3.22/1.00    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.22/1.00    inference(nnf_transformation,[],[f22])).
% 3.22/1.00  
% 3.22/1.00  fof(f59,plain,(
% 3.22/1.00    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.22/1.00    inference(cnf_transformation,[],[f45])).
% 3.22/1.00  
% 3.22/1.00  fof(f75,plain,(
% 3.22/1.00    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.22/1.00    inference(cnf_transformation,[],[f33])).
% 3.22/1.00  
% 3.22/1.00  fof(f84,plain,(
% 3.22/1.00    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 3.22/1.00    inference(cnf_transformation,[],[f48])).
% 3.22/1.00  
% 3.22/1.00  fof(f4,axiom,(
% 3.22/1.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.22/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/1.00  
% 3.22/1.00  fof(f42,plain,(
% 3.22/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.22/1.00    inference(nnf_transformation,[],[f4])).
% 3.22/1.00  
% 3.22/1.00  fof(f43,plain,(
% 3.22/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.22/1.00    inference(flattening,[],[f42])).
% 3.22/1.00  
% 3.22/1.00  fof(f55,plain,(
% 3.22/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.22/1.00    inference(cnf_transformation,[],[f43])).
% 3.22/1.00  
% 3.22/1.00  fof(f89,plain,(
% 3.22/1.00    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.22/1.00    inference(equality_resolution,[],[f55])).
% 3.22/1.00  
% 3.22/1.00  fof(f71,plain,(
% 3.22/1.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.22/1.00    inference(cnf_transformation,[],[f46])).
% 3.22/1.00  
% 3.22/1.00  fof(f93,plain,(
% 3.22/1.00    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.22/1.00    inference(equality_resolution,[],[f71])).
% 3.22/1.00  
% 3.22/1.00  fof(f56,plain,(
% 3.22/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.22/1.00    inference(cnf_transformation,[],[f43])).
% 3.22/1.00  
% 3.22/1.00  fof(f88,plain,(
% 3.22/1.00    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.22/1.00    inference(equality_resolution,[],[f56])).
% 3.22/1.00  
% 3.22/1.00  fof(f54,plain,(
% 3.22/1.00    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.22/1.00    inference(cnf_transformation,[],[f43])).
% 3.22/1.00  
% 3.22/1.00  fof(f1,axiom,(
% 3.22/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.22/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/1.00  
% 3.22/1.00  fof(f40,plain,(
% 3.22/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.22/1.00    inference(nnf_transformation,[],[f1])).
% 3.22/1.00  
% 3.22/1.00  fof(f41,plain,(
% 3.22/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.22/1.00    inference(flattening,[],[f40])).
% 3.22/1.00  
% 3.22/1.00  fof(f51,plain,(
% 3.22/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.22/1.00    inference(cnf_transformation,[],[f41])).
% 3.22/1.00  
% 3.22/1.00  fof(f2,axiom,(
% 3.22/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.22/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/1.00  
% 3.22/1.00  fof(f52,plain,(
% 3.22/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.22/1.00    inference(cnf_transformation,[],[f2])).
% 3.22/1.00  
% 3.22/1.00  fof(f3,axiom,(
% 3.22/1.00    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 3.22/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/1.00  
% 3.22/1.00  fof(f21,plain,(
% 3.22/1.00    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 3.22/1.00    inference(ennf_transformation,[],[f3])).
% 3.22/1.00  
% 3.22/1.00  fof(f53,plain,(
% 3.22/1.00    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 3.22/1.00    inference(cnf_transformation,[],[f21])).
% 3.22/1.00  
% 3.22/1.00  fof(f5,axiom,(
% 3.22/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.22/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/1.00  
% 3.22/1.00  fof(f44,plain,(
% 3.22/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.22/1.00    inference(nnf_transformation,[],[f5])).
% 3.22/1.00  
% 3.22/1.00  fof(f57,plain,(
% 3.22/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.22/1.00    inference(cnf_transformation,[],[f44])).
% 3.22/1.00  
% 3.22/1.00  fof(f9,axiom,(
% 3.22/1.00    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 3.22/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.22/1.00  
% 3.22/1.00  fof(f24,plain,(
% 3.22/1.00    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 3.22/1.00    inference(ennf_transformation,[],[f9])).
% 3.22/1.00  
% 3.22/1.00  fof(f63,plain,(
% 3.22/1.00    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 3.22/1.00    inference(cnf_transformation,[],[f24])).
% 3.22/1.00  
% 3.22/1.00  fof(f58,plain,(
% 3.22/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.22/1.00    inference(cnf_transformation,[],[f44])).
% 3.22/1.00  
% 3.22/1.00  cnf(c_33,negated_conjecture,
% 3.22/1.00      ( r1_tarski(sK2,sK0) ),
% 3.22/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_1701,plain,
% 3.22/1.00      ( r1_tarski(sK2,sK0) = iProver_top ),
% 3.22/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_24,plain,
% 3.22/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.22/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.22/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.22/1.00      | k1_xboole_0 = X2 ),
% 3.22/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_35,negated_conjecture,
% 3.22/1.00      ( v1_funct_2(sK3,sK0,sK1) ),
% 3.22/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_628,plain,
% 3.22/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.22/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.22/1.00      | sK3 != X0
% 3.22/1.00      | sK1 != X2
% 3.22/1.00      | sK0 != X1
% 3.22/1.00      | k1_xboole_0 = X2 ),
% 3.22/1.00      inference(resolution_lifted,[status(thm)],[c_24,c_35]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_629,plain,
% 3.22/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.22/1.00      | k1_relset_1(sK0,sK1,sK3) = sK0
% 3.22/1.00      | k1_xboole_0 = sK1 ),
% 3.22/1.00      inference(unflattening,[status(thm)],[c_628]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_34,negated_conjecture,
% 3.22/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.22/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_631,plain,
% 3.22/1.00      ( k1_relset_1(sK0,sK1,sK3) = sK0 | k1_xboole_0 = sK1 ),
% 3.22/1.00      inference(global_propositional_subsumption,
% 3.22/1.00                [status(thm)],
% 3.22/1.00                [c_629,c_34]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_1700,plain,
% 3.22/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.22/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_18,plain,
% 3.22/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.22/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.22/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_1706,plain,
% 3.22/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.22/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.22/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_3257,plain,
% 3.22/1.00      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 3.22/1.00      inference(superposition,[status(thm)],[c_1700,c_1706]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_3592,plain,
% 3.22/1.00      ( k1_relat_1(sK3) = sK0 | sK1 = k1_xboole_0 ),
% 3.22/1.00      inference(superposition,[status(thm)],[c_631,c_3257]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_15,plain,
% 3.22/1.00      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 3.22/1.00      | ~ v1_relat_1(X1)
% 3.22/1.00      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 3.22/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_1708,plain,
% 3.22/1.00      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 3.22/1.00      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 3.22/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.22/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_4387,plain,
% 3.22/1.00      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 3.22/1.00      | sK1 = k1_xboole_0
% 3.22/1.00      | r1_tarski(X0,sK0) != iProver_top
% 3.22/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.22/1.00      inference(superposition,[status(thm)],[c_3592,c_1708]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_39,plain,
% 3.22/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.22/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_16,plain,
% 3.22/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.22/1.00      | v1_relat_1(X0) ),
% 3.22/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_1993,plain,
% 3.22/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.22/1.00      | v1_relat_1(sK3) ),
% 3.22/1.00      inference(instantiation,[status(thm)],[c_16]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_1994,plain,
% 3.22/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.22/1.00      | v1_relat_1(sK3) = iProver_top ),
% 3.22/1.00      inference(predicate_to_equality,[status(thm)],[c_1993]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_4688,plain,
% 3.22/1.00      ( r1_tarski(X0,sK0) != iProver_top
% 3.22/1.00      | sK1 = k1_xboole_0
% 3.22/1.00      | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
% 3.22/1.00      inference(global_propositional_subsumption,
% 3.22/1.00                [status(thm)],
% 3.22/1.00                [c_4387,c_39,c_1994]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_4689,plain,
% 3.22/1.00      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 3.22/1.00      | sK1 = k1_xboole_0
% 3.22/1.00      | r1_tarski(X0,sK0) != iProver_top ),
% 3.22/1.00      inference(renaming,[status(thm)],[c_4688]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_4700,plain,
% 3.22/1.00      ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2 | sK1 = k1_xboole_0 ),
% 3.22/1.00      inference(superposition,[status(thm)],[c_1701,c_4689]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_28,plain,
% 3.22/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.22/1.00      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.22/1.00      | ~ v1_funct_1(X0)
% 3.22/1.00      | ~ v1_relat_1(X0) ),
% 3.22/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_1702,plain,
% 3.22/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
% 3.22/1.00      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 3.22/1.00      | v1_funct_1(X0) != iProver_top
% 3.22/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.22/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_4987,plain,
% 3.22/1.00      ( sK1 = k1_xboole_0
% 3.22/1.00      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 3.22/1.00      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
% 3.22/1.00      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
% 3.22/1.00      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.22/1.00      inference(superposition,[status(thm)],[c_4700,c_1702]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_27,plain,
% 3.22/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.22/1.00      | ~ v1_funct_1(X0)
% 3.22/1.00      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 3.22/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_1703,plain,
% 3.22/1.00      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 3.22/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.22/1.00      | v1_funct_1(X2) != iProver_top ),
% 3.22/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_5396,plain,
% 3.22/1.00      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
% 3.22/1.00      | v1_funct_1(sK3) != iProver_top ),
% 3.22/1.00      inference(superposition,[status(thm)],[c_1700,c_1703]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_36,negated_conjecture,
% 3.22/1.00      ( v1_funct_1(sK3) ),
% 3.22/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_2082,plain,
% 3.22/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.22/1.00      | ~ v1_funct_1(sK3)
% 3.22/1.00      | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
% 3.22/1.00      inference(instantiation,[status(thm)],[c_27]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_2280,plain,
% 3.22/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.22/1.00      | ~ v1_funct_1(sK3)
% 3.22/1.00      | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 3.22/1.00      inference(instantiation,[status(thm)],[c_2082]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_5697,plain,
% 3.22/1.00      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 3.22/1.00      inference(global_propositional_subsumption,
% 3.22/1.00                [status(thm)],
% 3.22/1.00                [c_5396,c_36,c_34,c_2280]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_26,plain,
% 3.22/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.22/1.00      | ~ v1_funct_1(X0)
% 3.22/1.00      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
% 3.22/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_1704,plain,
% 3.22/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.22/1.00      | v1_funct_1(X0) != iProver_top
% 3.22/1.00      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
% 3.22/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_4427,plain,
% 3.22/1.00      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
% 3.22/1.00      | v1_funct_1(sK3) != iProver_top ),
% 3.22/1.00      inference(superposition,[status(thm)],[c_1700,c_1704]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_37,plain,
% 3.22/1.00      ( v1_funct_1(sK3) = iProver_top ),
% 3.22/1.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_2058,plain,
% 3.22/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.22/1.00      | v1_funct_1(k2_partfun1(X0,X1,sK3,X2))
% 3.22/1.00      | ~ v1_funct_1(sK3) ),
% 3.22/1.00      inference(instantiation,[status(thm)],[c_26]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_2195,plain,
% 3.22/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.22/1.00      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
% 3.22/1.00      | ~ v1_funct_1(sK3) ),
% 3.22/1.00      inference(instantiation,[status(thm)],[c_2058]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_2196,plain,
% 3.22/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.22/1.00      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
% 3.22/1.00      | v1_funct_1(sK3) != iProver_top ),
% 3.22/1.00      inference(predicate_to_equality,[status(thm)],[c_2195]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_4596,plain,
% 3.22/1.00      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
% 3.22/1.00      inference(global_propositional_subsumption,
% 3.22/1.00                [status(thm)],
% 3.22/1.00                [c_4427,c_37,c_39,c_2196]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_5706,plain,
% 3.22/1.00      ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 3.22/1.00      inference(demodulation,[status(thm)],[c_5697,c_4596]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_6058,plain,
% 3.22/1.00      ( sK1 = k1_xboole_0
% 3.22/1.00      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 3.22/1.00      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
% 3.22/1.00      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.22/1.00      inference(forward_subsumption_resolution,
% 3.22/1.00                [status(thm)],
% 3.22/1.00                [c_4987,c_5706]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_29,plain,
% 3.22/1.00      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 3.22/1.00      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.22/1.00      | ~ v1_funct_1(X0)
% 3.22/1.00      | ~ v1_relat_1(X0) ),
% 3.22/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_31,negated_conjecture,
% 3.22/1.00      ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
% 3.22/1.00      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.22/1.00      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
% 3.22/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_639,plain,
% 3.22/1.00      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.22/1.00      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.22/1.00      | ~ v1_funct_1(X0)
% 3.22/1.00      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.22/1.00      | ~ v1_relat_1(X0)
% 3.22/1.00      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 3.22/1.00      | k1_relat_1(X0) != sK2
% 3.22/1.00      | sK1 != X1 ),
% 3.22/1.00      inference(resolution_lifted,[status(thm)],[c_29,c_31]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_640,plain,
% 3.22/1.00      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.22/1.00      | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
% 3.22/1.00      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.22/1.00      | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.22/1.00      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
% 3.22/1.00      inference(unflattening,[status(thm)],[c_639]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_17,plain,
% 3.22/1.00      ( v5_relat_1(X0,X1)
% 3.22/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.22/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_11,plain,
% 3.22/1.00      ( ~ v5_relat_1(X0,X1)
% 3.22/1.00      | r1_tarski(k2_relat_1(X0),X1)
% 3.22/1.00      | ~ v1_relat_1(X0) ),
% 3.22/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_427,plain,
% 3.22/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.22/1.00      | r1_tarski(k2_relat_1(X0),X2)
% 3.22/1.00      | ~ v1_relat_1(X0) ),
% 3.22/1.00      inference(resolution,[status(thm)],[c_17,c_11]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_431,plain,
% 3.22/1.00      ( r1_tarski(k2_relat_1(X0),X2)
% 3.22/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.22/1.00      inference(global_propositional_subsumption,
% 3.22/1.00                [status(thm)],
% 3.22/1.00                [c_427,c_16]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_432,plain,
% 3.22/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.22/1.00      | r1_tarski(k2_relat_1(X0),X2) ),
% 3.22/1.00      inference(renaming,[status(thm)],[c_431]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_652,plain,
% 3.22/1.00      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.22/1.00      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.22/1.00      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
% 3.22/1.00      inference(forward_subsumption_resolution,
% 3.22/1.00                [status(thm)],
% 3.22/1.00                [c_640,c_16,c_432]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_1689,plain,
% 3.22/1.00      ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 3.22/1.00      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.22/1.00      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.22/1.00      inference(predicate_to_equality,[status(thm)],[c_652]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_5704,plain,
% 3.22/1.00      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 3.22/1.00      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.22/1.00      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.22/1.00      inference(demodulation,[status(thm)],[c_5697,c_1689]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_5720,plain,
% 3.22/1.00      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 3.22/1.00      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.22/1.00      inference(forward_subsumption_resolution,
% 3.22/1.00                [status(thm)],
% 3.22/1.00                [c_5704,c_5706]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_6138,plain,
% 3.22/1.00      ( sK1 = k1_xboole_0
% 3.22/1.00      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.22/1.00      inference(superposition,[status(thm)],[c_4700,c_5720]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_6144,plain,
% 3.22/1.00      ( sK1 = k1_xboole_0
% 3.22/1.00      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
% 3.22/1.00      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.22/1.00      inference(superposition,[status(thm)],[c_6058,c_6138]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_25,plain,
% 3.22/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.22/1.00      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.22/1.00      | ~ v1_funct_1(X0) ),
% 3.22/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_1705,plain,
% 3.22/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.22/1.00      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 3.22/1.00      | v1_funct_1(X0) != iProver_top ),
% 3.22/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_6226,plain,
% 3.22/1.00      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 3.22/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.22/1.00      | v1_funct_1(sK3) != iProver_top ),
% 3.22/1.00      inference(superposition,[status(thm)],[c_5697,c_1705]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_6750,plain,
% 3.22/1.00      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.22/1.00      inference(global_propositional_subsumption,
% 3.22/1.00                [status(thm)],
% 3.22/1.00                [c_6226,c_37,c_39]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_1707,plain,
% 3.22/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.22/1.00      | v1_relat_1(X0) = iProver_top ),
% 3.22/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_6762,plain,
% 3.22/1.00      ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 3.22/1.00      inference(superposition,[status(thm)],[c_6750,c_1707]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_1698,plain,
% 3.22/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.22/1.00      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 3.22/1.00      inference(predicate_to_equality,[status(thm)],[c_432]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_6761,plain,
% 3.22/1.00      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) = iProver_top ),
% 3.22/1.00      inference(superposition,[status(thm)],[c_6750,c_1698]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_8495,plain,
% 3.22/1.00      ( sK1 = k1_xboole_0 ),
% 3.22/1.00      inference(forward_subsumption_resolution,
% 3.22/1.00                [status(thm)],
% 3.22/1.00                [c_6144,c_6762,c_6761]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_6759,plain,
% 3.22/1.00      ( k1_relset_1(sK0,sK1,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
% 3.22/1.00      inference(superposition,[status(thm)],[c_6750,c_1706]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_8497,plain,
% 3.22/1.00      ( k1_relset_1(sK0,k1_xboole_0,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
% 3.22/1.00      inference(demodulation,[status(thm)],[c_8495,c_6759]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_32,negated_conjecture,
% 3.22/1.00      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 3.22/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_8518,plain,
% 3.22/1.00      ( sK0 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.22/1.00      inference(demodulation,[status(thm)],[c_8495,c_32]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_8519,plain,
% 3.22/1.00      ( sK0 = k1_xboole_0 ),
% 3.22/1.00      inference(equality_resolution_simp,[status(thm)],[c_8518]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_8599,plain,
% 3.22/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
% 3.22/1.00      inference(light_normalisation,[status(thm)],[c_8497,c_8519]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_8502,plain,
% 3.22/1.00      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
% 3.22/1.00      inference(demodulation,[status(thm)],[c_8495,c_6750]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_8576,plain,
% 3.22/1.00      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.22/1.00      inference(light_normalisation,[status(thm)],[c_8502,c_8519]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_6,plain,
% 3.22/1.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.22/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_8578,plain,
% 3.22/1.00      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.22/1.00      inference(demodulation,[status(thm)],[c_8576,c_6]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_21,plain,
% 3.22/1.00      ( v1_funct_2(X0,k1_xboole_0,X1)
% 3.22/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.22/1.00      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 3.22/1.00      inference(cnf_transformation,[],[f93]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_553,plain,
% 3.22/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.22/1.00      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.22/1.00      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.22/1.00      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 3.22/1.00      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 3.22/1.00      | sK2 != k1_xboole_0
% 3.22/1.00      | sK1 != X1 ),
% 3.22/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_31]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_554,plain,
% 3.22/1.00      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.22/1.00      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 3.22/1.00      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.22/1.00      | k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
% 3.22/1.00      | sK2 != k1_xboole_0 ),
% 3.22/1.00      inference(unflattening,[status(thm)],[c_553]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_1693,plain,
% 3.22/1.00      ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
% 3.22/1.00      | sK2 != k1_xboole_0
% 3.22/1.00      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.22/1.00      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
% 3.22/1.00      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.22/1.00      inference(predicate_to_equality,[status(thm)],[c_554]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_1898,plain,
% 3.22/1.00      ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
% 3.22/1.00      | sK2 != k1_xboole_0
% 3.22/1.00      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.22/1.00      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.22/1.00      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.22/1.00      inference(demodulation,[status(thm)],[c_1693,c_6]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_2276,plain,
% 3.22/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.22/1.00      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.22/1.00      | ~ v1_funct_1(sK3) ),
% 3.22/1.00      inference(instantiation,[status(thm)],[c_2195]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_2277,plain,
% 3.22/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.22/1.00      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) = iProver_top
% 3.22/1.00      | v1_funct_1(sK3) != iProver_top ),
% 3.22/1.00      inference(predicate_to_equality,[status(thm)],[c_2276]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_2424,plain,
% 3.22/1.00      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.22/1.00      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.22/1.00      | sK2 != k1_xboole_0
% 3.22/1.00      | k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0 ),
% 3.22/1.00      inference(global_propositional_subsumption,
% 3.22/1.00                [status(thm)],
% 3.22/1.00                [c_1898,c_37,c_39,c_2277]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_2425,plain,
% 3.22/1.00      ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
% 3.22/1.00      | sK2 != k1_xboole_0
% 3.22/1.00      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.22/1.00      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.22/1.00      inference(renaming,[status(thm)],[c_2424]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_5701,plain,
% 3.22/1.00      ( k1_relset_1(k1_xboole_0,sK1,k7_relat_1(sK3,sK2)) != k1_xboole_0
% 3.22/1.00      | sK2 != k1_xboole_0
% 3.22/1.00      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.22/1.00      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.22/1.00      inference(demodulation,[status(thm)],[c_5697,c_2425]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_8504,plain,
% 3.22/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,sK2)) != k1_xboole_0
% 3.22/1.00      | sK2 != k1_xboole_0
% 3.22/1.00      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
% 3.22/1.00      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.22/1.00      inference(demodulation,[status(thm)],[c_8495,c_5701]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_5,plain,
% 3.22/1.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.22/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_8567,plain,
% 3.22/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,sK2)) != k1_xboole_0
% 3.22/1.00      | sK2 != k1_xboole_0
% 3.22/1.00      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.22/1.00      inference(demodulation,[status(thm)],[c_8504,c_5]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_8582,plain,
% 3.22/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,sK2)) != k1_xboole_0
% 3.22/1.00      | sK2 != k1_xboole_0 ),
% 3.22/1.00      inference(backward_subsumption_resolution,
% 3.22/1.00                [status(thm)],
% 3.22/1.00                [c_8578,c_8567]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_8601,plain,
% 3.22/1.00      ( k1_relat_1(k7_relat_1(sK3,sK2)) != k1_xboole_0
% 3.22/1.00      | sK2 != k1_xboole_0 ),
% 3.22/1.00      inference(demodulation,[status(thm)],[c_8599,c_8582]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_7,plain,
% 3.22/1.00      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.22/1.00      | k1_xboole_0 = X0
% 3.22/1.00      | k1_xboole_0 = X1 ),
% 3.22/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_109,plain,
% 3.22/1.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.22/1.00      | k1_xboole_0 = k1_xboole_0 ),
% 3.22/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_110,plain,
% 3.22/1.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.22/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_0,plain,
% 3.22/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.22/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_2025,plain,
% 3.22/1.00      ( ~ r1_tarski(sK2,k1_xboole_0)
% 3.22/1.00      | ~ r1_tarski(k1_xboole_0,sK2)
% 3.22/1.00      | sK2 = k1_xboole_0 ),
% 3.22/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_1001,plain,( X0 = X0 ),theory(equality) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_2395,plain,
% 3.22/1.00      ( sK2 = sK2 ),
% 3.22/1.00      inference(instantiation,[status(thm)],[c_1001]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_1002,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_3024,plain,
% 3.22/1.00      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 3.22/1.00      inference(instantiation,[status(thm)],[c_1002]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_3025,plain,
% 3.22/1.00      ( sK1 != k1_xboole_0
% 3.22/1.00      | k1_xboole_0 = sK1
% 3.22/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.22/1.00      inference(instantiation,[status(thm)],[c_3024]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_1003,plain,
% 3.22/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.22/1.00      theory(equality) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_2308,plain,
% 3.22/1.00      ( ~ r1_tarski(X0,X1)
% 3.22/1.00      | r1_tarski(sK2,k1_xboole_0)
% 3.22/1.00      | sK2 != X0
% 3.22/1.00      | k1_xboole_0 != X1 ),
% 3.22/1.00      inference(instantiation,[status(thm)],[c_1003]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_3559,plain,
% 3.22/1.00      ( ~ r1_tarski(sK2,X0)
% 3.22/1.00      | r1_tarski(sK2,k1_xboole_0)
% 3.22/1.00      | sK2 != sK2
% 3.22/1.00      | k1_xboole_0 != X0 ),
% 3.22/1.00      inference(instantiation,[status(thm)],[c_2308]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_6889,plain,
% 3.22/1.00      ( ~ r1_tarski(sK2,sK0)
% 3.22/1.00      | r1_tarski(sK2,k1_xboole_0)
% 3.22/1.00      | sK2 != sK2
% 3.22/1.00      | k1_xboole_0 != sK0 ),
% 3.22/1.00      inference(instantiation,[status(thm)],[c_3559]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_3,plain,
% 3.22/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 3.22/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_7134,plain,
% 3.22/1.00      ( r1_tarski(k1_xboole_0,sK2) ),
% 3.22/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_9811,plain,
% 3.22/1.00      ( k1_relat_1(k7_relat_1(sK3,sK2)) != k1_xboole_0 ),
% 3.22/1.00      inference(global_propositional_subsumption,
% 3.22/1.00                [status(thm)],
% 3.22/1.00                [c_8601,c_33,c_32,c_109,c_110,c_2025,c_2395,c_3025,
% 3.22/1.00                 c_6889,c_7134,c_8495]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_8669,plain,
% 3.22/1.00      ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
% 3.22/1.00      inference(demodulation,[status(thm)],[c_8519,c_1701]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_4,plain,
% 3.22/1.00      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 3.22/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_1714,plain,
% 3.22/1.00      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.22/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_8682,plain,
% 3.22/1.00      ( sK2 = k1_xboole_0 ),
% 3.22/1.00      inference(superposition,[status(thm)],[c_8669,c_1714]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_9,plain,
% 3.22/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.22/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_1712,plain,
% 3.22/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.22/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.22/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_2813,plain,
% 3.22/1.00      ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 3.22/1.00      inference(superposition,[status(thm)],[c_1700,c_1712]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_8513,plain,
% 3.22/1.00      ( r1_tarski(sK3,k2_zfmisc_1(sK0,k1_xboole_0)) = iProver_top ),
% 3.22/1.00      inference(demodulation,[status(thm)],[c_8495,c_2813]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_8533,plain,
% 3.22/1.00      ( r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 3.22/1.00      inference(light_normalisation,[status(thm)],[c_8513,c_8519]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_8535,plain,
% 3.22/1.00      ( r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 3.22/1.00      inference(demodulation,[status(thm)],[c_8533,c_6]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_8873,plain,
% 3.22/1.00      ( sK3 = k1_xboole_0 ),
% 3.22/1.00      inference(superposition,[status(thm)],[c_8535,c_1714]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_9813,plain,
% 3.22/1.00      ( k1_relat_1(k7_relat_1(k1_xboole_0,k1_xboole_0)) != k1_xboole_0 ),
% 3.22/1.00      inference(light_normalisation,[status(thm)],[c_9811,c_8682,c_8873]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_14,plain,
% 3.22/1.00      ( r1_tarski(k7_relat_1(X0,X1),X0) | ~ v1_relat_1(X0) ),
% 3.22/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_1709,plain,
% 3.22/1.00      ( r1_tarski(k7_relat_1(X0,X1),X0) = iProver_top
% 3.22/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.22/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_2806,plain,
% 3.22/1.00      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0
% 3.22/1.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.22/1.00      inference(superposition,[status(thm)],[c_1709,c_1714]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_82,plain,
% 3.22/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.22/1.00      | v1_relat_1(X0) = iProver_top ),
% 3.22/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_84,plain,
% 3.22/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 3.22/1.00      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.22/1.00      inference(instantiation,[status(thm)],[c_82]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_8,plain,
% 3.22/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.22/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_1988,plain,
% 3.22/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.22/1.00      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
% 3.22/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_1989,plain,
% 3.22/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 3.22/1.00      | r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
% 3.22/1.00      inference(predicate_to_equality,[status(thm)],[c_1988]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_1991,plain,
% 3.22/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
% 3.22/1.00      | r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 3.22/1.00      inference(instantiation,[status(thm)],[c_1989]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_2184,plain,
% 3.22/1.00      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) ),
% 3.22/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_2187,plain,
% 3.22/1.00      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.22/1.00      inference(predicate_to_equality,[status(thm)],[c_2184]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_2189,plain,
% 3.22/1.00      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 3.22/1.00      inference(instantiation,[status(thm)],[c_2187]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_2951,plain,
% 3.22/1.00      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.22/1.00      inference(global_propositional_subsumption,
% 3.22/1.00                [status(thm)],
% 3.22/1.00                [c_2806,c_84,c_1991,c_2189]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_9814,plain,
% 3.22/1.00      ( k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
% 3.22/1.00      inference(demodulation,[status(thm)],[c_9813,c_2951]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_1715,plain,
% 3.22/1.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.22/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_4698,plain,
% 3.22/1.00      ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0
% 3.22/1.00      | sK1 = k1_xboole_0 ),
% 3.22/1.00      inference(superposition,[status(thm)],[c_1715,c_4689]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_2087,plain,
% 3.22/1.00      ( ~ r1_tarski(X0,k1_relat_1(sK3))
% 3.22/1.00      | ~ v1_relat_1(sK3)
% 3.22/1.00      | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
% 3.22/1.00      inference(instantiation,[status(thm)],[c_15]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_2089,plain,
% 3.22/1.00      ( ~ r1_tarski(k1_xboole_0,k1_relat_1(sK3))
% 3.22/1.00      | ~ v1_relat_1(sK3)
% 3.22/1.00      | k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
% 3.22/1.00      inference(instantiation,[status(thm)],[c_2087]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_2449,plain,
% 3.22/1.00      ( r1_tarski(k1_xboole_0,k1_relat_1(sK3)) ),
% 3.22/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_8145,plain,
% 3.22/1.00      ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
% 3.22/1.00      inference(global_propositional_subsumption,
% 3.22/1.00                [status(thm)],
% 3.22/1.00                [c_4698,c_34,c_1993,c_2089,c_2449]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_9601,plain,
% 3.22/1.00      ( k1_relat_1(k7_relat_1(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
% 3.22/1.00      inference(demodulation,[status(thm)],[c_8873,c_8145]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(c_9613,plain,
% 3.22/1.00      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.22/1.00      inference(demodulation,[status(thm)],[c_9601,c_2951]) ).
% 3.22/1.00  
% 3.22/1.00  cnf(contradiction,plain,
% 3.22/1.00      ( $false ),
% 3.22/1.00      inference(minisat,[status(thm)],[c_9814,c_9613]) ).
% 3.22/1.00  
% 3.22/1.00  
% 3.22/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.22/1.00  
% 3.22/1.00  ------                               Statistics
% 3.22/1.00  
% 3.22/1.00  ------ General
% 3.22/1.00  
% 3.22/1.00  abstr_ref_over_cycles:                  0
% 3.22/1.00  abstr_ref_under_cycles:                 0
% 3.22/1.00  gc_basic_clause_elim:                   0
% 3.22/1.00  forced_gc_time:                         0
% 3.22/1.00  parsing_time:                           0.008
% 3.22/1.00  unif_index_cands_time:                  0.
% 3.22/1.00  unif_index_add_time:                    0.
% 3.22/1.00  orderings_time:                         0.
% 3.22/1.00  out_proof_time:                         0.013
% 3.22/1.00  total_time:                             0.308
% 3.22/1.00  num_of_symbols:                         49
% 3.22/1.00  num_of_terms:                           9966
% 3.22/1.00  
% 3.22/1.00  ------ Preprocessing
% 3.22/1.00  
% 3.22/1.00  num_of_splits:                          0
% 3.22/1.00  num_of_split_atoms:                     0
% 3.22/1.00  num_of_reused_defs:                     0
% 3.22/1.00  num_eq_ax_congr_red:                    13
% 3.22/1.00  num_of_sem_filtered_clauses:            1
% 3.22/1.00  num_of_subtypes:                        0
% 3.22/1.00  monotx_restored_types:                  0
% 3.22/1.00  sat_num_of_epr_types:                   0
% 3.22/1.00  sat_num_of_non_cyclic_types:            0
% 3.22/1.00  sat_guarded_non_collapsed_types:        0
% 3.22/1.00  num_pure_diseq_elim:                    0
% 3.22/1.00  simp_replaced_by:                       0
% 3.22/1.00  res_preprocessed:                       163
% 3.22/1.00  prep_upred:                             0
% 3.22/1.00  prep_unflattend:                        43
% 3.22/1.00  smt_new_axioms:                         0
% 3.22/1.00  pred_elim_cands:                        4
% 3.22/1.00  pred_elim:                              2
% 3.22/1.00  pred_elim_cl:                           0
% 3.22/1.00  pred_elim_cycles:                       4
% 3.22/1.00  merged_defs:                            8
% 3.22/1.00  merged_defs_ncl:                        0
% 3.22/1.00  bin_hyper_res:                          8
% 3.22/1.00  prep_cycles:                            4
% 3.22/1.00  pred_elim_time:                         0.009
% 3.22/1.00  splitting_time:                         0.
% 3.22/1.00  sem_filter_time:                        0.
% 3.22/1.00  monotx_time:                            0.001
% 3.22/1.00  subtype_inf_time:                       0.
% 3.22/1.00  
% 3.22/1.00  ------ Problem properties
% 3.22/1.00  
% 3.22/1.00  clauses:                                35
% 3.22/1.00  conjectures:                            4
% 3.22/1.00  epr:                                    7
% 3.22/1.00  horn:                                   30
% 3.22/1.00  ground:                                 12
% 3.22/1.00  unary:                                  8
% 3.22/1.00  binary:                                 10
% 3.22/1.00  lits:                                   93
% 3.22/1.00  lits_eq:                                35
% 3.22/1.00  fd_pure:                                0
% 3.22/1.00  fd_pseudo:                              0
% 3.22/1.00  fd_cond:                                4
% 3.22/1.00  fd_pseudo_cond:                         1
% 3.22/1.00  ac_symbols:                             0
% 3.22/1.00  
% 3.22/1.00  ------ Propositional Solver
% 3.22/1.00  
% 3.22/1.00  prop_solver_calls:                      28
% 3.22/1.00  prop_fast_solver_calls:                 1238
% 3.22/1.00  smt_solver_calls:                       0
% 3.22/1.00  smt_fast_solver_calls:                  0
% 3.22/1.00  prop_num_of_clauses:                    3873
% 3.22/1.00  prop_preprocess_simplified:             10139
% 3.22/1.00  prop_fo_subsumed:                       27
% 3.22/1.00  prop_solver_time:                       0.
% 3.22/1.00  smt_solver_time:                        0.
% 3.22/1.00  smt_fast_solver_time:                   0.
% 3.22/1.00  prop_fast_solver_time:                  0.
% 3.22/1.00  prop_unsat_core_time:                   0.
% 3.22/1.00  
% 3.22/1.00  ------ QBF
% 3.22/1.00  
% 3.22/1.00  qbf_q_res:                              0
% 3.22/1.00  qbf_num_tautologies:                    0
% 3.22/1.00  qbf_prep_cycles:                        0
% 3.22/1.00  
% 3.22/1.00  ------ BMC1
% 3.22/1.00  
% 3.22/1.00  bmc1_current_bound:                     -1
% 3.22/1.00  bmc1_last_solved_bound:                 -1
% 3.22/1.00  bmc1_unsat_core_size:                   -1
% 3.22/1.00  bmc1_unsat_core_parents_size:           -1
% 3.22/1.00  bmc1_merge_next_fun:                    0
% 3.22/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.22/1.00  
% 3.22/1.00  ------ Instantiation
% 3.22/1.00  
% 3.22/1.00  inst_num_of_clauses:                    1056
% 3.22/1.00  inst_num_in_passive:                    358
% 3.22/1.00  inst_num_in_active:                     469
% 3.22/1.00  inst_num_in_unprocessed:                230
% 3.22/1.00  inst_num_of_loops:                      570
% 3.22/1.00  inst_num_of_learning_restarts:          0
% 3.22/1.00  inst_num_moves_active_passive:          99
% 3.22/1.00  inst_lit_activity:                      0
% 3.22/1.00  inst_lit_activity_moves:                0
% 3.22/1.00  inst_num_tautologies:                   0
% 3.22/1.00  inst_num_prop_implied:                  0
% 3.22/1.00  inst_num_existing_simplified:           0
% 3.22/1.00  inst_num_eq_res_simplified:             0
% 3.22/1.00  inst_num_child_elim:                    0
% 3.22/1.00  inst_num_of_dismatching_blockings:      443
% 3.22/1.00  inst_num_of_non_proper_insts:           1092
% 3.22/1.00  inst_num_of_duplicates:                 0
% 3.22/1.00  inst_inst_num_from_inst_to_res:         0
% 3.22/1.00  inst_dismatching_checking_time:         0.
% 3.22/1.00  
% 3.22/1.00  ------ Resolution
% 3.22/1.00  
% 3.22/1.00  res_num_of_clauses:                     0
% 3.22/1.00  res_num_in_passive:                     0
% 3.22/1.00  res_num_in_active:                      0
% 3.22/1.00  res_num_of_loops:                       167
% 3.22/1.00  res_forward_subset_subsumed:            41
% 3.22/1.00  res_backward_subset_subsumed:           2
% 3.22/1.00  res_forward_subsumed:                   0
% 3.22/1.00  res_backward_subsumed:                  0
% 3.22/1.00  res_forward_subsumption_resolution:     5
% 3.22/1.00  res_backward_subsumption_resolution:    0
% 3.22/1.00  res_clause_to_clause_subsumption:       559
% 3.22/1.00  res_orphan_elimination:                 0
% 3.22/1.00  res_tautology_del:                      62
% 3.22/1.00  res_num_eq_res_simplified:              1
% 3.22/1.00  res_num_sel_changes:                    0
% 3.22/1.00  res_moves_from_active_to_pass:          0
% 3.22/1.00  
% 3.22/1.00  ------ Superposition
% 3.22/1.00  
% 3.22/1.00  sup_time_total:                         0.
% 3.22/1.00  sup_time_generating:                    0.
% 3.22/1.00  sup_time_sim_full:                      0.
% 3.22/1.00  sup_time_sim_immed:                     0.
% 3.22/1.00  
% 3.22/1.00  sup_num_of_clauses:                     134
% 3.22/1.00  sup_num_in_active:                      52
% 3.22/1.00  sup_num_in_passive:                     82
% 3.22/1.00  sup_num_of_loops:                       112
% 3.22/1.00  sup_fw_superposition:                   93
% 3.22/1.00  sup_bw_superposition:                   111
% 3.22/1.00  sup_immediate_simplified:               69
% 3.22/1.00  sup_given_eliminated:                   4
% 3.22/1.00  comparisons_done:                       0
% 3.22/1.00  comparisons_avoided:                    22
% 3.22/1.00  
% 3.22/1.00  ------ Simplifications
% 3.22/1.00  
% 3.22/1.00  
% 3.22/1.00  sim_fw_subset_subsumed:                 18
% 3.22/1.00  sim_bw_subset_subsumed:                 19
% 3.22/1.00  sim_fw_subsumed:                        7
% 3.22/1.00  sim_bw_subsumed:                        0
% 3.22/1.00  sim_fw_subsumption_res:                 9
% 3.22/1.00  sim_bw_subsumption_res:                 3
% 3.22/1.00  sim_tautology_del:                      8
% 3.22/1.00  sim_eq_tautology_del:                   12
% 3.22/1.00  sim_eq_res_simp:                        3
% 3.22/1.00  sim_fw_demodulated:                     19
% 3.22/1.00  sim_bw_demodulated:                     62
% 3.22/1.00  sim_light_normalised:                   35
% 3.22/1.00  sim_joinable_taut:                      0
% 3.22/1.00  sim_joinable_simp:                      0
% 3.22/1.00  sim_ac_normalised:                      0
% 3.22/1.00  sim_smt_subsumption:                    0
% 3.22/1.00  
%------------------------------------------------------------------------------
