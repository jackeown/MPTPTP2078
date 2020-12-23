%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:53 EST 2020

% Result     : Theorem 3.59s
% Output     : CNFRefutation 3.59s
% Verified   : 
% Statistics : Number of formulae       :  236 (5196 expanded)
%              Number of clauses        :  155 (1720 expanded)
%              Number of leaves         :   20 ( 971 expanded)
%              Depth                    :   27
%              Number of atoms          :  697 (28462 expanded)
%              Number of equality atoms :  362 (7819 expanded)
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
    inference(ennf_transformation,[],[f19])).

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

fof(f48,plain,
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

fof(f49,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f40,f48])).

fof(f84,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f49])).

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
    inference(ennf_transformation,[],[f14])).

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

fof(f47,plain,(
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

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f82,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f83,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f49])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f10,axiom,(
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
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f80,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f16,axiom,(
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
    inference(ennf_transformation,[],[f16])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f81,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f15,axiom,(
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
    inference(ennf_transformation,[],[f15])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f86,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f49])).

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

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f85,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f49])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f43])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f90,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f91,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f74])).

fof(f92,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f91])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f89,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f58])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f41])).

fof(f52,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f94,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f72])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f87,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f51])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f4,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f55,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_33,negated_conjecture,
    ( r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2176,plain,
    ( r1_tarski(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_35,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_759,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X0
    | sK1 != X2
    | sK0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_35])).

cnf(c_760,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_759])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_762,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_760,c_34])).

cnf(c_2175,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2181,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4139,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2175,c_2181])).

cnf(c_4583,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_762,c_4139])).

cnf(c_15,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2183,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_5100,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4583,c_2183])).

cnf(c_39,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2468,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2469,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2468])).

cnf(c_5898,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | sK1 = k1_xboole_0
    | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5100,c_39,c_2469])).

cnf(c_5899,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5898])).

cnf(c_5910,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2176,c_5899])).

cnf(c_28,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2177,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_6007,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5910,c_2177])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2178,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_6195,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2175,c_2178])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2550,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_2732,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_2550])).

cnf(c_6319,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6195,c_36,c_34,c_2732])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2179,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_5352,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2175,c_2179])).

cnf(c_37,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_2526,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(k2_partfun1(X0,X1,sK3,X2))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_2646,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2526])).

cnf(c_2647,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2646])).

cnf(c_5571,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5352,c_37,c_39,c_2647])).

cnf(c_6328,plain,
    ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6319,c_5571])).

cnf(c_6840,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6007,c_6328])).

cnf(c_29,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_31,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_770,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_relat_1(X0)
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_relat_1(X0) != sK2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_31])).

cnf(c_771,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
    inference(unflattening,[status(thm)],[c_770])).

cnf(c_17,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_12,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_425,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_17,c_12])).

cnf(c_429,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_425,c_16])).

cnf(c_430,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_429])).

cnf(c_783,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_771,c_16,c_430])).

cnf(c_2164,plain,
    ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_783])).

cnf(c_6326,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6319,c_2164])).

cnf(c_6342,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6326,c_6328])).

cnf(c_9107,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5910,c_6342])).

cnf(c_9965,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6840,c_9107])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2180,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_7121,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6319,c_2180])).

cnf(c_7701,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7121,c_37,c_39])).

cnf(c_2182,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_7713,plain,
    ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7701,c_2182])).

cnf(c_2173,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_430])).

cnf(c_7712,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_7701,c_2173])).

cnf(c_11953,plain,
    ( sK1 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_9965,c_7713,c_7712])).

cnf(c_11981,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11953,c_7701])).

cnf(c_32,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_11998,plain,
    ( sK0 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_11953,c_32])).

cnf(c_11999,plain,
    ( sK0 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_11998])).

cnf(c_12057,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11981,c_11999])).

cnf(c_7,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_12059,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_12057,c_7])).

cnf(c_19,plain,
    ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_587,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK2 != X0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_31])).

cnf(c_588,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_587])).

cnf(c_2172,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_588])).

cnf(c_6,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2362,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2172,c_6])).

cnf(c_9,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_103,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_105,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_103])).

cnf(c_4,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_111,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_113,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_111])).

cnf(c_2728,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2646])).

cnf(c_2729,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2728])).

cnf(c_2842,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2362,c_37,c_39,c_105,c_113,c_2729])).

cnf(c_6324,plain,
    ( k7_relat_1(sK3,sK2) != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6319,c_2842])).

cnf(c_8,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_106,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_107,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_112,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2495,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK2)
    | sK2 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1478,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2777,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK0,k1_xboole_0)
    | sK0 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_1478])).

cnf(c_2779,plain,
    ( r1_tarski(sK0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | sK0 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2777])).

cnf(c_1477,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2514,plain,
    ( sK0 != X0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1477])).

cnf(c_2865,plain,
    ( sK0 != sK0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_2514])).

cnf(c_1476,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2866,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1476])).

cnf(c_3509,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1477])).

cnf(c_3510,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3509])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2763,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | ~ r1_tarski(sK2,X0)
    | r1_tarski(sK2,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3692,plain,
    ( ~ r1_tarski(sK2,sK0)
    | r1_tarski(sK2,k1_xboole_0)
    | ~ r1_tarski(sK0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2763])).

cnf(c_6576,plain,
    ( r1_tarski(k1_xboole_0,sK2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_6609,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6324,c_33,c_32,c_106,c_107,c_112,c_2495,c_2779,c_2865,c_2866,c_3510,c_3692,c_5910,c_6342,c_6576])).

cnf(c_11984,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11953,c_6609])).

cnf(c_12047,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11984,c_6])).

cnf(c_12061,plain,
    ( sK2 = k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_12059,c_12047])).

cnf(c_21,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_684,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | sK2 != k1_xboole_0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_31])).

cnf(c_685,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_684])).

cnf(c_2168,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_685])).

cnf(c_2375,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2168,c_7])).

cnf(c_2912,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | sK2 != k1_xboole_0
    | k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2375,c_37,c_39,c_2729])).

cnf(c_2913,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2912])).

cnf(c_6323,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k7_relat_1(sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6319,c_2913])).

cnf(c_6618,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k7_relat_1(sK3,sK2)) != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6323,c_6609])).

cnf(c_11983,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,sK2)) != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11953,c_6618])).

cnf(c_12053,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,sK2)) != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11983,c_6])).

cnf(c_12062,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,sK2)) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_12059,c_12053])).

cnf(c_12066,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_12061,c_12062])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2191,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2189,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_5908,plain,
    ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2189,c_5899])).

cnf(c_2555,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2557,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2555])).

cnf(c_2903,plain,
    ( r1_tarski(k1_xboole_0,k1_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_8804,plain,
    ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5908,c_34,c_2468,c_2557,c_2903])).

cnf(c_8808,plain,
    ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_xboole_0)),X0) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8804,c_2177])).

cnf(c_8820,plain,
    ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_xboole_0)),X0) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8808,c_7])).

cnf(c_6372,plain,
    ( v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_6328])).

cnf(c_7744,plain,
    ( v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_7713])).

cnf(c_9279,plain,
    ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_xboole_0)),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8820,c_6372,c_7744])).

cnf(c_9287,plain,
    ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2191,c_9279])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2186,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_9455,plain,
    ( r1_tarski(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_9287,c_2186])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2188,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_9495,plain,
    ( k7_relat_1(sK3,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9455,c_2188])).

cnf(c_12069,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_12066,c_9495])).

cnf(c_2187,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4141,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_2181])).

cnf(c_4247,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
    | r1_tarski(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2187,c_4141])).

cnf(c_4828,plain,
    ( k1_relset_1(k1_xboole_0,X0,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2191,c_4247])).

cnf(c_12070,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_12069,c_4828])).

cnf(c_9686,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9495,c_8804])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12070,c_9686])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:27:32 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.59/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.59/0.98  
% 3.59/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.59/0.98  
% 3.59/0.98  ------  iProver source info
% 3.59/0.98  
% 3.59/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.59/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.59/0.98  git: non_committed_changes: false
% 3.59/0.98  git: last_make_outside_of_git: false
% 3.59/0.98  
% 3.59/0.98  ------ 
% 3.59/0.98  
% 3.59/0.98  ------ Input Options
% 3.59/0.98  
% 3.59/0.98  --out_options                           all
% 3.59/0.98  --tptp_safe_out                         true
% 3.59/0.98  --problem_path                          ""
% 3.59/0.98  --include_path                          ""
% 3.59/0.98  --clausifier                            res/vclausify_rel
% 3.59/0.98  --clausifier_options                    --mode clausify
% 3.59/0.98  --stdin                                 false
% 3.59/0.98  --stats_out                             all
% 3.59/0.98  
% 3.59/0.98  ------ General Options
% 3.59/0.98  
% 3.59/0.98  --fof                                   false
% 3.59/0.98  --time_out_real                         305.
% 3.59/0.98  --time_out_virtual                      -1.
% 3.59/0.98  --symbol_type_check                     false
% 3.59/0.98  --clausify_out                          false
% 3.59/0.98  --sig_cnt_out                           false
% 3.59/0.98  --trig_cnt_out                          false
% 3.59/0.98  --trig_cnt_out_tolerance                1.
% 3.59/0.98  --trig_cnt_out_sk_spl                   false
% 3.59/0.98  --abstr_cl_out                          false
% 3.59/0.98  
% 3.59/0.98  ------ Global Options
% 3.59/0.98  
% 3.59/0.98  --schedule                              default
% 3.59/0.98  --add_important_lit                     false
% 3.59/0.98  --prop_solver_per_cl                    1000
% 3.59/0.98  --min_unsat_core                        false
% 3.59/0.98  --soft_assumptions                      false
% 3.59/0.98  --soft_lemma_size                       3
% 3.59/0.98  --prop_impl_unit_size                   0
% 3.59/0.98  --prop_impl_unit                        []
% 3.59/0.98  --share_sel_clauses                     true
% 3.59/0.98  --reset_solvers                         false
% 3.59/0.98  --bc_imp_inh                            [conj_cone]
% 3.59/0.98  --conj_cone_tolerance                   3.
% 3.59/0.98  --extra_neg_conj                        none
% 3.59/0.98  --large_theory_mode                     true
% 3.59/0.98  --prolific_symb_bound                   200
% 3.59/0.98  --lt_threshold                          2000
% 3.59/0.98  --clause_weak_htbl                      true
% 3.59/0.98  --gc_record_bc_elim                     false
% 3.59/0.98  
% 3.59/0.98  ------ Preprocessing Options
% 3.59/0.98  
% 3.59/0.98  --preprocessing_flag                    true
% 3.59/0.98  --time_out_prep_mult                    0.1
% 3.59/0.98  --splitting_mode                        input
% 3.59/0.98  --splitting_grd                         true
% 3.59/0.98  --splitting_cvd                         false
% 3.59/0.98  --splitting_cvd_svl                     false
% 3.59/0.98  --splitting_nvd                         32
% 3.59/0.98  --sub_typing                            true
% 3.59/0.98  --prep_gs_sim                           true
% 3.59/0.98  --prep_unflatten                        true
% 3.59/0.98  --prep_res_sim                          true
% 3.59/0.98  --prep_upred                            true
% 3.59/0.98  --prep_sem_filter                       exhaustive
% 3.59/0.98  --prep_sem_filter_out                   false
% 3.59/0.98  --pred_elim                             true
% 3.59/0.98  --res_sim_input                         true
% 3.59/0.98  --eq_ax_congr_red                       true
% 3.59/0.98  --pure_diseq_elim                       true
% 3.59/0.98  --brand_transform                       false
% 3.59/0.98  --non_eq_to_eq                          false
% 3.59/0.98  --prep_def_merge                        true
% 3.59/0.98  --prep_def_merge_prop_impl              false
% 3.59/0.98  --prep_def_merge_mbd                    true
% 3.59/0.98  --prep_def_merge_tr_red                 false
% 3.59/0.98  --prep_def_merge_tr_cl                  false
% 3.59/0.98  --smt_preprocessing                     true
% 3.59/0.98  --smt_ac_axioms                         fast
% 3.59/0.98  --preprocessed_out                      false
% 3.59/0.98  --preprocessed_stats                    false
% 3.59/0.98  
% 3.59/0.98  ------ Abstraction refinement Options
% 3.59/0.98  
% 3.59/0.98  --abstr_ref                             []
% 3.59/0.98  --abstr_ref_prep                        false
% 3.59/0.98  --abstr_ref_until_sat                   false
% 3.59/0.98  --abstr_ref_sig_restrict                funpre
% 3.59/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.59/0.98  --abstr_ref_under                       []
% 3.59/0.98  
% 3.59/0.98  ------ SAT Options
% 3.59/0.98  
% 3.59/0.98  --sat_mode                              false
% 3.59/0.98  --sat_fm_restart_options                ""
% 3.59/0.98  --sat_gr_def                            false
% 3.59/0.98  --sat_epr_types                         true
% 3.59/0.98  --sat_non_cyclic_types                  false
% 3.59/0.98  --sat_finite_models                     false
% 3.59/0.98  --sat_fm_lemmas                         false
% 3.59/0.98  --sat_fm_prep                           false
% 3.59/0.98  --sat_fm_uc_incr                        true
% 3.59/0.98  --sat_out_model                         small
% 3.59/0.98  --sat_out_clauses                       false
% 3.59/0.98  
% 3.59/0.98  ------ QBF Options
% 3.59/0.98  
% 3.59/0.98  --qbf_mode                              false
% 3.59/0.98  --qbf_elim_univ                         false
% 3.59/0.98  --qbf_dom_inst                          none
% 3.59/0.98  --qbf_dom_pre_inst                      false
% 3.59/0.98  --qbf_sk_in                             false
% 3.59/0.98  --qbf_pred_elim                         true
% 3.59/0.98  --qbf_split                             512
% 3.59/0.98  
% 3.59/0.98  ------ BMC1 Options
% 3.59/0.98  
% 3.59/0.98  --bmc1_incremental                      false
% 3.59/0.98  --bmc1_axioms                           reachable_all
% 3.59/0.98  --bmc1_min_bound                        0
% 3.59/0.98  --bmc1_max_bound                        -1
% 3.59/0.98  --bmc1_max_bound_default                -1
% 3.59/0.98  --bmc1_symbol_reachability              true
% 3.59/0.98  --bmc1_property_lemmas                  false
% 3.59/0.98  --bmc1_k_induction                      false
% 3.59/0.98  --bmc1_non_equiv_states                 false
% 3.59/0.98  --bmc1_deadlock                         false
% 3.59/0.98  --bmc1_ucm                              false
% 3.59/0.98  --bmc1_add_unsat_core                   none
% 3.59/0.98  --bmc1_unsat_core_children              false
% 3.59/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.59/0.98  --bmc1_out_stat                         full
% 3.59/0.98  --bmc1_ground_init                      false
% 3.59/0.98  --bmc1_pre_inst_next_state              false
% 3.59/0.98  --bmc1_pre_inst_state                   false
% 3.59/0.98  --bmc1_pre_inst_reach_state             false
% 3.59/0.98  --bmc1_out_unsat_core                   false
% 3.59/0.98  --bmc1_aig_witness_out                  false
% 3.59/0.98  --bmc1_verbose                          false
% 3.59/0.98  --bmc1_dump_clauses_tptp                false
% 3.59/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.59/0.98  --bmc1_dump_file                        -
% 3.59/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.59/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.59/0.98  --bmc1_ucm_extend_mode                  1
% 3.59/0.98  --bmc1_ucm_init_mode                    2
% 3.59/0.98  --bmc1_ucm_cone_mode                    none
% 3.59/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.59/0.98  --bmc1_ucm_relax_model                  4
% 3.59/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.59/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.59/0.98  --bmc1_ucm_layered_model                none
% 3.59/0.98  --bmc1_ucm_max_lemma_size               10
% 3.59/0.98  
% 3.59/0.98  ------ AIG Options
% 3.59/0.98  
% 3.59/0.98  --aig_mode                              false
% 3.59/0.98  
% 3.59/0.98  ------ Instantiation Options
% 3.59/0.98  
% 3.59/0.98  --instantiation_flag                    true
% 3.59/0.98  --inst_sos_flag                         false
% 3.59/0.98  --inst_sos_phase                        true
% 3.59/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.59/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.59/0.98  --inst_lit_sel_side                     num_symb
% 3.59/0.98  --inst_solver_per_active                1400
% 3.59/0.98  --inst_solver_calls_frac                1.
% 3.59/0.98  --inst_passive_queue_type               priority_queues
% 3.59/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.59/0.98  --inst_passive_queues_freq              [25;2]
% 3.59/0.98  --inst_dismatching                      true
% 3.59/0.98  --inst_eager_unprocessed_to_passive     true
% 3.59/0.98  --inst_prop_sim_given                   true
% 3.59/0.98  --inst_prop_sim_new                     false
% 3.59/0.98  --inst_subs_new                         false
% 3.59/0.98  --inst_eq_res_simp                      false
% 3.59/0.98  --inst_subs_given                       false
% 3.59/0.98  --inst_orphan_elimination               true
% 3.59/0.98  --inst_learning_loop_flag               true
% 3.59/0.98  --inst_learning_start                   3000
% 3.59/0.98  --inst_learning_factor                  2
% 3.59/0.98  --inst_start_prop_sim_after_learn       3
% 3.59/0.98  --inst_sel_renew                        solver
% 3.59/0.98  --inst_lit_activity_flag                true
% 3.59/0.98  --inst_restr_to_given                   false
% 3.59/0.98  --inst_activity_threshold               500
% 3.59/0.98  --inst_out_proof                        true
% 3.59/0.98  
% 3.59/0.98  ------ Resolution Options
% 3.59/0.98  
% 3.59/0.98  --resolution_flag                       true
% 3.59/0.98  --res_lit_sel                           adaptive
% 3.59/0.98  --res_lit_sel_side                      none
% 3.59/0.98  --res_ordering                          kbo
% 3.59/0.98  --res_to_prop_solver                    active
% 3.59/0.98  --res_prop_simpl_new                    false
% 3.59/0.98  --res_prop_simpl_given                  true
% 3.59/0.98  --res_passive_queue_type                priority_queues
% 3.59/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.59/0.98  --res_passive_queues_freq               [15;5]
% 3.59/0.98  --res_forward_subs                      full
% 3.59/0.98  --res_backward_subs                     full
% 3.59/0.98  --res_forward_subs_resolution           true
% 3.59/0.98  --res_backward_subs_resolution          true
% 3.59/0.98  --res_orphan_elimination                true
% 3.59/0.98  --res_time_limit                        2.
% 3.59/0.98  --res_out_proof                         true
% 3.59/0.98  
% 3.59/0.98  ------ Superposition Options
% 3.59/0.98  
% 3.59/0.98  --superposition_flag                    true
% 3.59/0.98  --sup_passive_queue_type                priority_queues
% 3.59/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.59/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.59/0.98  --demod_completeness_check              fast
% 3.59/0.98  --demod_use_ground                      true
% 3.59/0.98  --sup_to_prop_solver                    passive
% 3.59/0.98  --sup_prop_simpl_new                    true
% 3.59/0.98  --sup_prop_simpl_given                  true
% 3.59/0.98  --sup_fun_splitting                     false
% 3.59/0.98  --sup_smt_interval                      50000
% 3.59/0.98  
% 3.59/0.98  ------ Superposition Simplification Setup
% 3.59/0.98  
% 3.59/0.98  --sup_indices_passive                   []
% 3.59/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.59/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.59/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.59/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.59/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.59/0.98  --sup_full_bw                           [BwDemod]
% 3.59/0.98  --sup_immed_triv                        [TrivRules]
% 3.59/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.59/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.59/0.98  --sup_immed_bw_main                     []
% 3.59/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.59/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.59/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.59/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.59/0.98  
% 3.59/0.98  ------ Combination Options
% 3.59/0.98  
% 3.59/0.98  --comb_res_mult                         3
% 3.59/0.98  --comb_sup_mult                         2
% 3.59/0.98  --comb_inst_mult                        10
% 3.59/0.98  
% 3.59/0.98  ------ Debug Options
% 3.59/0.98  
% 3.59/0.98  --dbg_backtrace                         false
% 3.59/0.98  --dbg_dump_prop_clauses                 false
% 3.59/0.98  --dbg_dump_prop_clauses_file            -
% 3.59/0.98  --dbg_out_stat                          false
% 3.59/0.98  ------ Parsing...
% 3.59/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.59/0.98  
% 3.59/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.59/0.98  
% 3.59/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.59/0.98  
% 3.59/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.59/0.98  ------ Proving...
% 3.59/0.98  ------ Problem Properties 
% 3.59/0.98  
% 3.59/0.98  
% 3.59/0.98  clauses                                 35
% 3.59/0.98  conjectures                             4
% 3.59/0.98  EPR                                     8
% 3.59/0.98  Horn                                    30
% 3.59/0.98  unary                                   8
% 3.59/0.98  binary                                  9
% 3.59/0.98  lits                                    94
% 3.59/0.98  lits eq                                 35
% 3.59/0.98  fd_pure                                 0
% 3.59/0.98  fd_pseudo                               0
% 3.59/0.98  fd_cond                                 4
% 3.59/0.98  fd_pseudo_cond                          1
% 3.59/0.98  AC symbols                              0
% 3.59/0.98  
% 3.59/0.98  ------ Schedule dynamic 5 is on 
% 3.59/0.98  
% 3.59/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.59/0.98  
% 3.59/0.98  
% 3.59/0.98  ------ 
% 3.59/0.98  Current options:
% 3.59/0.98  ------ 
% 3.59/0.98  
% 3.59/0.98  ------ Input Options
% 3.59/0.98  
% 3.59/0.98  --out_options                           all
% 3.59/0.98  --tptp_safe_out                         true
% 3.59/0.98  --problem_path                          ""
% 3.59/0.98  --include_path                          ""
% 3.59/0.98  --clausifier                            res/vclausify_rel
% 3.59/0.98  --clausifier_options                    --mode clausify
% 3.59/0.98  --stdin                                 false
% 3.59/0.98  --stats_out                             all
% 3.59/0.98  
% 3.59/0.98  ------ General Options
% 3.59/0.98  
% 3.59/0.98  --fof                                   false
% 3.59/0.98  --time_out_real                         305.
% 3.59/0.98  --time_out_virtual                      -1.
% 3.59/0.98  --symbol_type_check                     false
% 3.59/0.98  --clausify_out                          false
% 3.59/0.98  --sig_cnt_out                           false
% 3.59/0.98  --trig_cnt_out                          false
% 3.59/0.98  --trig_cnt_out_tolerance                1.
% 3.59/0.98  --trig_cnt_out_sk_spl                   false
% 3.59/0.98  --abstr_cl_out                          false
% 3.59/0.98  
% 3.59/0.98  ------ Global Options
% 3.59/0.98  
% 3.59/0.98  --schedule                              default
% 3.59/0.98  --add_important_lit                     false
% 3.59/0.98  --prop_solver_per_cl                    1000
% 3.59/0.98  --min_unsat_core                        false
% 3.59/0.98  --soft_assumptions                      false
% 3.59/0.98  --soft_lemma_size                       3
% 3.59/0.98  --prop_impl_unit_size                   0
% 3.59/0.98  --prop_impl_unit                        []
% 3.59/0.98  --share_sel_clauses                     true
% 3.59/0.98  --reset_solvers                         false
% 3.59/0.98  --bc_imp_inh                            [conj_cone]
% 3.59/0.98  --conj_cone_tolerance                   3.
% 3.59/0.98  --extra_neg_conj                        none
% 3.59/0.98  --large_theory_mode                     true
% 3.59/0.98  --prolific_symb_bound                   200
% 3.59/0.98  --lt_threshold                          2000
% 3.59/0.98  --clause_weak_htbl                      true
% 3.59/0.98  --gc_record_bc_elim                     false
% 3.59/0.98  
% 3.59/0.98  ------ Preprocessing Options
% 3.59/0.98  
% 3.59/0.98  --preprocessing_flag                    true
% 3.59/0.98  --time_out_prep_mult                    0.1
% 3.59/0.98  --splitting_mode                        input
% 3.59/0.98  --splitting_grd                         true
% 3.59/0.98  --splitting_cvd                         false
% 3.59/0.98  --splitting_cvd_svl                     false
% 3.59/0.98  --splitting_nvd                         32
% 3.59/0.98  --sub_typing                            true
% 3.59/0.98  --prep_gs_sim                           true
% 3.59/0.98  --prep_unflatten                        true
% 3.59/0.98  --prep_res_sim                          true
% 3.59/0.98  --prep_upred                            true
% 3.59/0.98  --prep_sem_filter                       exhaustive
% 3.59/0.98  --prep_sem_filter_out                   false
% 3.59/0.98  --pred_elim                             true
% 3.59/0.98  --res_sim_input                         true
% 3.59/0.98  --eq_ax_congr_red                       true
% 3.59/0.98  --pure_diseq_elim                       true
% 3.59/0.98  --brand_transform                       false
% 3.59/0.98  --non_eq_to_eq                          false
% 3.59/0.98  --prep_def_merge                        true
% 3.59/0.98  --prep_def_merge_prop_impl              false
% 3.59/0.98  --prep_def_merge_mbd                    true
% 3.59/0.98  --prep_def_merge_tr_red                 false
% 3.59/0.98  --prep_def_merge_tr_cl                  false
% 3.59/0.98  --smt_preprocessing                     true
% 3.59/0.98  --smt_ac_axioms                         fast
% 3.59/0.98  --preprocessed_out                      false
% 3.59/0.98  --preprocessed_stats                    false
% 3.59/0.98  
% 3.59/0.98  ------ Abstraction refinement Options
% 3.59/0.98  
% 3.59/0.98  --abstr_ref                             []
% 3.59/0.98  --abstr_ref_prep                        false
% 3.59/0.98  --abstr_ref_until_sat                   false
% 3.59/0.98  --abstr_ref_sig_restrict                funpre
% 3.59/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.59/0.98  --abstr_ref_under                       []
% 3.59/0.98  
% 3.59/0.98  ------ SAT Options
% 3.59/0.98  
% 3.59/0.98  --sat_mode                              false
% 3.59/0.98  --sat_fm_restart_options                ""
% 3.59/0.98  --sat_gr_def                            false
% 3.59/0.98  --sat_epr_types                         true
% 3.59/0.98  --sat_non_cyclic_types                  false
% 3.59/0.98  --sat_finite_models                     false
% 3.59/0.98  --sat_fm_lemmas                         false
% 3.59/0.98  --sat_fm_prep                           false
% 3.59/0.98  --sat_fm_uc_incr                        true
% 3.59/0.98  --sat_out_model                         small
% 3.59/0.98  --sat_out_clauses                       false
% 3.59/0.98  
% 3.59/0.98  ------ QBF Options
% 3.59/0.98  
% 3.59/0.98  --qbf_mode                              false
% 3.59/0.98  --qbf_elim_univ                         false
% 3.59/0.98  --qbf_dom_inst                          none
% 3.59/0.98  --qbf_dom_pre_inst                      false
% 3.59/0.98  --qbf_sk_in                             false
% 3.59/0.98  --qbf_pred_elim                         true
% 3.59/0.98  --qbf_split                             512
% 3.59/0.98  
% 3.59/0.98  ------ BMC1 Options
% 3.59/0.98  
% 3.59/0.98  --bmc1_incremental                      false
% 3.59/0.98  --bmc1_axioms                           reachable_all
% 3.59/0.98  --bmc1_min_bound                        0
% 3.59/0.98  --bmc1_max_bound                        -1
% 3.59/0.98  --bmc1_max_bound_default                -1
% 3.59/0.98  --bmc1_symbol_reachability              true
% 3.59/0.98  --bmc1_property_lemmas                  false
% 3.59/0.98  --bmc1_k_induction                      false
% 3.59/0.98  --bmc1_non_equiv_states                 false
% 3.59/0.98  --bmc1_deadlock                         false
% 3.59/0.98  --bmc1_ucm                              false
% 3.59/0.98  --bmc1_add_unsat_core                   none
% 3.59/0.98  --bmc1_unsat_core_children              false
% 3.59/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.59/0.98  --bmc1_out_stat                         full
% 3.59/0.98  --bmc1_ground_init                      false
% 3.59/0.98  --bmc1_pre_inst_next_state              false
% 3.59/0.98  --bmc1_pre_inst_state                   false
% 3.59/0.98  --bmc1_pre_inst_reach_state             false
% 3.59/0.98  --bmc1_out_unsat_core                   false
% 3.59/0.98  --bmc1_aig_witness_out                  false
% 3.59/0.98  --bmc1_verbose                          false
% 3.59/0.98  --bmc1_dump_clauses_tptp                false
% 3.59/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.59/0.98  --bmc1_dump_file                        -
% 3.59/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.59/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.59/0.98  --bmc1_ucm_extend_mode                  1
% 3.59/0.98  --bmc1_ucm_init_mode                    2
% 3.59/0.98  --bmc1_ucm_cone_mode                    none
% 3.59/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.59/0.98  --bmc1_ucm_relax_model                  4
% 3.59/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.59/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.59/0.98  --bmc1_ucm_layered_model                none
% 3.59/0.98  --bmc1_ucm_max_lemma_size               10
% 3.59/0.98  
% 3.59/0.98  ------ AIG Options
% 3.59/0.98  
% 3.59/0.98  --aig_mode                              false
% 3.59/0.98  
% 3.59/0.98  ------ Instantiation Options
% 3.59/0.98  
% 3.59/0.98  --instantiation_flag                    true
% 3.59/0.98  --inst_sos_flag                         false
% 3.59/0.98  --inst_sos_phase                        true
% 3.59/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.59/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.59/0.98  --inst_lit_sel_side                     none
% 3.59/0.98  --inst_solver_per_active                1400
% 3.59/0.98  --inst_solver_calls_frac                1.
% 3.59/0.98  --inst_passive_queue_type               priority_queues
% 3.59/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.59/0.98  --inst_passive_queues_freq              [25;2]
% 3.59/0.98  --inst_dismatching                      true
% 3.59/0.98  --inst_eager_unprocessed_to_passive     true
% 3.59/0.98  --inst_prop_sim_given                   true
% 3.59/0.98  --inst_prop_sim_new                     false
% 3.59/0.98  --inst_subs_new                         false
% 3.59/0.98  --inst_eq_res_simp                      false
% 3.59/0.98  --inst_subs_given                       false
% 3.59/0.98  --inst_orphan_elimination               true
% 3.59/0.98  --inst_learning_loop_flag               true
% 3.59/0.98  --inst_learning_start                   3000
% 3.59/0.98  --inst_learning_factor                  2
% 3.59/0.98  --inst_start_prop_sim_after_learn       3
% 3.59/0.98  --inst_sel_renew                        solver
% 3.59/0.98  --inst_lit_activity_flag                true
% 3.59/0.98  --inst_restr_to_given                   false
% 3.59/0.98  --inst_activity_threshold               500
% 3.59/0.98  --inst_out_proof                        true
% 3.59/0.98  
% 3.59/0.98  ------ Resolution Options
% 3.59/0.98  
% 3.59/0.98  --resolution_flag                       false
% 3.59/0.98  --res_lit_sel                           adaptive
% 3.59/0.98  --res_lit_sel_side                      none
% 3.59/0.98  --res_ordering                          kbo
% 3.59/0.98  --res_to_prop_solver                    active
% 3.59/0.98  --res_prop_simpl_new                    false
% 3.59/0.98  --res_prop_simpl_given                  true
% 3.59/0.98  --res_passive_queue_type                priority_queues
% 3.59/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.59/0.98  --res_passive_queues_freq               [15;5]
% 3.59/0.98  --res_forward_subs                      full
% 3.59/0.98  --res_backward_subs                     full
% 3.59/0.98  --res_forward_subs_resolution           true
% 3.59/0.98  --res_backward_subs_resolution          true
% 3.59/0.98  --res_orphan_elimination                true
% 3.59/0.98  --res_time_limit                        2.
% 3.59/0.98  --res_out_proof                         true
% 3.59/0.98  
% 3.59/0.98  ------ Superposition Options
% 3.59/0.98  
% 3.59/0.98  --superposition_flag                    true
% 3.59/0.98  --sup_passive_queue_type                priority_queues
% 3.59/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.59/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.59/0.98  --demod_completeness_check              fast
% 3.59/0.98  --demod_use_ground                      true
% 3.59/0.98  --sup_to_prop_solver                    passive
% 3.59/0.98  --sup_prop_simpl_new                    true
% 3.59/0.98  --sup_prop_simpl_given                  true
% 3.59/0.98  --sup_fun_splitting                     false
% 3.59/0.98  --sup_smt_interval                      50000
% 3.59/0.98  
% 3.59/0.98  ------ Superposition Simplification Setup
% 3.59/0.98  
% 3.59/0.98  --sup_indices_passive                   []
% 3.59/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.59/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.59/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.59/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.59/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.59/0.98  --sup_full_bw                           [BwDemod]
% 3.59/0.98  --sup_immed_triv                        [TrivRules]
% 3.59/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.59/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.59/0.98  --sup_immed_bw_main                     []
% 3.59/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.59/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.59/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.59/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.59/0.98  
% 3.59/0.98  ------ Combination Options
% 3.59/0.98  
% 3.59/0.98  --comb_res_mult                         3
% 3.59/0.98  --comb_sup_mult                         2
% 3.59/0.98  --comb_inst_mult                        10
% 3.59/0.98  
% 3.59/0.98  ------ Debug Options
% 3.59/0.98  
% 3.59/0.98  --dbg_backtrace                         false
% 3.59/0.98  --dbg_dump_prop_clauses                 false
% 3.59/0.98  --dbg_dump_prop_clauses_file            -
% 3.59/0.98  --dbg_out_stat                          false
% 3.59/0.98  
% 3.59/0.98  
% 3.59/0.98  
% 3.59/0.98  
% 3.59/0.98  ------ Proving...
% 3.59/0.98  
% 3.59/0.98  
% 3.59/0.98  % SZS status Theorem for theBenchmark.p
% 3.59/0.98  
% 3.59/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.59/0.98  
% 3.59/0.98  fof(f18,conjecture,(
% 3.59/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f19,negated_conjecture,(
% 3.59/0.98    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.59/0.98    inference(negated_conjecture,[],[f18])).
% 3.59/0.98  
% 3.59/0.98  fof(f39,plain,(
% 3.59/0.98    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.59/0.98    inference(ennf_transformation,[],[f19])).
% 3.59/0.98  
% 3.59/0.98  fof(f40,plain,(
% 3.59/0.98    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.59/0.98    inference(flattening,[],[f39])).
% 3.59/0.98  
% 3.59/0.98  fof(f48,plain,(
% 3.59/0.98    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 3.59/0.98    introduced(choice_axiom,[])).
% 3.59/0.98  
% 3.59/0.98  fof(f49,plain,(
% 3.59/0.98    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 3.59/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f40,f48])).
% 3.59/0.98  
% 3.59/0.98  fof(f84,plain,(
% 3.59/0.98    r1_tarski(sK2,sK0)),
% 3.59/0.98    inference(cnf_transformation,[],[f49])).
% 3.59/0.98  
% 3.59/0.98  fof(f14,axiom,(
% 3.59/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f31,plain,(
% 3.59/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.59/0.98    inference(ennf_transformation,[],[f14])).
% 3.59/0.98  
% 3.59/0.98  fof(f32,plain,(
% 3.59/0.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.59/0.98    inference(flattening,[],[f31])).
% 3.59/0.98  
% 3.59/0.98  fof(f47,plain,(
% 3.59/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.59/0.98    inference(nnf_transformation,[],[f32])).
% 3.59/0.98  
% 3.59/0.98  fof(f69,plain,(
% 3.59/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.59/0.98    inference(cnf_transformation,[],[f47])).
% 3.59/0.98  
% 3.59/0.98  fof(f82,plain,(
% 3.59/0.98    v1_funct_2(sK3,sK0,sK1)),
% 3.59/0.98    inference(cnf_transformation,[],[f49])).
% 3.59/0.98  
% 3.59/0.98  fof(f83,plain,(
% 3.59/0.98    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.59/0.98    inference(cnf_transformation,[],[f49])).
% 3.59/0.98  
% 3.59/0.98  fof(f13,axiom,(
% 3.59/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f30,plain,(
% 3.59/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.59/0.98    inference(ennf_transformation,[],[f13])).
% 3.59/0.98  
% 3.59/0.98  fof(f68,plain,(
% 3.59/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.59/0.98    inference(cnf_transformation,[],[f30])).
% 3.59/0.98  
% 3.59/0.98  fof(f10,axiom,(
% 3.59/0.98    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 3.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f26,plain,(
% 3.59/0.98    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 3.59/0.98    inference(ennf_transformation,[],[f10])).
% 3.59/0.98  
% 3.59/0.98  fof(f27,plain,(
% 3.59/0.98    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.59/0.98    inference(flattening,[],[f26])).
% 3.59/0.98  
% 3.59/0.98  fof(f65,plain,(
% 3.59/0.98    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.59/0.98    inference(cnf_transformation,[],[f27])).
% 3.59/0.98  
% 3.59/0.98  fof(f11,axiom,(
% 3.59/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f28,plain,(
% 3.59/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.59/0.98    inference(ennf_transformation,[],[f11])).
% 3.59/0.98  
% 3.59/0.98  fof(f66,plain,(
% 3.59/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.59/0.98    inference(cnf_transformation,[],[f28])).
% 3.59/0.98  
% 3.59/0.98  fof(f17,axiom,(
% 3.59/0.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 3.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f37,plain,(
% 3.59/0.98    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.59/0.98    inference(ennf_transformation,[],[f17])).
% 3.59/0.98  
% 3.59/0.98  fof(f38,plain,(
% 3.59/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.59/0.98    inference(flattening,[],[f37])).
% 3.59/0.98  
% 3.59/0.98  fof(f80,plain,(
% 3.59/0.98    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.59/0.98    inference(cnf_transformation,[],[f38])).
% 3.59/0.98  
% 3.59/0.98  fof(f16,axiom,(
% 3.59/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 3.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f35,plain,(
% 3.59/0.98    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.59/0.98    inference(ennf_transformation,[],[f16])).
% 3.59/0.98  
% 3.59/0.98  fof(f36,plain,(
% 3.59/0.98    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.59/0.98    inference(flattening,[],[f35])).
% 3.59/0.98  
% 3.59/0.98  fof(f77,plain,(
% 3.59/0.98    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.59/0.98    inference(cnf_transformation,[],[f36])).
% 3.59/0.98  
% 3.59/0.98  fof(f81,plain,(
% 3.59/0.98    v1_funct_1(sK3)),
% 3.59/0.98    inference(cnf_transformation,[],[f49])).
% 3.59/0.98  
% 3.59/0.98  fof(f15,axiom,(
% 3.59/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 3.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f33,plain,(
% 3.59/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.59/0.98    inference(ennf_transformation,[],[f15])).
% 3.59/0.98  
% 3.59/0.98  fof(f34,plain,(
% 3.59/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.59/0.98    inference(flattening,[],[f33])).
% 3.59/0.98  
% 3.59/0.98  fof(f75,plain,(
% 3.59/0.98    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.59/0.98    inference(cnf_transformation,[],[f34])).
% 3.59/0.98  
% 3.59/0.98  fof(f79,plain,(
% 3.59/0.98    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.59/0.98    inference(cnf_transformation,[],[f38])).
% 3.59/0.98  
% 3.59/0.98  fof(f86,plain,(
% 3.59/0.98    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 3.59/0.98    inference(cnf_transformation,[],[f49])).
% 3.59/0.98  
% 3.59/0.98  fof(f12,axiom,(
% 3.59/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f20,plain,(
% 3.59/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.59/0.98    inference(pure_predicate_removal,[],[f12])).
% 3.59/0.98  
% 3.59/0.98  fof(f29,plain,(
% 3.59/0.98    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.59/0.98    inference(ennf_transformation,[],[f20])).
% 3.59/0.98  
% 3.59/0.98  fof(f67,plain,(
% 3.59/0.98    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.59/0.98    inference(cnf_transformation,[],[f29])).
% 3.59/0.98  
% 3.59/0.98  fof(f7,axiom,(
% 3.59/0.98    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f24,plain,(
% 3.59/0.98    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.59/0.98    inference(ennf_transformation,[],[f7])).
% 3.59/0.98  
% 3.59/0.98  fof(f46,plain,(
% 3.59/0.98    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.59/0.98    inference(nnf_transformation,[],[f24])).
% 3.59/0.98  
% 3.59/0.98  fof(f61,plain,(
% 3.59/0.98    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.59/0.98    inference(cnf_transformation,[],[f46])).
% 3.59/0.98  
% 3.59/0.98  fof(f76,plain,(
% 3.59/0.98    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.59/0.98    inference(cnf_transformation,[],[f34])).
% 3.59/0.98  
% 3.59/0.98  fof(f85,plain,(
% 3.59/0.98    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 3.59/0.98    inference(cnf_transformation,[],[f49])).
% 3.59/0.98  
% 3.59/0.98  fof(f5,axiom,(
% 3.59/0.98    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f43,plain,(
% 3.59/0.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.59/0.98    inference(nnf_transformation,[],[f5])).
% 3.59/0.98  
% 3.59/0.98  fof(f44,plain,(
% 3.59/0.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.59/0.98    inference(flattening,[],[f43])).
% 3.59/0.98  
% 3.59/0.98  fof(f57,plain,(
% 3.59/0.98    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.59/0.98    inference(cnf_transformation,[],[f44])).
% 3.59/0.98  
% 3.59/0.98  fof(f90,plain,(
% 3.59/0.98    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.59/0.98    inference(equality_resolution,[],[f57])).
% 3.59/0.98  
% 3.59/0.98  fof(f74,plain,(
% 3.59/0.98    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.59/0.98    inference(cnf_transformation,[],[f47])).
% 3.59/0.98  
% 3.59/0.98  fof(f91,plain,(
% 3.59/0.98    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.59/0.98    inference(equality_resolution,[],[f74])).
% 3.59/0.98  
% 3.59/0.98  fof(f92,plain,(
% 3.59/0.98    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.59/0.98    inference(equality_resolution,[],[f91])).
% 3.59/0.98  
% 3.59/0.98  fof(f58,plain,(
% 3.59/0.98    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.59/0.98    inference(cnf_transformation,[],[f44])).
% 3.59/0.98  
% 3.59/0.98  fof(f89,plain,(
% 3.59/0.98    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.59/0.98    inference(equality_resolution,[],[f58])).
% 3.59/0.98  
% 3.59/0.98  fof(f6,axiom,(
% 3.59/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f45,plain,(
% 3.59/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.59/0.98    inference(nnf_transformation,[],[f6])).
% 3.59/0.98  
% 3.59/0.98  fof(f60,plain,(
% 3.59/0.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.59/0.98    inference(cnf_transformation,[],[f45])).
% 3.59/0.98  
% 3.59/0.98  fof(f3,axiom,(
% 3.59/0.98    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f54,plain,(
% 3.59/0.98    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.59/0.98    inference(cnf_transformation,[],[f3])).
% 3.59/0.98  
% 3.59/0.98  fof(f56,plain,(
% 3.59/0.98    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.59/0.98    inference(cnf_transformation,[],[f44])).
% 3.59/0.98  
% 3.59/0.98  fof(f1,axiom,(
% 3.59/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f41,plain,(
% 3.59/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.59/0.98    inference(nnf_transformation,[],[f1])).
% 3.59/0.98  
% 3.59/0.98  fof(f42,plain,(
% 3.59/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.59/0.98    inference(flattening,[],[f41])).
% 3.59/0.98  
% 3.59/0.98  fof(f52,plain,(
% 3.59/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.59/0.98    inference(cnf_transformation,[],[f42])).
% 3.59/0.98  
% 3.59/0.98  fof(f2,axiom,(
% 3.59/0.98    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f21,plain,(
% 3.59/0.98    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.59/0.98    inference(ennf_transformation,[],[f2])).
% 3.59/0.98  
% 3.59/0.98  fof(f22,plain,(
% 3.59/0.98    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.59/0.98    inference(flattening,[],[f21])).
% 3.59/0.98  
% 3.59/0.98  fof(f53,plain,(
% 3.59/0.98    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 3.59/0.98    inference(cnf_transformation,[],[f22])).
% 3.59/0.98  
% 3.59/0.98  fof(f72,plain,(
% 3.59/0.98    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.59/0.98    inference(cnf_transformation,[],[f47])).
% 3.59/0.98  
% 3.59/0.98  fof(f94,plain,(
% 3.59/0.98    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.59/0.98    inference(equality_resolution,[],[f72])).
% 3.59/0.98  
% 3.59/0.98  fof(f51,plain,(
% 3.59/0.98    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.59/0.98    inference(cnf_transformation,[],[f42])).
% 3.59/0.98  
% 3.59/0.98  fof(f87,plain,(
% 3.59/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.59/0.98    inference(equality_resolution,[],[f51])).
% 3.59/0.98  
% 3.59/0.98  fof(f59,plain,(
% 3.59/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.59/0.98    inference(cnf_transformation,[],[f45])).
% 3.59/0.98  
% 3.59/0.98  fof(f4,axiom,(
% 3.59/0.98    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 3.59/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.98  
% 3.59/0.98  fof(f23,plain,(
% 3.59/0.98    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 3.59/0.98    inference(ennf_transformation,[],[f4])).
% 3.59/0.98  
% 3.59/0.98  fof(f55,plain,(
% 3.59/0.98    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 3.59/0.98    inference(cnf_transformation,[],[f23])).
% 3.59/0.98  
% 3.59/0.98  cnf(c_33,negated_conjecture,
% 3.59/0.98      ( r1_tarski(sK2,sK0) ),
% 3.59/0.98      inference(cnf_transformation,[],[f84]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2176,plain,
% 3.59/0.98      ( r1_tarski(sK2,sK0) = iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_24,plain,
% 3.59/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.59/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.59/0.98      | k1_relset_1(X1,X2,X0) = X1
% 3.59/0.98      | k1_xboole_0 = X2 ),
% 3.59/0.98      inference(cnf_transformation,[],[f69]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_35,negated_conjecture,
% 3.59/0.98      ( v1_funct_2(sK3,sK0,sK1) ),
% 3.59/0.98      inference(cnf_transformation,[],[f82]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_759,plain,
% 3.59/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.59/0.98      | k1_relset_1(X1,X2,X0) = X1
% 3.59/0.98      | sK3 != X0
% 3.59/0.98      | sK1 != X2
% 3.59/0.98      | sK0 != X1
% 3.59/0.98      | k1_xboole_0 = X2 ),
% 3.59/0.98      inference(resolution_lifted,[status(thm)],[c_24,c_35]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_760,plain,
% 3.59/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.59/0.98      | k1_relset_1(sK0,sK1,sK3) = sK0
% 3.59/0.98      | k1_xboole_0 = sK1 ),
% 3.59/0.98      inference(unflattening,[status(thm)],[c_759]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_34,negated_conjecture,
% 3.59/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.59/0.98      inference(cnf_transformation,[],[f83]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_762,plain,
% 3.59/0.98      ( k1_relset_1(sK0,sK1,sK3) = sK0 | k1_xboole_0 = sK1 ),
% 3.59/0.98      inference(global_propositional_subsumption,
% 3.59/0.98                [status(thm)],
% 3.59/0.98                [c_760,c_34]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2175,plain,
% 3.59/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_18,plain,
% 3.59/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.59/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.59/0.98      inference(cnf_transformation,[],[f68]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2181,plain,
% 3.59/0.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.59/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_4139,plain,
% 3.59/0.98      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_2175,c_2181]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_4583,plain,
% 3.59/0.98      ( k1_relat_1(sK3) = sK0 | sK1 = k1_xboole_0 ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_762,c_4139]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_15,plain,
% 3.59/0.98      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 3.59/0.98      | ~ v1_relat_1(X1)
% 3.59/0.98      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 3.59/0.98      inference(cnf_transformation,[],[f65]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2183,plain,
% 3.59/0.98      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 3.59/0.98      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 3.59/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_5100,plain,
% 3.59/0.98      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 3.59/0.98      | sK1 = k1_xboole_0
% 3.59/0.98      | r1_tarski(X0,sK0) != iProver_top
% 3.59/0.98      | v1_relat_1(sK3) != iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_4583,c_2183]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_39,plain,
% 3.59/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_16,plain,
% 3.59/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.59/0.98      | v1_relat_1(X0) ),
% 3.59/0.98      inference(cnf_transformation,[],[f66]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2468,plain,
% 3.59/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.59/0.98      | v1_relat_1(sK3) ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_16]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2469,plain,
% 3.59/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.59/0.98      | v1_relat_1(sK3) = iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_2468]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_5898,plain,
% 3.59/0.98      ( r1_tarski(X0,sK0) != iProver_top
% 3.59/0.98      | sK1 = k1_xboole_0
% 3.59/0.98      | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
% 3.59/0.98      inference(global_propositional_subsumption,
% 3.59/0.98                [status(thm)],
% 3.59/0.98                [c_5100,c_39,c_2469]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_5899,plain,
% 3.59/0.98      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 3.59/0.98      | sK1 = k1_xboole_0
% 3.59/0.98      | r1_tarski(X0,sK0) != iProver_top ),
% 3.59/0.98      inference(renaming,[status(thm)],[c_5898]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_5910,plain,
% 3.59/0.98      ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2 | sK1 = k1_xboole_0 ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_2176,c_5899]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_28,plain,
% 3.59/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.59/0.98      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.59/0.98      | ~ v1_funct_1(X0)
% 3.59/0.98      | ~ v1_relat_1(X0) ),
% 3.59/0.98      inference(cnf_transformation,[],[f80]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2177,plain,
% 3.59/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
% 3.59/0.98      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 3.59/0.98      | v1_funct_1(X0) != iProver_top
% 3.59/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_6007,plain,
% 3.59/0.98      ( sK1 = k1_xboole_0
% 3.59/0.98      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 3.59/0.98      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
% 3.59/0.98      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
% 3.59/0.98      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_5910,c_2177]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_27,plain,
% 3.59/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.59/0.98      | ~ v1_funct_1(X0)
% 3.59/0.98      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 3.59/0.98      inference(cnf_transformation,[],[f77]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2178,plain,
% 3.59/0.98      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 3.59/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.59/0.98      | v1_funct_1(X2) != iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_6195,plain,
% 3.59/0.98      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
% 3.59/0.98      | v1_funct_1(sK3) != iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_2175,c_2178]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_36,negated_conjecture,
% 3.59/0.98      ( v1_funct_1(sK3) ),
% 3.59/0.98      inference(cnf_transformation,[],[f81]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2550,plain,
% 3.59/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.59/0.98      | ~ v1_funct_1(sK3)
% 3.59/0.98      | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_27]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2732,plain,
% 3.59/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.59/0.98      | ~ v1_funct_1(sK3)
% 3.59/0.98      | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_2550]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_6319,plain,
% 3.59/0.98      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 3.59/0.98      inference(global_propositional_subsumption,
% 3.59/0.98                [status(thm)],
% 3.59/0.98                [c_6195,c_36,c_34,c_2732]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_26,plain,
% 3.59/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.59/0.98      | ~ v1_funct_1(X0)
% 3.59/0.98      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
% 3.59/0.98      inference(cnf_transformation,[],[f75]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2179,plain,
% 3.59/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.59/0.98      | v1_funct_1(X0) != iProver_top
% 3.59/0.98      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_5352,plain,
% 3.59/0.98      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
% 3.59/0.98      | v1_funct_1(sK3) != iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_2175,c_2179]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_37,plain,
% 3.59/0.98      ( v1_funct_1(sK3) = iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2526,plain,
% 3.59/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.59/0.98      | v1_funct_1(k2_partfun1(X0,X1,sK3,X2))
% 3.59/0.98      | ~ v1_funct_1(sK3) ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_26]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2646,plain,
% 3.59/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.59/0.98      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
% 3.59/0.98      | ~ v1_funct_1(sK3) ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_2526]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2647,plain,
% 3.59/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.59/0.98      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
% 3.59/0.98      | v1_funct_1(sK3) != iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_2646]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_5571,plain,
% 3.59/0.98      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
% 3.59/0.98      inference(global_propositional_subsumption,
% 3.59/0.98                [status(thm)],
% 3.59/0.98                [c_5352,c_37,c_39,c_2647]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_6328,plain,
% 3.59/0.98      ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 3.59/0.98      inference(demodulation,[status(thm)],[c_6319,c_5571]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_6840,plain,
% 3.59/0.98      ( sK1 = k1_xboole_0
% 3.59/0.98      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 3.59/0.98      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
% 3.59/0.98      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.59/0.98      inference(forward_subsumption_resolution,
% 3.59/0.98                [status(thm)],
% 3.59/0.98                [c_6007,c_6328]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_29,plain,
% 3.59/0.98      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 3.59/0.98      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.59/0.98      | ~ v1_funct_1(X0)
% 3.59/0.98      | ~ v1_relat_1(X0) ),
% 3.59/0.98      inference(cnf_transformation,[],[f79]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_31,negated_conjecture,
% 3.59/0.98      ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
% 3.59/0.98      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.59/0.98      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
% 3.59/0.98      inference(cnf_transformation,[],[f86]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_770,plain,
% 3.59/0.98      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.59/0.98      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.59/0.98      | ~ v1_funct_1(X0)
% 3.59/0.98      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.59/0.98      | ~ v1_relat_1(X0)
% 3.59/0.98      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 3.59/0.98      | k1_relat_1(X0) != sK2
% 3.59/0.98      | sK1 != X1 ),
% 3.59/0.98      inference(resolution_lifted,[status(thm)],[c_29,c_31]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_771,plain,
% 3.59/0.98      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.59/0.98      | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
% 3.59/0.98      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.59/0.98      | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.59/0.98      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
% 3.59/0.98      inference(unflattening,[status(thm)],[c_770]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_17,plain,
% 3.59/0.98      ( v5_relat_1(X0,X1)
% 3.59/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.59/0.98      inference(cnf_transformation,[],[f67]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_12,plain,
% 3.59/0.98      ( ~ v5_relat_1(X0,X1)
% 3.59/0.98      | r1_tarski(k2_relat_1(X0),X1)
% 3.59/0.98      | ~ v1_relat_1(X0) ),
% 3.59/0.98      inference(cnf_transformation,[],[f61]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_425,plain,
% 3.59/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.59/0.98      | r1_tarski(k2_relat_1(X0),X2)
% 3.59/0.98      | ~ v1_relat_1(X0) ),
% 3.59/0.98      inference(resolution,[status(thm)],[c_17,c_12]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_429,plain,
% 3.59/0.98      ( r1_tarski(k2_relat_1(X0),X2)
% 3.59/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.59/0.98      inference(global_propositional_subsumption,
% 3.59/0.98                [status(thm)],
% 3.59/0.98                [c_425,c_16]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_430,plain,
% 3.59/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.59/0.98      | r1_tarski(k2_relat_1(X0),X2) ),
% 3.59/0.98      inference(renaming,[status(thm)],[c_429]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_783,plain,
% 3.59/0.98      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.59/0.98      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.59/0.98      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
% 3.59/0.98      inference(forward_subsumption_resolution,
% 3.59/0.98                [status(thm)],
% 3.59/0.98                [c_771,c_16,c_430]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2164,plain,
% 3.59/0.98      ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 3.59/0.98      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.59/0.98      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_783]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_6326,plain,
% 3.59/0.98      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 3.59/0.98      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.59/0.98      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.59/0.98      inference(demodulation,[status(thm)],[c_6319,c_2164]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_6342,plain,
% 3.59/0.98      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 3.59/0.98      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.59/0.98      inference(forward_subsumption_resolution,
% 3.59/0.98                [status(thm)],
% 3.59/0.98                [c_6326,c_6328]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_9107,plain,
% 3.59/0.98      ( sK1 = k1_xboole_0
% 3.59/0.98      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_5910,c_6342]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_9965,plain,
% 3.59/0.98      ( sK1 = k1_xboole_0
% 3.59/0.98      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
% 3.59/0.98      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_6840,c_9107]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_25,plain,
% 3.59/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.59/0.98      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.59/0.98      | ~ v1_funct_1(X0) ),
% 3.59/0.98      inference(cnf_transformation,[],[f76]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2180,plain,
% 3.59/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.59/0.98      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 3.59/0.98      | v1_funct_1(X0) != iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_7121,plain,
% 3.59/0.98      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 3.59/0.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.59/0.98      | v1_funct_1(sK3) != iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_6319,c_2180]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_7701,plain,
% 3.59/0.98      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.59/0.98      inference(global_propositional_subsumption,
% 3.59/0.98                [status(thm)],
% 3.59/0.98                [c_7121,c_37,c_39]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2182,plain,
% 3.59/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.59/0.98      | v1_relat_1(X0) = iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_7713,plain,
% 3.59/0.98      ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_7701,c_2182]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2173,plain,
% 3.59/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.59/0.98      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_430]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_7712,plain,
% 3.59/0.98      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) = iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_7701,c_2173]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_11953,plain,
% 3.59/0.98      ( sK1 = k1_xboole_0 ),
% 3.59/0.98      inference(forward_subsumption_resolution,
% 3.59/0.98                [status(thm)],
% 3.59/0.98                [c_9965,c_7713,c_7712]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_11981,plain,
% 3.59/0.98      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
% 3.59/0.98      inference(demodulation,[status(thm)],[c_11953,c_7701]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_32,negated_conjecture,
% 3.59/0.98      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 3.59/0.98      inference(cnf_transformation,[],[f85]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_11998,plain,
% 3.59/0.98      ( sK0 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.59/0.98      inference(demodulation,[status(thm)],[c_11953,c_32]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_11999,plain,
% 3.59/0.98      ( sK0 = k1_xboole_0 ),
% 3.59/0.98      inference(equality_resolution_simp,[status(thm)],[c_11998]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_12057,plain,
% 3.59/0.98      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.59/0.98      inference(light_normalisation,[status(thm)],[c_11981,c_11999]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_7,plain,
% 3.59/0.98      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.59/0.98      inference(cnf_transformation,[],[f90]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_12059,plain,
% 3.59/0.98      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.59/0.98      inference(demodulation,[status(thm)],[c_12057,c_7]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_19,plain,
% 3.59/0.98      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
% 3.59/0.98      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 3.59/0.98      | k1_xboole_0 = X0 ),
% 3.59/0.98      inference(cnf_transformation,[],[f92]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_587,plain,
% 3.59/0.98      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.59/0.98      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 3.59/0.98      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.59/0.98      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 3.59/0.98      | sK2 != X0
% 3.59/0.98      | sK1 != k1_xboole_0
% 3.59/0.98      | k1_xboole_0 = X0 ),
% 3.59/0.98      inference(resolution_lifted,[status(thm)],[c_19,c_31]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_588,plain,
% 3.59/0.98      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.59/0.98      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
% 3.59/0.98      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.59/0.98      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 3.59/0.98      | sK1 != k1_xboole_0
% 3.59/0.98      | k1_xboole_0 = sK2 ),
% 3.59/0.98      inference(unflattening,[status(thm)],[c_587]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2172,plain,
% 3.59/0.98      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 3.59/0.98      | sK1 != k1_xboole_0
% 3.59/0.98      | k1_xboole_0 = sK2
% 3.59/0.98      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.59/0.98      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
% 3.59/0.98      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_588]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_6,plain,
% 3.59/0.98      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.59/0.98      inference(cnf_transformation,[],[f89]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2362,plain,
% 3.59/0.98      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 3.59/0.98      | sK2 = k1_xboole_0
% 3.59/0.98      | sK1 != k1_xboole_0
% 3.59/0.98      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.59/0.98      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.59/0.98      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.59/0.98      inference(demodulation,[status(thm)],[c_2172,c_6]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_9,plain,
% 3.59/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.59/0.98      inference(cnf_transformation,[],[f60]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_103,plain,
% 3.59/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.59/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_105,plain,
% 3.59/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.59/0.98      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_103]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_4,plain,
% 3.59/0.98      ( r1_tarski(k1_xboole_0,X0) ),
% 3.59/0.98      inference(cnf_transformation,[],[f54]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_111,plain,
% 3.59/0.98      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_113,plain,
% 3.59/0.98      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_111]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2728,plain,
% 3.59/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.59/0.98      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.59/0.98      | ~ v1_funct_1(sK3) ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_2646]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2729,plain,
% 3.59/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.59/0.98      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) = iProver_top
% 3.59/0.98      | v1_funct_1(sK3) != iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_2728]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2842,plain,
% 3.59/0.98      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 3.59/0.98      | sK2 = k1_xboole_0
% 3.59/0.98      | sK1 != k1_xboole_0
% 3.59/0.98      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.59/0.98      inference(global_propositional_subsumption,
% 3.59/0.98                [status(thm)],
% 3.59/0.98                [c_2362,c_37,c_39,c_105,c_113,c_2729]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_6324,plain,
% 3.59/0.98      ( k7_relat_1(sK3,sK2) != k1_xboole_0
% 3.59/0.98      | sK2 = k1_xboole_0
% 3.59/0.98      | sK1 != k1_xboole_0
% 3.59/0.98      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.59/0.98      inference(demodulation,[status(thm)],[c_6319,c_2842]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_8,plain,
% 3.59/0.98      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.59/0.98      | k1_xboole_0 = X0
% 3.59/0.98      | k1_xboole_0 = X1 ),
% 3.59/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_106,plain,
% 3.59/0.98      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.59/0.98      | k1_xboole_0 = k1_xboole_0 ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_8]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_107,plain,
% 3.59/0.98      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_7]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_112,plain,
% 3.59/0.98      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_4]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_0,plain,
% 3.59/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.59/0.98      inference(cnf_transformation,[],[f52]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2495,plain,
% 3.59/0.98      ( ~ r1_tarski(sK2,k1_xboole_0)
% 3.59/0.98      | ~ r1_tarski(k1_xboole_0,sK2)
% 3.59/0.98      | sK2 = k1_xboole_0 ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_0]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1478,plain,
% 3.59/0.98      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.59/0.98      theory(equality) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2777,plain,
% 3.59/0.98      ( ~ r1_tarski(X0,X1)
% 3.59/0.98      | r1_tarski(sK0,k1_xboole_0)
% 3.59/0.98      | sK0 != X0
% 3.59/0.98      | k1_xboole_0 != X1 ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_1478]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2779,plain,
% 3.59/0.98      ( r1_tarski(sK0,k1_xboole_0)
% 3.59/0.98      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 3.59/0.98      | sK0 != k1_xboole_0
% 3.59/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_2777]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1477,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2514,plain,
% 3.59/0.98      ( sK0 != X0 | sK0 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_1477]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2865,plain,
% 3.59/0.98      ( sK0 != sK0 | sK0 = k1_xboole_0 | k1_xboole_0 != sK0 ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_2514]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1476,plain,( X0 = X0 ),theory(equality) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2866,plain,
% 3.59/0.98      ( sK0 = sK0 ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_1476]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_3509,plain,
% 3.59/0.98      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_1477]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_3510,plain,
% 3.59/0.98      ( sK1 != k1_xboole_0
% 3.59/0.98      | k1_xboole_0 = sK1
% 3.59/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_3509]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_3,plain,
% 3.59/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 3.59/0.98      inference(cnf_transformation,[],[f53]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2763,plain,
% 3.59/0.98      ( ~ r1_tarski(X0,k1_xboole_0)
% 3.59/0.98      | ~ r1_tarski(sK2,X0)
% 3.59/0.98      | r1_tarski(sK2,k1_xboole_0) ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_3]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_3692,plain,
% 3.59/0.98      ( ~ r1_tarski(sK2,sK0)
% 3.59/0.98      | r1_tarski(sK2,k1_xboole_0)
% 3.59/0.98      | ~ r1_tarski(sK0,k1_xboole_0) ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_2763]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_6576,plain,
% 3.59/0.98      ( r1_tarski(k1_xboole_0,sK2) ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_4]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_6609,plain,
% 3.59/0.98      ( sK2 = k1_xboole_0
% 3.59/0.98      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.59/0.98      inference(global_propositional_subsumption,
% 3.59/0.98                [status(thm)],
% 3.59/0.98                [c_6324,c_33,c_32,c_106,c_107,c_112,c_2495,c_2779,c_2865,
% 3.59/0.98                 c_2866,c_3510,c_3692,c_5910,c_6342,c_6576]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_11984,plain,
% 3.59/0.98      ( sK2 = k1_xboole_0
% 3.59/0.98      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
% 3.59/0.98      inference(demodulation,[status(thm)],[c_11953,c_6609]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_12047,plain,
% 3.59/0.98      ( sK2 = k1_xboole_0
% 3.59/0.98      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.59/0.98      inference(demodulation,[status(thm)],[c_11984,c_6]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_12061,plain,
% 3.59/0.98      ( sK2 = k1_xboole_0 ),
% 3.59/0.98      inference(backward_subsumption_resolution,
% 3.59/0.98                [status(thm)],
% 3.59/0.98                [c_12059,c_12047]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_21,plain,
% 3.59/0.98      ( v1_funct_2(X0,k1_xboole_0,X1)
% 3.59/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.59/0.98      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 3.59/0.98      inference(cnf_transformation,[],[f94]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_684,plain,
% 3.59/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.59/0.98      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.59/0.98      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.59/0.98      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 3.59/0.98      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 3.59/0.98      | sK2 != k1_xboole_0
% 3.59/0.98      | sK1 != X1 ),
% 3.59/0.98      inference(resolution_lifted,[status(thm)],[c_21,c_31]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_685,plain,
% 3.59/0.98      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.59/0.98      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 3.59/0.98      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.59/0.98      | k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
% 3.59/0.98      | sK2 != k1_xboole_0 ),
% 3.59/0.98      inference(unflattening,[status(thm)],[c_684]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2168,plain,
% 3.59/0.98      ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
% 3.59/0.98      | sK2 != k1_xboole_0
% 3.59/0.98      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.59/0.98      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
% 3.59/0.98      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_685]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2375,plain,
% 3.59/0.98      ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
% 3.59/0.98      | sK2 != k1_xboole_0
% 3.59/0.98      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.59/0.98      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.59/0.98      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.59/0.98      inference(demodulation,[status(thm)],[c_2168,c_7]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2912,plain,
% 3.59/0.98      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.59/0.98      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.59/0.98      | sK2 != k1_xboole_0
% 3.59/0.98      | k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0 ),
% 3.59/0.98      inference(global_propositional_subsumption,
% 3.59/0.98                [status(thm)],
% 3.59/0.98                [c_2375,c_37,c_39,c_2729]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2913,plain,
% 3.59/0.98      ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
% 3.59/0.98      | sK2 != k1_xboole_0
% 3.59/0.98      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.59/0.98      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.59/0.98      inference(renaming,[status(thm)],[c_2912]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_6323,plain,
% 3.59/0.98      ( k1_relset_1(k1_xboole_0,sK1,k7_relat_1(sK3,sK2)) != k1_xboole_0
% 3.59/0.98      | sK2 != k1_xboole_0
% 3.59/0.98      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.59/0.98      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.59/0.98      inference(demodulation,[status(thm)],[c_6319,c_2913]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_6618,plain,
% 3.59/0.98      ( k1_relset_1(k1_xboole_0,sK1,k7_relat_1(sK3,sK2)) != k1_xboole_0
% 3.59/0.98      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.59/0.98      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.59/0.98      inference(global_propositional_subsumption,
% 3.59/0.98                [status(thm)],
% 3.59/0.98                [c_6323,c_6609]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_11983,plain,
% 3.59/0.98      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,sK2)) != k1_xboole_0
% 3.59/0.98      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
% 3.59/0.98      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.59/0.98      inference(demodulation,[status(thm)],[c_11953,c_6618]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_12053,plain,
% 3.59/0.98      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,sK2)) != k1_xboole_0
% 3.59/0.98      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.59/0.98      inference(demodulation,[status(thm)],[c_11983,c_6]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_12062,plain,
% 3.59/0.98      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,sK2)) != k1_xboole_0 ),
% 3.59/0.98      inference(backward_subsumption_resolution,
% 3.59/0.98                [status(thm)],
% 3.59/0.98                [c_12059,c_12053]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_12066,plain,
% 3.59/0.98      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0 ),
% 3.59/0.98      inference(demodulation,[status(thm)],[c_12061,c_12062]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_1,plain,
% 3.59/0.98      ( r1_tarski(X0,X0) ),
% 3.59/0.98      inference(cnf_transformation,[],[f87]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2191,plain,
% 3.59/0.98      ( r1_tarski(X0,X0) = iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2189,plain,
% 3.59/0.98      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_5908,plain,
% 3.59/0.98      ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0
% 3.59/0.98      | sK1 = k1_xboole_0 ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_2189,c_5899]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2555,plain,
% 3.59/0.98      ( ~ r1_tarski(X0,k1_relat_1(sK3))
% 3.59/0.98      | ~ v1_relat_1(sK3)
% 3.59/0.98      | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_15]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2557,plain,
% 3.59/0.98      ( ~ r1_tarski(k1_xboole_0,k1_relat_1(sK3))
% 3.59/0.98      | ~ v1_relat_1(sK3)
% 3.59/0.98      | k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_2555]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2903,plain,
% 3.59/0.98      ( r1_tarski(k1_xboole_0,k1_relat_1(sK3)) ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_4]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_8804,plain,
% 3.59/0.98      ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
% 3.59/0.98      inference(global_propositional_subsumption,
% 3.59/0.98                [status(thm)],
% 3.59/0.98                [c_5908,c_34,c_2468,c_2557,c_2903]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_8808,plain,
% 3.59/0.98      ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) = iProver_top
% 3.59/0.98      | r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_xboole_0)),X0) != iProver_top
% 3.59/0.98      | v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top
% 3.59/0.98      | v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_8804,c_2177]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_8820,plain,
% 3.59/0.98      ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.59/0.98      | r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_xboole_0)),X0) != iProver_top
% 3.59/0.98      | v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top
% 3.59/0.98      | v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
% 3.59/0.98      inference(light_normalisation,[status(thm)],[c_8808,c_7]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_6372,plain,
% 3.59/0.98      ( v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) = iProver_top ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_6328]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_7744,plain,
% 3.59/0.98      ( v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = iProver_top ),
% 3.59/0.98      inference(instantiation,[status(thm)],[c_7713]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_9279,plain,
% 3.59/0.98      ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.59/0.98      | r1_tarski(k2_relat_1(k7_relat_1(sK3,k1_xboole_0)),X0) != iProver_top ),
% 3.59/0.98      inference(global_propositional_subsumption,
% 3.59/0.98                [status(thm)],
% 3.59/0.98                [c_8820,c_6372,c_7744]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_9287,plain,
% 3.59/0.98      ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_2191,c_9279]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_10,plain,
% 3.59/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.59/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2186,plain,
% 3.59/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.59/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_9455,plain,
% 3.59/0.98      ( r1_tarski(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_9287,c_2186]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_5,plain,
% 3.59/0.98      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 3.59/0.98      inference(cnf_transformation,[],[f55]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2188,plain,
% 3.59/0.98      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_9495,plain,
% 3.59/0.98      ( k7_relat_1(sK3,k1_xboole_0) = k1_xboole_0 ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_9455,c_2188]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_12069,plain,
% 3.59/0.98      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
% 3.59/0.98      inference(light_normalisation,[status(thm)],[c_12066,c_9495]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_2187,plain,
% 3.59/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.59/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 3.59/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_4141,plain,
% 3.59/0.98      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
% 3.59/0.98      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_7,c_2181]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_4247,plain,
% 3.59/0.98      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
% 3.59/0.98      | r1_tarski(X1,k1_xboole_0) != iProver_top ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_2187,c_4141]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_4828,plain,
% 3.59/0.98      ( k1_relset_1(k1_xboole_0,X0,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
% 3.59/0.98      inference(superposition,[status(thm)],[c_2191,c_4247]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_12070,plain,
% 3.59/0.98      ( k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
% 3.59/0.98      inference(demodulation,[status(thm)],[c_12069,c_4828]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(c_9686,plain,
% 3.59/0.98      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.59/0.98      inference(demodulation,[status(thm)],[c_9495,c_8804]) ).
% 3.59/0.98  
% 3.59/0.98  cnf(contradiction,plain,
% 3.59/0.98      ( $false ),
% 3.59/0.98      inference(minisat,[status(thm)],[c_12070,c_9686]) ).
% 3.59/0.98  
% 3.59/0.98  
% 3.59/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.59/0.98  
% 3.59/0.98  ------                               Statistics
% 3.59/0.98  
% 3.59/0.98  ------ General
% 3.59/0.98  
% 3.59/0.98  abstr_ref_over_cycles:                  0
% 3.59/0.98  abstr_ref_under_cycles:                 0
% 3.59/0.98  gc_basic_clause_elim:                   0
% 3.59/0.98  forced_gc_time:                         0
% 3.59/0.98  parsing_time:                           0.022
% 3.59/0.98  unif_index_cands_time:                  0.
% 3.59/0.98  unif_index_add_time:                    0.
% 3.59/0.98  orderings_time:                         0.
% 3.59/0.98  out_proof_time:                         0.013
% 3.59/0.98  total_time:                             0.321
% 3.59/0.98  num_of_symbols:                         49
% 3.59/0.98  num_of_terms:                           10421
% 3.59/0.98  
% 3.59/0.98  ------ Preprocessing
% 3.59/0.98  
% 3.59/0.98  num_of_splits:                          0
% 3.59/0.98  num_of_split_atoms:                     0
% 3.59/0.98  num_of_reused_defs:                     0
% 3.59/0.98  num_eq_ax_congr_red:                    13
% 3.59/0.98  num_of_sem_filtered_clauses:            1
% 3.59/0.98  num_of_subtypes:                        0
% 3.59/0.98  monotx_restored_types:                  0
% 3.59/0.98  sat_num_of_epr_types:                   0
% 3.59/0.98  sat_num_of_non_cyclic_types:            0
% 3.59/0.98  sat_guarded_non_collapsed_types:        0
% 3.59/0.98  num_pure_diseq_elim:                    0
% 3.59/0.98  simp_replaced_by:                       0
% 3.59/0.98  res_preprocessed:                       163
% 3.59/0.98  prep_upred:                             0
% 3.59/0.98  prep_unflattend:                        60
% 3.59/0.98  smt_new_axioms:                         0
% 3.59/0.98  pred_elim_cands:                        4
% 3.59/0.98  pred_elim:                              2
% 3.59/0.98  pred_elim_cl:                           0
% 3.59/0.98  pred_elim_cycles:                       5
% 3.59/0.98  merged_defs:                            8
% 3.59/0.98  merged_defs_ncl:                        0
% 3.59/0.98  bin_hyper_res:                          8
% 3.59/0.98  prep_cycles:                            4
% 3.59/0.98  pred_elim_time:                         0.017
% 3.59/0.98  splitting_time:                         0.
% 3.59/0.98  sem_filter_time:                        0.
% 3.59/0.98  monotx_time:                            0.001
% 3.59/0.98  subtype_inf_time:                       0.
% 3.59/0.98  
% 3.59/0.98  ------ Problem properties
% 3.59/0.98  
% 3.59/0.98  clauses:                                35
% 3.59/0.98  conjectures:                            4
% 3.59/0.98  epr:                                    8
% 3.59/0.98  horn:                                   30
% 3.59/0.98  ground:                                 12
% 3.59/0.98  unary:                                  8
% 3.59/0.98  binary:                                 9
% 3.59/0.98  lits:                                   94
% 3.59/0.98  lits_eq:                                35
% 3.59/0.98  fd_pure:                                0
% 3.59/0.98  fd_pseudo:                              0
% 3.59/0.98  fd_cond:                                4
% 3.59/0.98  fd_pseudo_cond:                         1
% 3.59/0.98  ac_symbols:                             0
% 3.59/0.98  
% 3.59/0.98  ------ Propositional Solver
% 3.59/0.98  
% 3.59/0.98  prop_solver_calls:                      27
% 3.59/0.98  prop_fast_solver_calls:                 1396
% 3.59/0.98  smt_solver_calls:                       0
% 3.59/0.98  smt_fast_solver_calls:                  0
% 3.59/0.98  prop_num_of_clauses:                    4526
% 3.59/0.98  prop_preprocess_simplified:             11230
% 3.59/0.98  prop_fo_subsumed:                       32
% 3.59/0.98  prop_solver_time:                       0.
% 3.59/0.98  smt_solver_time:                        0.
% 3.59/0.98  smt_fast_solver_time:                   0.
% 3.59/0.98  prop_fast_solver_time:                  0.
% 3.59/0.98  prop_unsat_core_time:                   0.
% 3.59/0.98  
% 3.59/0.98  ------ QBF
% 3.59/0.98  
% 3.59/0.98  qbf_q_res:                              0
% 3.59/0.98  qbf_num_tautologies:                    0
% 3.59/0.98  qbf_prep_cycles:                        0
% 3.59/0.98  
% 3.59/0.98  ------ BMC1
% 3.59/0.98  
% 3.59/0.98  bmc1_current_bound:                     -1
% 3.59/0.98  bmc1_last_solved_bound:                 -1
% 3.59/0.98  bmc1_unsat_core_size:                   -1
% 3.59/0.98  bmc1_unsat_core_parents_size:           -1
% 3.59/0.98  bmc1_merge_next_fun:                    0
% 3.59/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.59/0.98  
% 3.59/0.98  ------ Instantiation
% 3.59/0.98  
% 3.59/0.98  inst_num_of_clauses:                    1233
% 3.59/0.98  inst_num_in_passive:                    303
% 3.59/0.98  inst_num_in_active:                     502
% 3.59/0.98  inst_num_in_unprocessed:                428
% 3.59/0.98  inst_num_of_loops:                      660
% 3.59/0.98  inst_num_of_learning_restarts:          0
% 3.59/0.98  inst_num_moves_active_passive:          157
% 3.59/0.98  inst_lit_activity:                      0
% 3.59/0.98  inst_lit_activity_moves:                0
% 3.59/0.98  inst_num_tautologies:                   0
% 3.59/0.98  inst_num_prop_implied:                  0
% 3.59/0.98  inst_num_existing_simplified:           0
% 3.59/0.98  inst_num_eq_res_simplified:             0
% 3.59/0.98  inst_num_child_elim:                    0
% 3.59/0.98  inst_num_of_dismatching_blockings:      428
% 3.59/0.98  inst_num_of_non_proper_insts:           1203
% 3.59/0.98  inst_num_of_duplicates:                 0
% 3.59/0.98  inst_inst_num_from_inst_to_res:         0
% 3.59/0.98  inst_dismatching_checking_time:         0.
% 3.59/0.98  
% 3.59/0.98  ------ Resolution
% 3.59/0.98  
% 3.59/0.98  res_num_of_clauses:                     0
% 3.59/0.98  res_num_in_passive:                     0
% 3.59/0.98  res_num_in_active:                      0
% 3.59/0.98  res_num_of_loops:                       167
% 3.59/0.98  res_forward_subset_subsumed:            41
% 3.59/0.98  res_backward_subset_subsumed:           0
% 3.59/0.98  res_forward_subsumed:                   0
% 3.59/0.98  res_backward_subsumed:                  0
% 3.59/0.98  res_forward_subsumption_resolution:     5
% 3.59/0.98  res_backward_subsumption_resolution:    0
% 3.59/0.98  res_clause_to_clause_subsumption:       1055
% 3.59/0.98  res_orphan_elimination:                 0
% 3.59/0.98  res_tautology_del:                      92
% 3.59/0.98  res_num_eq_res_simplified:              1
% 3.59/0.98  res_num_sel_changes:                    0
% 3.59/0.98  res_moves_from_active_to_pass:          0
% 3.59/0.98  
% 3.59/0.98  ------ Superposition
% 3.59/0.98  
% 3.59/0.98  sup_time_total:                         0.
% 3.59/0.98  sup_time_generating:                    0.
% 3.59/0.98  sup_time_sim_full:                      0.
% 3.59/0.98  sup_time_sim_immed:                     0.
% 3.59/0.98  
% 3.59/0.98  sup_num_of_clauses:                     193
% 3.59/0.98  sup_num_in_active:                      65
% 3.59/0.98  sup_num_in_passive:                     128
% 3.59/0.98  sup_num_of_loops:                       130
% 3.59/0.98  sup_fw_superposition:                   140
% 3.59/0.98  sup_bw_superposition:                   166
% 3.59/0.98  sup_immediate_simplified:               108
% 3.59/0.98  sup_given_eliminated:                   3
% 3.59/0.98  comparisons_done:                       0
% 3.59/0.98  comparisons_avoided:                    25
% 3.59/0.98  
% 3.59/0.98  ------ Simplifications
% 3.59/0.98  
% 3.59/0.98  
% 3.59/0.98  sim_fw_subset_subsumed:                 21
% 3.59/0.98  sim_bw_subset_subsumed:                 25
% 3.59/0.98  sim_fw_subsumed:                        23
% 3.59/0.98  sim_bw_subsumed:                        4
% 3.59/0.98  sim_fw_subsumption_res:                 10
% 3.59/0.98  sim_bw_subsumption_res:                 2
% 3.59/0.98  sim_tautology_del:                      8
% 3.59/0.98  sim_eq_tautology_del:                   16
% 3.59/0.98  sim_eq_res_simp:                        3
% 3.59/0.98  sim_fw_demodulated:                     27
% 3.59/0.98  sim_bw_demodulated:                     63
% 3.59/0.98  sim_light_normalised:                   51
% 3.59/0.98  sim_joinable_taut:                      0
% 3.59/0.98  sim_joinable_simp:                      0
% 3.59/0.98  sim_ac_normalised:                      0
% 3.59/0.98  sim_smt_subsumption:                    0
% 3.59/0.98  
%------------------------------------------------------------------------------
