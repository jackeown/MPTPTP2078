%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:52 EST 2020

% Result     : Theorem 3.60s
% Output     : CNFRefutation 3.60s
% Verified   : 
% Statistics : Number of formulae       :  214 (5809 expanded)
%              Number of clauses        :  139 (1906 expanded)
%              Number of leaves         :   19 (1089 expanded)
%              Depth                    :   27
%              Number of atoms          :  656 (32231 expanded)
%              Number of equality atoms :  332 (8719 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   3 average)
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

fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

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

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f60,plain,(
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

fof(f4,axiom,(
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
    inference(nnf_transformation,[],[f4])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f43])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f90,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f56])).

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

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f89,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f57])).

fof(f5,axiom,(
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
    inference(nnf_transformation,[],[f5])).

fof(f59,plain,(
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

fof(f55,plain,(
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

cnf(c_33,negated_conjecture,
    ( r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1684,plain,
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

cnf(c_621,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X0
    | sK1 != X2
    | sK0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_35])).

cnf(c_622,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_621])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_624,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_622,c_34])).

cnf(c_1683,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1689,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3544,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1683,c_1689])).

cnf(c_3856,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_624,c_3544])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1692,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4618,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3856,c_1692])).

cnf(c_39,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1970,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1971,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1970])).

cnf(c_5472,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | sK1 = k1_xboole_0
    | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4618,c_39,c_1971])).

cnf(c_5473,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5472])).

cnf(c_5483,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1684,c_5473])).

cnf(c_28,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1685,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_5559,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5483,c_1685])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1686,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_5716,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1683,c_1686])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2044,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_2155,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_2044])).

cnf(c_5833,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5716,c_36,c_34,c_2155])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1687,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4649,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1683,c_1687])).

cnf(c_37,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_2020,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(k2_partfun1(X0,X1,sK3,X2))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_2123,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2020])).

cnf(c_2124,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2123])).

cnf(c_5144,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4649,c_37,c_39,c_2124])).

cnf(c_5842,plain,
    ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5833,c_5144])).

cnf(c_6612,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5559,c_5842])).

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

cnf(c_632,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_relat_1(X0)
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_relat_1(X0) != sK2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_31])).

cnf(c_633,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
    inference(unflattening,[status(thm)],[c_632])).

cnf(c_17,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_11,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_420,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_17,c_11])).

cnf(c_424,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_420,c_16])).

cnf(c_425,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_424])).

cnf(c_645,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_633,c_16,c_425])).

cnf(c_1672,plain,
    ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_645])).

cnf(c_5840,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5833,c_1672])).

cnf(c_5856,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5840,c_5842])).

cnf(c_9554,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5483,c_5856])).

cnf(c_9700,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6612,c_9554])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1688,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_6694,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5833,c_1688])).

cnf(c_7691,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6694,c_37,c_39])).

cnf(c_1690,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_7703,plain,
    ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7691,c_1690])).

cnf(c_1681,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_425])).

cnf(c_7702,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_7691,c_1681])).

cnf(c_11692,plain,
    ( sK1 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_9700,c_7703,c_7702])).

cnf(c_7700,plain,
    ( k1_relset_1(sK0,sK1,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_7691,c_1689])).

cnf(c_11712,plain,
    ( k1_relset_1(sK0,k1_xboole_0,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(demodulation,[status(thm)],[c_11692,c_7700])).

cnf(c_32,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_11733,plain,
    ( sK0 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_11692,c_32])).

cnf(c_11734,plain,
    ( sK0 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_11733])).

cnf(c_11814,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(light_normalisation,[status(thm)],[c_11712,c_11734])).

cnf(c_11716,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11692,c_7691])).

cnf(c_11791,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11716,c_11734])).

cnf(c_6,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_11793,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11791,c_6])).

cnf(c_19,plain,
    ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_449,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK2 != X0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_31])).

cnf(c_450,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_449])).

cnf(c_1680,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_450])).

cnf(c_5,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1869,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1680,c_5])).

cnf(c_8,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_104,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_106,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_104])).

cnf(c_4,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_109,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_111,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_109])).

cnf(c_2250,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2123])).

cnf(c_2251,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2250])).

cnf(c_2322,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1869,c_37,c_39,c_106,c_111,c_2251])).

cnf(c_5838,plain,
    ( k7_relat_1(sK3,sK2) != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5833,c_2322])).

cnf(c_7,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_107,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_108,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_110,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1992,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK2)
    | sK2 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_992,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2260,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK0,k1_xboole_0)
    | sK0 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_992])).

cnf(c_2262,plain,
    ( r1_tarski(sK0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | sK0 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2260])).

cnf(c_991,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2008,plain,
    ( sK0 != X0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_991])).

cnf(c_2345,plain,
    ( sK0 != sK0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_2008])).

cnf(c_990,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2346,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_990])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2182,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | ~ r1_tarski(sK2,X0)
    | r1_tarski(sK2,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2512,plain,
    ( ~ r1_tarski(sK2,sK0)
    | r1_tarski(sK2,k1_xboole_0)
    | ~ r1_tarski(sK0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2182])).

cnf(c_3032,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_991])).

cnf(c_3033,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3032])).

cnf(c_3932,plain,
    ( r1_tarski(k1_xboole_0,sK2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_5969,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5838,c_33,c_32,c_107,c_108,c_110,c_1992,c_2262,c_2345,c_2346,c_2512,c_3033,c_3932,c_5483,c_5856])).

cnf(c_11719,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11692,c_5969])).

cnf(c_11782,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11719,c_5])).

cnf(c_11795,plain,
    ( sK2 = k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_11793,c_11782])).

cnf(c_21,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_546,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | sK2 != k1_xboole_0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_31])).

cnf(c_547,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_546])).

cnf(c_1676,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_547])).

cnf(c_1882,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1676,c_6])).

cnf(c_2390,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | sK2 != k1_xboole_0
    | k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1882,c_37,c_39,c_2251])).

cnf(c_2391,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2390])).

cnf(c_5837,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k7_relat_1(sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5833,c_2391])).

cnf(c_6204,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k7_relat_1(sK3,sK2)) != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5837,c_5969])).

cnf(c_11718,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,sK2)) != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11692,c_6204])).

cnf(c_11788,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,sK2)) != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11718,c_5])).

cnf(c_11796,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,sK2)) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_11793,c_11788])).

cnf(c_11800,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_11795,c_11796])).

cnf(c_11816,plain,
    ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_11814,c_11800])).

cnf(c_1696,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_5482,plain,
    ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1696,c_5473])).

cnf(c_2049,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2051,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2049])).

cnf(c_2381,plain,
    ( r1_tarski(k1_xboole_0,k1_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_9091,plain,
    ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5482,c_34,c_1970,c_2051,c_2381])).

cnf(c_11819,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_11816,c_9091])).

cnf(c_11820,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_11819])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:26:29 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.60/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.60/0.99  
% 3.60/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.60/0.99  
% 3.60/0.99  ------  iProver source info
% 3.60/0.99  
% 3.60/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.60/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.60/0.99  git: non_committed_changes: false
% 3.60/0.99  git: last_make_outside_of_git: false
% 3.60/0.99  
% 3.60/0.99  ------ 
% 3.60/0.99  
% 3.60/0.99  ------ Input Options
% 3.60/0.99  
% 3.60/0.99  --out_options                           all
% 3.60/0.99  --tptp_safe_out                         true
% 3.60/0.99  --problem_path                          ""
% 3.60/0.99  --include_path                          ""
% 3.60/0.99  --clausifier                            res/vclausify_rel
% 3.60/0.99  --clausifier_options                    --mode clausify
% 3.60/0.99  --stdin                                 false
% 3.60/0.99  --stats_out                             all
% 3.60/0.99  
% 3.60/0.99  ------ General Options
% 3.60/0.99  
% 3.60/0.99  --fof                                   false
% 3.60/0.99  --time_out_real                         305.
% 3.60/0.99  --time_out_virtual                      -1.
% 3.60/0.99  --symbol_type_check                     false
% 3.60/0.99  --clausify_out                          false
% 3.60/0.99  --sig_cnt_out                           false
% 3.60/0.99  --trig_cnt_out                          false
% 3.60/0.99  --trig_cnt_out_tolerance                1.
% 3.60/0.99  --trig_cnt_out_sk_spl                   false
% 3.60/0.99  --abstr_cl_out                          false
% 3.60/0.99  
% 3.60/0.99  ------ Global Options
% 3.60/0.99  
% 3.60/0.99  --schedule                              default
% 3.60/0.99  --add_important_lit                     false
% 3.60/0.99  --prop_solver_per_cl                    1000
% 3.60/0.99  --min_unsat_core                        false
% 3.60/0.99  --soft_assumptions                      false
% 3.60/0.99  --soft_lemma_size                       3
% 3.60/0.99  --prop_impl_unit_size                   0
% 3.60/0.99  --prop_impl_unit                        []
% 3.60/0.99  --share_sel_clauses                     true
% 3.60/0.99  --reset_solvers                         false
% 3.60/0.99  --bc_imp_inh                            [conj_cone]
% 3.60/0.99  --conj_cone_tolerance                   3.
% 3.60/0.99  --extra_neg_conj                        none
% 3.60/0.99  --large_theory_mode                     true
% 3.60/0.99  --prolific_symb_bound                   200
% 3.60/0.99  --lt_threshold                          2000
% 3.60/0.99  --clause_weak_htbl                      true
% 3.60/0.99  --gc_record_bc_elim                     false
% 3.60/0.99  
% 3.60/0.99  ------ Preprocessing Options
% 3.60/0.99  
% 3.60/0.99  --preprocessing_flag                    true
% 3.60/0.99  --time_out_prep_mult                    0.1
% 3.60/0.99  --splitting_mode                        input
% 3.60/0.99  --splitting_grd                         true
% 3.60/0.99  --splitting_cvd                         false
% 3.60/0.99  --splitting_cvd_svl                     false
% 3.60/0.99  --splitting_nvd                         32
% 3.60/0.99  --sub_typing                            true
% 3.60/0.99  --prep_gs_sim                           true
% 3.60/0.99  --prep_unflatten                        true
% 3.60/0.99  --prep_res_sim                          true
% 3.60/0.99  --prep_upred                            true
% 3.60/0.99  --prep_sem_filter                       exhaustive
% 3.60/0.99  --prep_sem_filter_out                   false
% 3.60/0.99  --pred_elim                             true
% 3.60/0.99  --res_sim_input                         true
% 3.60/0.99  --eq_ax_congr_red                       true
% 3.60/0.99  --pure_diseq_elim                       true
% 3.60/0.99  --brand_transform                       false
% 3.60/0.99  --non_eq_to_eq                          false
% 3.60/0.99  --prep_def_merge                        true
% 3.60/0.99  --prep_def_merge_prop_impl              false
% 3.60/0.99  --prep_def_merge_mbd                    true
% 3.60/0.99  --prep_def_merge_tr_red                 false
% 3.60/0.99  --prep_def_merge_tr_cl                  false
% 3.60/0.99  --smt_preprocessing                     true
% 3.60/0.99  --smt_ac_axioms                         fast
% 3.60/0.99  --preprocessed_out                      false
% 3.60/0.99  --preprocessed_stats                    false
% 3.60/0.99  
% 3.60/0.99  ------ Abstraction refinement Options
% 3.60/0.99  
% 3.60/0.99  --abstr_ref                             []
% 3.60/0.99  --abstr_ref_prep                        false
% 3.60/0.99  --abstr_ref_until_sat                   false
% 3.60/0.99  --abstr_ref_sig_restrict                funpre
% 3.60/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.60/0.99  --abstr_ref_under                       []
% 3.60/0.99  
% 3.60/0.99  ------ SAT Options
% 3.60/0.99  
% 3.60/0.99  --sat_mode                              false
% 3.60/0.99  --sat_fm_restart_options                ""
% 3.60/0.99  --sat_gr_def                            false
% 3.60/0.99  --sat_epr_types                         true
% 3.60/0.99  --sat_non_cyclic_types                  false
% 3.60/0.99  --sat_finite_models                     false
% 3.60/0.99  --sat_fm_lemmas                         false
% 3.60/0.99  --sat_fm_prep                           false
% 3.60/0.99  --sat_fm_uc_incr                        true
% 3.60/0.99  --sat_out_model                         small
% 3.60/0.99  --sat_out_clauses                       false
% 3.60/0.99  
% 3.60/0.99  ------ QBF Options
% 3.60/0.99  
% 3.60/0.99  --qbf_mode                              false
% 3.60/0.99  --qbf_elim_univ                         false
% 3.60/0.99  --qbf_dom_inst                          none
% 3.60/0.99  --qbf_dom_pre_inst                      false
% 3.60/0.99  --qbf_sk_in                             false
% 3.60/0.99  --qbf_pred_elim                         true
% 3.60/0.99  --qbf_split                             512
% 3.60/0.99  
% 3.60/0.99  ------ BMC1 Options
% 3.60/0.99  
% 3.60/0.99  --bmc1_incremental                      false
% 3.60/0.99  --bmc1_axioms                           reachable_all
% 3.60/0.99  --bmc1_min_bound                        0
% 3.60/0.99  --bmc1_max_bound                        -1
% 3.60/0.99  --bmc1_max_bound_default                -1
% 3.60/0.99  --bmc1_symbol_reachability              true
% 3.60/0.99  --bmc1_property_lemmas                  false
% 3.60/0.99  --bmc1_k_induction                      false
% 3.60/0.99  --bmc1_non_equiv_states                 false
% 3.60/0.99  --bmc1_deadlock                         false
% 3.60/0.99  --bmc1_ucm                              false
% 3.60/0.99  --bmc1_add_unsat_core                   none
% 3.60/0.99  --bmc1_unsat_core_children              false
% 3.60/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.60/0.99  --bmc1_out_stat                         full
% 3.60/0.99  --bmc1_ground_init                      false
% 3.60/0.99  --bmc1_pre_inst_next_state              false
% 3.60/0.99  --bmc1_pre_inst_state                   false
% 3.60/0.99  --bmc1_pre_inst_reach_state             false
% 3.60/0.99  --bmc1_out_unsat_core                   false
% 3.60/0.99  --bmc1_aig_witness_out                  false
% 3.60/0.99  --bmc1_verbose                          false
% 3.60/0.99  --bmc1_dump_clauses_tptp                false
% 3.60/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.60/0.99  --bmc1_dump_file                        -
% 3.60/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.60/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.60/0.99  --bmc1_ucm_extend_mode                  1
% 3.60/0.99  --bmc1_ucm_init_mode                    2
% 3.60/0.99  --bmc1_ucm_cone_mode                    none
% 3.60/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.60/0.99  --bmc1_ucm_relax_model                  4
% 3.60/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.60/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.60/0.99  --bmc1_ucm_layered_model                none
% 3.60/0.99  --bmc1_ucm_max_lemma_size               10
% 3.60/0.99  
% 3.60/0.99  ------ AIG Options
% 3.60/0.99  
% 3.60/0.99  --aig_mode                              false
% 3.60/0.99  
% 3.60/0.99  ------ Instantiation Options
% 3.60/0.99  
% 3.60/0.99  --instantiation_flag                    true
% 3.60/0.99  --inst_sos_flag                         false
% 3.60/0.99  --inst_sos_phase                        true
% 3.60/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.60/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.60/0.99  --inst_lit_sel_side                     num_symb
% 3.60/0.99  --inst_solver_per_active                1400
% 3.60/0.99  --inst_solver_calls_frac                1.
% 3.60/0.99  --inst_passive_queue_type               priority_queues
% 3.60/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.60/0.99  --inst_passive_queues_freq              [25;2]
% 3.60/0.99  --inst_dismatching                      true
% 3.60/0.99  --inst_eager_unprocessed_to_passive     true
% 3.60/0.99  --inst_prop_sim_given                   true
% 3.60/0.99  --inst_prop_sim_new                     false
% 3.60/0.99  --inst_subs_new                         false
% 3.60/0.99  --inst_eq_res_simp                      false
% 3.60/0.99  --inst_subs_given                       false
% 3.60/0.99  --inst_orphan_elimination               true
% 3.60/0.99  --inst_learning_loop_flag               true
% 3.60/0.99  --inst_learning_start                   3000
% 3.60/0.99  --inst_learning_factor                  2
% 3.60/0.99  --inst_start_prop_sim_after_learn       3
% 3.60/0.99  --inst_sel_renew                        solver
% 3.60/0.99  --inst_lit_activity_flag                true
% 3.60/0.99  --inst_restr_to_given                   false
% 3.60/0.99  --inst_activity_threshold               500
% 3.60/0.99  --inst_out_proof                        true
% 3.60/0.99  
% 3.60/0.99  ------ Resolution Options
% 3.60/0.99  
% 3.60/0.99  --resolution_flag                       true
% 3.60/0.99  --res_lit_sel                           adaptive
% 3.60/0.99  --res_lit_sel_side                      none
% 3.60/0.99  --res_ordering                          kbo
% 3.60/0.99  --res_to_prop_solver                    active
% 3.60/0.99  --res_prop_simpl_new                    false
% 3.60/0.99  --res_prop_simpl_given                  true
% 3.60/0.99  --res_passive_queue_type                priority_queues
% 3.60/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.60/0.99  --res_passive_queues_freq               [15;5]
% 3.60/0.99  --res_forward_subs                      full
% 3.60/0.99  --res_backward_subs                     full
% 3.60/0.99  --res_forward_subs_resolution           true
% 3.60/0.99  --res_backward_subs_resolution          true
% 3.60/0.99  --res_orphan_elimination                true
% 3.60/0.99  --res_time_limit                        2.
% 3.60/0.99  --res_out_proof                         true
% 3.60/0.99  
% 3.60/0.99  ------ Superposition Options
% 3.60/0.99  
% 3.60/0.99  --superposition_flag                    true
% 3.60/0.99  --sup_passive_queue_type                priority_queues
% 3.60/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.60/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.60/0.99  --demod_completeness_check              fast
% 3.60/0.99  --demod_use_ground                      true
% 3.60/0.99  --sup_to_prop_solver                    passive
% 3.60/0.99  --sup_prop_simpl_new                    true
% 3.60/0.99  --sup_prop_simpl_given                  true
% 3.60/0.99  --sup_fun_splitting                     false
% 3.60/0.99  --sup_smt_interval                      50000
% 3.60/0.99  
% 3.60/0.99  ------ Superposition Simplification Setup
% 3.60/0.99  
% 3.60/0.99  --sup_indices_passive                   []
% 3.60/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.60/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.60/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.60/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.60/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.60/0.99  --sup_full_bw                           [BwDemod]
% 3.60/0.99  --sup_immed_triv                        [TrivRules]
% 3.60/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.60/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.60/0.99  --sup_immed_bw_main                     []
% 3.60/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.60/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.60/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.60/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.60/0.99  
% 3.60/0.99  ------ Combination Options
% 3.60/0.99  
% 3.60/0.99  --comb_res_mult                         3
% 3.60/0.99  --comb_sup_mult                         2
% 3.60/0.99  --comb_inst_mult                        10
% 3.60/0.99  
% 3.60/0.99  ------ Debug Options
% 3.60/0.99  
% 3.60/0.99  --dbg_backtrace                         false
% 3.60/0.99  --dbg_dump_prop_clauses                 false
% 3.60/0.99  --dbg_dump_prop_clauses_file            -
% 3.60/0.99  --dbg_out_stat                          false
% 3.60/0.99  ------ Parsing...
% 3.60/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.60/0.99  
% 3.60/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.60/0.99  
% 3.60/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.60/0.99  
% 3.60/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.60/0.99  ------ Proving...
% 3.60/0.99  ------ Problem Properties 
% 3.60/0.99  
% 3.60/0.99  
% 3.60/0.99  clauses                                 35
% 3.60/0.99  conjectures                             4
% 3.60/0.99  EPR                                     7
% 3.60/0.99  Horn                                    30
% 3.60/0.99  unary                                   8
% 3.60/0.99  binary                                  9
% 3.60/0.99  lits                                    94
% 3.60/0.99  lits eq                                 35
% 3.60/0.99  fd_pure                                 0
% 3.60/0.99  fd_pseudo                               0
% 3.60/0.99  fd_cond                                 3
% 3.60/0.99  fd_pseudo_cond                          1
% 3.60/0.99  AC symbols                              0
% 3.60/0.99  
% 3.60/0.99  ------ Schedule dynamic 5 is on 
% 3.60/0.99  
% 3.60/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.60/0.99  
% 3.60/0.99  
% 3.60/0.99  ------ 
% 3.60/0.99  Current options:
% 3.60/0.99  ------ 
% 3.60/0.99  
% 3.60/0.99  ------ Input Options
% 3.60/0.99  
% 3.60/0.99  --out_options                           all
% 3.60/0.99  --tptp_safe_out                         true
% 3.60/0.99  --problem_path                          ""
% 3.60/0.99  --include_path                          ""
% 3.60/0.99  --clausifier                            res/vclausify_rel
% 3.60/0.99  --clausifier_options                    --mode clausify
% 3.60/0.99  --stdin                                 false
% 3.60/0.99  --stats_out                             all
% 3.60/0.99  
% 3.60/0.99  ------ General Options
% 3.60/0.99  
% 3.60/0.99  --fof                                   false
% 3.60/0.99  --time_out_real                         305.
% 3.60/0.99  --time_out_virtual                      -1.
% 3.60/0.99  --symbol_type_check                     false
% 3.60/0.99  --clausify_out                          false
% 3.60/0.99  --sig_cnt_out                           false
% 3.60/0.99  --trig_cnt_out                          false
% 3.60/0.99  --trig_cnt_out_tolerance                1.
% 3.60/0.99  --trig_cnt_out_sk_spl                   false
% 3.60/0.99  --abstr_cl_out                          false
% 3.60/0.99  
% 3.60/0.99  ------ Global Options
% 3.60/0.99  
% 3.60/0.99  --schedule                              default
% 3.60/0.99  --add_important_lit                     false
% 3.60/0.99  --prop_solver_per_cl                    1000
% 3.60/0.99  --min_unsat_core                        false
% 3.60/0.99  --soft_assumptions                      false
% 3.60/0.99  --soft_lemma_size                       3
% 3.60/0.99  --prop_impl_unit_size                   0
% 3.60/0.99  --prop_impl_unit                        []
% 3.60/0.99  --share_sel_clauses                     true
% 3.60/0.99  --reset_solvers                         false
% 3.60/0.99  --bc_imp_inh                            [conj_cone]
% 3.60/0.99  --conj_cone_tolerance                   3.
% 3.60/0.99  --extra_neg_conj                        none
% 3.60/0.99  --large_theory_mode                     true
% 3.60/0.99  --prolific_symb_bound                   200
% 3.60/0.99  --lt_threshold                          2000
% 3.60/0.99  --clause_weak_htbl                      true
% 3.60/0.99  --gc_record_bc_elim                     false
% 3.60/0.99  
% 3.60/0.99  ------ Preprocessing Options
% 3.60/0.99  
% 3.60/0.99  --preprocessing_flag                    true
% 3.60/0.99  --time_out_prep_mult                    0.1
% 3.60/0.99  --splitting_mode                        input
% 3.60/0.99  --splitting_grd                         true
% 3.60/0.99  --splitting_cvd                         false
% 3.60/0.99  --splitting_cvd_svl                     false
% 3.60/0.99  --splitting_nvd                         32
% 3.60/0.99  --sub_typing                            true
% 3.60/0.99  --prep_gs_sim                           true
% 3.60/0.99  --prep_unflatten                        true
% 3.60/0.99  --prep_res_sim                          true
% 3.60/0.99  --prep_upred                            true
% 3.60/0.99  --prep_sem_filter                       exhaustive
% 3.60/0.99  --prep_sem_filter_out                   false
% 3.60/0.99  --pred_elim                             true
% 3.60/0.99  --res_sim_input                         true
% 3.60/0.99  --eq_ax_congr_red                       true
% 3.60/0.99  --pure_diseq_elim                       true
% 3.60/0.99  --brand_transform                       false
% 3.60/0.99  --non_eq_to_eq                          false
% 3.60/0.99  --prep_def_merge                        true
% 3.60/0.99  --prep_def_merge_prop_impl              false
% 3.60/0.99  --prep_def_merge_mbd                    true
% 3.60/0.99  --prep_def_merge_tr_red                 false
% 3.60/0.99  --prep_def_merge_tr_cl                  false
% 3.60/0.99  --smt_preprocessing                     true
% 3.60/0.99  --smt_ac_axioms                         fast
% 3.60/0.99  --preprocessed_out                      false
% 3.60/0.99  --preprocessed_stats                    false
% 3.60/0.99  
% 3.60/0.99  ------ Abstraction refinement Options
% 3.60/0.99  
% 3.60/0.99  --abstr_ref                             []
% 3.60/0.99  --abstr_ref_prep                        false
% 3.60/0.99  --abstr_ref_until_sat                   false
% 3.60/0.99  --abstr_ref_sig_restrict                funpre
% 3.60/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.60/0.99  --abstr_ref_under                       []
% 3.60/0.99  
% 3.60/0.99  ------ SAT Options
% 3.60/0.99  
% 3.60/0.99  --sat_mode                              false
% 3.60/0.99  --sat_fm_restart_options                ""
% 3.60/0.99  --sat_gr_def                            false
% 3.60/0.99  --sat_epr_types                         true
% 3.60/0.99  --sat_non_cyclic_types                  false
% 3.60/0.99  --sat_finite_models                     false
% 3.60/0.99  --sat_fm_lemmas                         false
% 3.60/0.99  --sat_fm_prep                           false
% 3.60/0.99  --sat_fm_uc_incr                        true
% 3.60/0.99  --sat_out_model                         small
% 3.60/0.99  --sat_out_clauses                       false
% 3.60/0.99  
% 3.60/0.99  ------ QBF Options
% 3.60/0.99  
% 3.60/0.99  --qbf_mode                              false
% 3.60/0.99  --qbf_elim_univ                         false
% 3.60/0.99  --qbf_dom_inst                          none
% 3.60/0.99  --qbf_dom_pre_inst                      false
% 3.60/0.99  --qbf_sk_in                             false
% 3.60/0.99  --qbf_pred_elim                         true
% 3.60/0.99  --qbf_split                             512
% 3.60/0.99  
% 3.60/0.99  ------ BMC1 Options
% 3.60/0.99  
% 3.60/0.99  --bmc1_incremental                      false
% 3.60/0.99  --bmc1_axioms                           reachable_all
% 3.60/0.99  --bmc1_min_bound                        0
% 3.60/0.99  --bmc1_max_bound                        -1
% 3.60/0.99  --bmc1_max_bound_default                -1
% 3.60/0.99  --bmc1_symbol_reachability              true
% 3.60/0.99  --bmc1_property_lemmas                  false
% 3.60/0.99  --bmc1_k_induction                      false
% 3.60/0.99  --bmc1_non_equiv_states                 false
% 3.60/0.99  --bmc1_deadlock                         false
% 3.60/0.99  --bmc1_ucm                              false
% 3.60/0.99  --bmc1_add_unsat_core                   none
% 3.60/0.99  --bmc1_unsat_core_children              false
% 3.60/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.60/0.99  --bmc1_out_stat                         full
% 3.60/0.99  --bmc1_ground_init                      false
% 3.60/0.99  --bmc1_pre_inst_next_state              false
% 3.60/0.99  --bmc1_pre_inst_state                   false
% 3.60/0.99  --bmc1_pre_inst_reach_state             false
% 3.60/0.99  --bmc1_out_unsat_core                   false
% 3.60/0.99  --bmc1_aig_witness_out                  false
% 3.60/0.99  --bmc1_verbose                          false
% 3.60/0.99  --bmc1_dump_clauses_tptp                false
% 3.60/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.60/0.99  --bmc1_dump_file                        -
% 3.60/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.60/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.60/0.99  --bmc1_ucm_extend_mode                  1
% 3.60/0.99  --bmc1_ucm_init_mode                    2
% 3.60/0.99  --bmc1_ucm_cone_mode                    none
% 3.60/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.60/0.99  --bmc1_ucm_relax_model                  4
% 3.60/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.60/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.60/0.99  --bmc1_ucm_layered_model                none
% 3.60/0.99  --bmc1_ucm_max_lemma_size               10
% 3.60/0.99  
% 3.60/0.99  ------ AIG Options
% 3.60/0.99  
% 3.60/0.99  --aig_mode                              false
% 3.60/0.99  
% 3.60/0.99  ------ Instantiation Options
% 3.60/0.99  
% 3.60/0.99  --instantiation_flag                    true
% 3.60/0.99  --inst_sos_flag                         false
% 3.60/0.99  --inst_sos_phase                        true
% 3.60/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.60/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.60/0.99  --inst_lit_sel_side                     none
% 3.60/0.99  --inst_solver_per_active                1400
% 3.60/0.99  --inst_solver_calls_frac                1.
% 3.60/0.99  --inst_passive_queue_type               priority_queues
% 3.60/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.60/0.99  --inst_passive_queues_freq              [25;2]
% 3.60/0.99  --inst_dismatching                      true
% 3.60/0.99  --inst_eager_unprocessed_to_passive     true
% 3.60/0.99  --inst_prop_sim_given                   true
% 3.60/0.99  --inst_prop_sim_new                     false
% 3.60/0.99  --inst_subs_new                         false
% 3.60/0.99  --inst_eq_res_simp                      false
% 3.60/0.99  --inst_subs_given                       false
% 3.60/0.99  --inst_orphan_elimination               true
% 3.60/0.99  --inst_learning_loop_flag               true
% 3.60/0.99  --inst_learning_start                   3000
% 3.60/0.99  --inst_learning_factor                  2
% 3.60/0.99  --inst_start_prop_sim_after_learn       3
% 3.60/0.99  --inst_sel_renew                        solver
% 3.60/0.99  --inst_lit_activity_flag                true
% 3.60/0.99  --inst_restr_to_given                   false
% 3.60/0.99  --inst_activity_threshold               500
% 3.60/0.99  --inst_out_proof                        true
% 3.60/0.99  
% 3.60/0.99  ------ Resolution Options
% 3.60/0.99  
% 3.60/0.99  --resolution_flag                       false
% 3.60/0.99  --res_lit_sel                           adaptive
% 3.60/0.99  --res_lit_sel_side                      none
% 3.60/0.99  --res_ordering                          kbo
% 3.60/0.99  --res_to_prop_solver                    active
% 3.60/0.99  --res_prop_simpl_new                    false
% 3.60/0.99  --res_prop_simpl_given                  true
% 3.60/0.99  --res_passive_queue_type                priority_queues
% 3.60/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.60/0.99  --res_passive_queues_freq               [15;5]
% 3.60/0.99  --res_forward_subs                      full
% 3.60/0.99  --res_backward_subs                     full
% 3.60/0.99  --res_forward_subs_resolution           true
% 3.60/0.99  --res_backward_subs_resolution          true
% 3.60/0.99  --res_orphan_elimination                true
% 3.60/0.99  --res_time_limit                        2.
% 3.60/0.99  --res_out_proof                         true
% 3.60/0.99  
% 3.60/0.99  ------ Superposition Options
% 3.60/0.99  
% 3.60/0.99  --superposition_flag                    true
% 3.60/0.99  --sup_passive_queue_type                priority_queues
% 3.60/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.60/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.60/0.99  --demod_completeness_check              fast
% 3.60/0.99  --demod_use_ground                      true
% 3.60/0.99  --sup_to_prop_solver                    passive
% 3.60/0.99  --sup_prop_simpl_new                    true
% 3.60/0.99  --sup_prop_simpl_given                  true
% 3.60/0.99  --sup_fun_splitting                     false
% 3.60/0.99  --sup_smt_interval                      50000
% 3.60/0.99  
% 3.60/0.99  ------ Superposition Simplification Setup
% 3.60/0.99  
% 3.60/0.99  --sup_indices_passive                   []
% 3.60/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.60/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.60/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.60/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.60/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.60/0.99  --sup_full_bw                           [BwDemod]
% 3.60/0.99  --sup_immed_triv                        [TrivRules]
% 3.60/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.60/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.60/0.99  --sup_immed_bw_main                     []
% 3.60/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.60/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.60/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.60/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.60/0.99  
% 3.60/0.99  ------ Combination Options
% 3.60/0.99  
% 3.60/0.99  --comb_res_mult                         3
% 3.60/0.99  --comb_sup_mult                         2
% 3.60/0.99  --comb_inst_mult                        10
% 3.60/0.99  
% 3.60/0.99  ------ Debug Options
% 3.60/0.99  
% 3.60/0.99  --dbg_backtrace                         false
% 3.60/0.99  --dbg_dump_prop_clauses                 false
% 3.60/0.99  --dbg_dump_prop_clauses_file            -
% 3.60/0.99  --dbg_out_stat                          false
% 3.60/0.99  
% 3.60/0.99  
% 3.60/0.99  
% 3.60/0.99  
% 3.60/0.99  ------ Proving...
% 3.60/0.99  
% 3.60/0.99  
% 3.60/0.99  % SZS status Theorem for theBenchmark.p
% 3.60/0.99  
% 3.60/0.99   Resolution empty clause
% 3.60/0.99  
% 3.60/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.60/0.99  
% 3.60/0.99  fof(f18,conjecture,(
% 3.60/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.60/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.60/0.99  
% 3.60/0.99  fof(f19,negated_conjecture,(
% 3.60/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.60/0.99    inference(negated_conjecture,[],[f18])).
% 3.60/0.99  
% 3.60/0.99  fof(f39,plain,(
% 3.60/0.99    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.60/0.99    inference(ennf_transformation,[],[f19])).
% 3.60/0.99  
% 3.60/0.99  fof(f40,plain,(
% 3.60/0.99    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.60/0.99    inference(flattening,[],[f39])).
% 3.60/0.99  
% 3.60/0.99  fof(f48,plain,(
% 3.60/0.99    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 3.60/0.99    introduced(choice_axiom,[])).
% 3.60/0.99  
% 3.60/0.99  fof(f49,plain,(
% 3.60/0.99    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 3.60/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f40,f48])).
% 3.60/0.99  
% 3.60/0.99  fof(f84,plain,(
% 3.60/0.99    r1_tarski(sK2,sK0)),
% 3.60/0.99    inference(cnf_transformation,[],[f49])).
% 3.60/0.99  
% 3.60/0.99  fof(f14,axiom,(
% 3.60/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.60/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.60/0.99  
% 3.60/0.99  fof(f31,plain,(
% 3.60/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.60/0.99    inference(ennf_transformation,[],[f14])).
% 3.60/0.99  
% 3.60/0.99  fof(f32,plain,(
% 3.60/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.60/0.99    inference(flattening,[],[f31])).
% 3.60/0.99  
% 3.60/0.99  fof(f47,plain,(
% 3.60/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.60/0.99    inference(nnf_transformation,[],[f32])).
% 3.60/0.99  
% 3.60/0.99  fof(f69,plain,(
% 3.60/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.60/0.99    inference(cnf_transformation,[],[f47])).
% 3.60/0.99  
% 3.60/0.99  fof(f82,plain,(
% 3.60/0.99    v1_funct_2(sK3,sK0,sK1)),
% 3.60/0.99    inference(cnf_transformation,[],[f49])).
% 3.60/0.99  
% 3.60/0.99  fof(f83,plain,(
% 3.60/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.60/0.99    inference(cnf_transformation,[],[f49])).
% 3.60/0.99  
% 3.60/0.99  fof(f13,axiom,(
% 3.60/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.60/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.60/0.99  
% 3.60/0.99  fof(f30,plain,(
% 3.60/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.60/0.99    inference(ennf_transformation,[],[f13])).
% 3.60/0.99  
% 3.60/0.99  fof(f68,plain,(
% 3.60/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.60/0.99    inference(cnf_transformation,[],[f30])).
% 3.60/0.99  
% 3.60/0.99  fof(f9,axiom,(
% 3.60/0.99    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 3.60/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.60/0.99  
% 3.60/0.99  fof(f25,plain,(
% 3.60/0.99    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 3.60/0.99    inference(ennf_transformation,[],[f9])).
% 3.60/0.99  
% 3.60/0.99  fof(f26,plain,(
% 3.60/0.99    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.60/0.99    inference(flattening,[],[f25])).
% 3.60/0.99  
% 3.60/0.99  fof(f64,plain,(
% 3.60/0.99    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.60/0.99    inference(cnf_transformation,[],[f26])).
% 3.60/0.99  
% 3.60/0.99  fof(f11,axiom,(
% 3.60/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.60/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.60/0.99  
% 3.60/0.99  fof(f28,plain,(
% 3.60/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.60/0.99    inference(ennf_transformation,[],[f11])).
% 3.60/0.99  
% 3.60/0.99  fof(f66,plain,(
% 3.60/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.60/0.99    inference(cnf_transformation,[],[f28])).
% 3.60/0.99  
% 3.60/0.99  fof(f17,axiom,(
% 3.60/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 3.60/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.60/0.99  
% 3.60/0.99  fof(f37,plain,(
% 3.60/0.99    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.60/0.99    inference(ennf_transformation,[],[f17])).
% 3.60/0.99  
% 3.60/0.99  fof(f38,plain,(
% 3.60/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.60/0.99    inference(flattening,[],[f37])).
% 3.60/0.99  
% 3.60/0.99  fof(f80,plain,(
% 3.60/0.99    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.60/0.99    inference(cnf_transformation,[],[f38])).
% 3.60/0.99  
% 3.60/0.99  fof(f16,axiom,(
% 3.60/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 3.60/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.60/0.99  
% 3.60/0.99  fof(f35,plain,(
% 3.60/0.99    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.60/0.99    inference(ennf_transformation,[],[f16])).
% 3.60/0.99  
% 3.60/0.99  fof(f36,plain,(
% 3.60/0.99    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.60/0.99    inference(flattening,[],[f35])).
% 3.60/0.99  
% 3.60/0.99  fof(f77,plain,(
% 3.60/0.99    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.60/0.99    inference(cnf_transformation,[],[f36])).
% 3.60/0.99  
% 3.60/0.99  fof(f81,plain,(
% 3.60/0.99    v1_funct_1(sK3)),
% 3.60/0.99    inference(cnf_transformation,[],[f49])).
% 3.60/0.99  
% 3.60/0.99  fof(f15,axiom,(
% 3.60/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 3.60/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.60/0.99  
% 3.60/0.99  fof(f33,plain,(
% 3.60/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.60/0.99    inference(ennf_transformation,[],[f15])).
% 3.60/0.99  
% 3.60/0.99  fof(f34,plain,(
% 3.60/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.60/0.99    inference(flattening,[],[f33])).
% 3.60/0.99  
% 3.60/0.99  fof(f75,plain,(
% 3.60/0.99    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.60/0.99    inference(cnf_transformation,[],[f34])).
% 3.60/0.99  
% 3.60/0.99  fof(f79,plain,(
% 3.60/0.99    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.60/0.99    inference(cnf_transformation,[],[f38])).
% 3.60/0.99  
% 3.60/0.99  fof(f86,plain,(
% 3.60/0.99    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 3.60/0.99    inference(cnf_transformation,[],[f49])).
% 3.60/0.99  
% 3.60/0.99  fof(f12,axiom,(
% 3.60/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.60/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.60/0.99  
% 3.60/0.99  fof(f20,plain,(
% 3.60/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.60/0.99    inference(pure_predicate_removal,[],[f12])).
% 3.60/0.99  
% 3.60/0.99  fof(f29,plain,(
% 3.60/0.99    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.60/0.99    inference(ennf_transformation,[],[f20])).
% 3.60/0.99  
% 3.60/0.99  fof(f67,plain,(
% 3.60/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.60/0.99    inference(cnf_transformation,[],[f29])).
% 3.60/0.99  
% 3.60/0.99  fof(f6,axiom,(
% 3.60/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.60/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.60/0.99  
% 3.60/0.99  fof(f23,plain,(
% 3.60/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.60/0.99    inference(ennf_transformation,[],[f6])).
% 3.60/0.99  
% 3.60/0.99  fof(f46,plain,(
% 3.60/0.99    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.60/0.99    inference(nnf_transformation,[],[f23])).
% 3.60/0.99  
% 3.60/0.99  fof(f60,plain,(
% 3.60/0.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.60/0.99    inference(cnf_transformation,[],[f46])).
% 3.60/0.99  
% 3.60/0.99  fof(f76,plain,(
% 3.60/0.99    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.60/0.99    inference(cnf_transformation,[],[f34])).
% 3.60/0.99  
% 3.60/0.99  fof(f85,plain,(
% 3.60/0.99    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 3.60/0.99    inference(cnf_transformation,[],[f49])).
% 3.60/0.99  
% 3.60/0.99  fof(f4,axiom,(
% 3.60/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.60/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.60/0.99  
% 3.60/0.99  fof(f43,plain,(
% 3.60/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.60/0.99    inference(nnf_transformation,[],[f4])).
% 3.60/0.99  
% 3.60/0.99  fof(f44,plain,(
% 3.60/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.60/0.99    inference(flattening,[],[f43])).
% 3.60/0.99  
% 3.60/0.99  fof(f56,plain,(
% 3.60/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.60/0.99    inference(cnf_transformation,[],[f44])).
% 3.60/0.99  
% 3.60/0.99  fof(f90,plain,(
% 3.60/0.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.60/0.99    inference(equality_resolution,[],[f56])).
% 3.60/0.99  
% 3.60/0.99  fof(f74,plain,(
% 3.60/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.60/0.99    inference(cnf_transformation,[],[f47])).
% 3.60/0.99  
% 3.60/0.99  fof(f91,plain,(
% 3.60/0.99    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.60/0.99    inference(equality_resolution,[],[f74])).
% 3.60/0.99  
% 3.60/0.99  fof(f92,plain,(
% 3.60/0.99    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.60/0.99    inference(equality_resolution,[],[f91])).
% 3.60/0.99  
% 3.60/0.99  fof(f57,plain,(
% 3.60/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.60/0.99    inference(cnf_transformation,[],[f44])).
% 3.60/0.99  
% 3.60/0.99  fof(f89,plain,(
% 3.60/0.99    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.60/0.99    inference(equality_resolution,[],[f57])).
% 3.60/0.99  
% 3.60/0.99  fof(f5,axiom,(
% 3.60/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.60/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.60/0.99  
% 3.60/0.99  fof(f45,plain,(
% 3.60/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.60/0.99    inference(nnf_transformation,[],[f5])).
% 3.60/0.99  
% 3.60/0.99  fof(f59,plain,(
% 3.60/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.60/0.99    inference(cnf_transformation,[],[f45])).
% 3.60/0.99  
% 3.60/0.99  fof(f3,axiom,(
% 3.60/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.60/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.60/0.99  
% 3.60/0.99  fof(f54,plain,(
% 3.60/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.60/0.99    inference(cnf_transformation,[],[f3])).
% 3.60/0.99  
% 3.60/0.99  fof(f55,plain,(
% 3.60/0.99    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.60/0.99    inference(cnf_transformation,[],[f44])).
% 3.60/0.99  
% 3.60/0.99  fof(f1,axiom,(
% 3.60/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.60/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.60/0.99  
% 3.60/0.99  fof(f41,plain,(
% 3.60/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.60/0.99    inference(nnf_transformation,[],[f1])).
% 3.60/0.99  
% 3.60/0.99  fof(f42,plain,(
% 3.60/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.60/0.99    inference(flattening,[],[f41])).
% 3.60/0.99  
% 3.60/0.99  fof(f52,plain,(
% 3.60/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.60/0.99    inference(cnf_transformation,[],[f42])).
% 3.60/0.99  
% 3.60/0.99  fof(f2,axiom,(
% 3.60/0.99    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.60/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.60/0.99  
% 3.60/0.99  fof(f21,plain,(
% 3.60/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.60/0.99    inference(ennf_transformation,[],[f2])).
% 3.60/0.99  
% 3.60/0.99  fof(f22,plain,(
% 3.60/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.60/0.99    inference(flattening,[],[f21])).
% 3.60/0.99  
% 3.60/0.99  fof(f53,plain,(
% 3.60/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 3.60/0.99    inference(cnf_transformation,[],[f22])).
% 3.60/0.99  
% 3.60/0.99  fof(f72,plain,(
% 3.60/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.60/0.99    inference(cnf_transformation,[],[f47])).
% 3.60/0.99  
% 3.60/0.99  fof(f94,plain,(
% 3.60/0.99    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.60/0.99    inference(equality_resolution,[],[f72])).
% 3.60/0.99  
% 3.60/0.99  cnf(c_33,negated_conjecture,
% 3.60/0.99      ( r1_tarski(sK2,sK0) ),
% 3.60/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_1684,plain,
% 3.60/0.99      ( r1_tarski(sK2,sK0) = iProver_top ),
% 3.60/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_24,plain,
% 3.60/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.60/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.60/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.60/0.99      | k1_xboole_0 = X2 ),
% 3.60/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_35,negated_conjecture,
% 3.60/0.99      ( v1_funct_2(sK3,sK0,sK1) ),
% 3.60/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_621,plain,
% 3.60/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.60/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.60/0.99      | sK3 != X0
% 3.60/0.99      | sK1 != X2
% 3.60/0.99      | sK0 != X1
% 3.60/0.99      | k1_xboole_0 = X2 ),
% 3.60/0.99      inference(resolution_lifted,[status(thm)],[c_24,c_35]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_622,plain,
% 3.60/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.60/0.99      | k1_relset_1(sK0,sK1,sK3) = sK0
% 3.60/0.99      | k1_xboole_0 = sK1 ),
% 3.60/0.99      inference(unflattening,[status(thm)],[c_621]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_34,negated_conjecture,
% 3.60/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.60/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_624,plain,
% 3.60/0.99      ( k1_relset_1(sK0,sK1,sK3) = sK0 | k1_xboole_0 = sK1 ),
% 3.60/0.99      inference(global_propositional_subsumption,[status(thm)],[c_622,c_34]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_1683,plain,
% 3.60/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.60/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_18,plain,
% 3.60/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.60/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.60/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_1689,plain,
% 3.60/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.60/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.60/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_3544,plain,
% 3.60/0.99      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 3.60/0.99      inference(superposition,[status(thm)],[c_1683,c_1689]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_3856,plain,
% 3.60/0.99      ( k1_relat_1(sK3) = sK0 | sK1 = k1_xboole_0 ),
% 3.60/0.99      inference(superposition,[status(thm)],[c_624,c_3544]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_14,plain,
% 3.60/0.99      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 3.60/0.99      | ~ v1_relat_1(X1)
% 3.60/0.99      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 3.60/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_1692,plain,
% 3.60/0.99      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 3.60/0.99      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 3.60/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.60/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_4618,plain,
% 3.60/0.99      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 3.60/0.99      | sK1 = k1_xboole_0
% 3.60/0.99      | r1_tarski(X0,sK0) != iProver_top
% 3.60/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.60/0.99      inference(superposition,[status(thm)],[c_3856,c_1692]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_39,plain,
% 3.60/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.60/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_16,plain,
% 3.60/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 3.60/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_1970,plain,
% 3.60/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.60/0.99      | v1_relat_1(sK3) ),
% 3.60/0.99      inference(instantiation,[status(thm)],[c_16]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_1971,plain,
% 3.60/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.60/0.99      | v1_relat_1(sK3) = iProver_top ),
% 3.60/0.99      inference(predicate_to_equality,[status(thm)],[c_1970]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_5472,plain,
% 3.60/0.99      ( r1_tarski(X0,sK0) != iProver_top
% 3.60/0.99      | sK1 = k1_xboole_0
% 3.60/0.99      | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
% 3.60/0.99      inference(global_propositional_subsumption,
% 3.60/0.99                [status(thm)],
% 3.60/0.99                [c_4618,c_39,c_1971]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_5473,plain,
% 3.60/0.99      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 3.60/0.99      | sK1 = k1_xboole_0
% 3.60/0.99      | r1_tarski(X0,sK0) != iProver_top ),
% 3.60/0.99      inference(renaming,[status(thm)],[c_5472]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_5483,plain,
% 3.60/0.99      ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2 | sK1 = k1_xboole_0 ),
% 3.60/0.99      inference(superposition,[status(thm)],[c_1684,c_5473]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_28,plain,
% 3.60/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.60/0.99      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.60/0.99      | ~ v1_funct_1(X0)
% 3.60/0.99      | ~ v1_relat_1(X0) ),
% 3.60/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_1685,plain,
% 3.60/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
% 3.60/0.99      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 3.60/0.99      | v1_funct_1(X0) != iProver_top
% 3.60/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.60/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_5559,plain,
% 3.60/0.99      ( sK1 = k1_xboole_0
% 3.60/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 3.60/0.99      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
% 3.60/0.99      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
% 3.60/0.99      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.60/0.99      inference(superposition,[status(thm)],[c_5483,c_1685]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_27,plain,
% 3.60/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.60/0.99      | ~ v1_funct_1(X0)
% 3.60/0.99      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 3.60/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_1686,plain,
% 3.60/0.99      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 3.60/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.60/0.99      | v1_funct_1(X2) != iProver_top ),
% 3.60/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_5716,plain,
% 3.60/0.99      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
% 3.60/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.60/0.99      inference(superposition,[status(thm)],[c_1683,c_1686]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_36,negated_conjecture,
% 3.60/0.99      ( v1_funct_1(sK3) ),
% 3.60/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_2044,plain,
% 3.60/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.60/0.99      | ~ v1_funct_1(sK3)
% 3.60/0.99      | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
% 3.60/0.99      inference(instantiation,[status(thm)],[c_27]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_2155,plain,
% 3.60/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.60/0.99      | ~ v1_funct_1(sK3)
% 3.60/0.99      | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 3.60/0.99      inference(instantiation,[status(thm)],[c_2044]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_5833,plain,
% 3.60/0.99      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 3.60/0.99      inference(global_propositional_subsumption,
% 3.60/0.99                [status(thm)],
% 3.60/0.99                [c_5716,c_36,c_34,c_2155]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_26,plain,
% 3.60/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.60/0.99      | ~ v1_funct_1(X0)
% 3.60/0.99      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
% 3.60/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_1687,plain,
% 3.60/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.60/0.99      | v1_funct_1(X0) != iProver_top
% 3.60/0.99      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
% 3.60/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_4649,plain,
% 3.60/0.99      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
% 3.60/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.60/0.99      inference(superposition,[status(thm)],[c_1683,c_1687]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_37,plain,
% 3.60/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 3.60/0.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_2020,plain,
% 3.60/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.60/0.99      | v1_funct_1(k2_partfun1(X0,X1,sK3,X2))
% 3.60/0.99      | ~ v1_funct_1(sK3) ),
% 3.60/0.99      inference(instantiation,[status(thm)],[c_26]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_2123,plain,
% 3.60/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.60/0.99      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
% 3.60/0.99      | ~ v1_funct_1(sK3) ),
% 3.60/0.99      inference(instantiation,[status(thm)],[c_2020]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_2124,plain,
% 3.60/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.60/0.99      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
% 3.60/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.60/0.99      inference(predicate_to_equality,[status(thm)],[c_2123]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_5144,plain,
% 3.60/0.99      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
% 3.60/0.99      inference(global_propositional_subsumption,
% 3.60/0.99                [status(thm)],
% 3.60/0.99                [c_4649,c_37,c_39,c_2124]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_5842,plain,
% 3.60/0.99      ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 3.60/0.99      inference(demodulation,[status(thm)],[c_5833,c_5144]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_6612,plain,
% 3.60/0.99      ( sK1 = k1_xboole_0
% 3.60/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 3.60/0.99      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
% 3.60/0.99      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.60/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_5559,c_5842]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_29,plain,
% 3.60/0.99      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 3.60/0.99      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.60/0.99      | ~ v1_funct_1(X0)
% 3.60/0.99      | ~ v1_relat_1(X0) ),
% 3.60/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_31,negated_conjecture,
% 3.60/0.99      ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
% 3.60/0.99      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.60/0.99      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
% 3.60/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_632,plain,
% 3.60/0.99      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.60/0.99      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.60/0.99      | ~ v1_funct_1(X0)
% 3.60/0.99      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.60/0.99      | ~ v1_relat_1(X0)
% 3.60/0.99      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 3.60/0.99      | k1_relat_1(X0) != sK2
% 3.60/0.99      | sK1 != X1 ),
% 3.60/0.99      inference(resolution_lifted,[status(thm)],[c_29,c_31]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_633,plain,
% 3.60/0.99      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.60/0.99      | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
% 3.60/0.99      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.60/0.99      | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.60/0.99      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
% 3.60/0.99      inference(unflattening,[status(thm)],[c_632]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_17,plain,
% 3.60/0.99      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.60/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_11,plain,
% 3.60/0.99      ( ~ v5_relat_1(X0,X1) | r1_tarski(k2_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 3.60/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_420,plain,
% 3.60/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.60/0.99      | r1_tarski(k2_relat_1(X0),X2)
% 3.60/0.99      | ~ v1_relat_1(X0) ),
% 3.60/0.99      inference(resolution,[status(thm)],[c_17,c_11]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_424,plain,
% 3.60/0.99      ( r1_tarski(k2_relat_1(X0),X2)
% 3.60/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.60/0.99      inference(global_propositional_subsumption,[status(thm)],[c_420,c_16]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_425,plain,
% 3.60/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.60/0.99      | r1_tarski(k2_relat_1(X0),X2) ),
% 3.60/0.99      inference(renaming,[status(thm)],[c_424]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_645,plain,
% 3.60/0.99      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.60/0.99      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.60/0.99      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
% 3.60/0.99      inference(forward_subsumption_resolution,
% 3.60/0.99                [status(thm)],
% 3.60/0.99                [c_633,c_16,c_425]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_1672,plain,
% 3.60/0.99      ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 3.60/0.99      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.60/0.99      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.60/0.99      inference(predicate_to_equality,[status(thm)],[c_645]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_5840,plain,
% 3.60/0.99      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 3.60/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.60/0.99      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.60/0.99      inference(demodulation,[status(thm)],[c_5833,c_1672]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_5856,plain,
% 3.60/0.99      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 3.60/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.60/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_5840,c_5842]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_9554,plain,
% 3.60/0.99      ( sK1 = k1_xboole_0
% 3.60/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.60/0.99      inference(superposition,[status(thm)],[c_5483,c_5856]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_9700,plain,
% 3.60/0.99      ( sK1 = k1_xboole_0
% 3.60/0.99      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
% 3.60/0.99      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.60/0.99      inference(superposition,[status(thm)],[c_6612,c_9554]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_25,plain,
% 3.60/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.60/0.99      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.60/0.99      | ~ v1_funct_1(X0) ),
% 3.60/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_1688,plain,
% 3.60/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.60/0.99      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 3.60/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.60/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_6694,plain,
% 3.60/0.99      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 3.60/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.60/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.60/0.99      inference(superposition,[status(thm)],[c_5833,c_1688]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_7691,plain,
% 3.60/0.99      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.60/0.99      inference(global_propositional_subsumption,
% 3.60/0.99                [status(thm)],
% 3.60/0.99                [c_6694,c_37,c_39]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_1690,plain,
% 3.60/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.60/0.99      | v1_relat_1(X0) = iProver_top ),
% 3.60/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_7703,plain,
% 3.60/0.99      ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 3.60/0.99      inference(superposition,[status(thm)],[c_7691,c_1690]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_1681,plain,
% 3.60/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.60/0.99      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 3.60/0.99      inference(predicate_to_equality,[status(thm)],[c_425]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_7702,plain,
% 3.60/0.99      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) = iProver_top ),
% 3.60/0.99      inference(superposition,[status(thm)],[c_7691,c_1681]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_11692,plain,
% 3.60/0.99      ( sK1 = k1_xboole_0 ),
% 3.60/0.99      inference(forward_subsumption_resolution,
% 3.60/0.99                [status(thm)],
% 3.60/0.99                [c_9700,c_7703,c_7702]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_7700,plain,
% 3.60/0.99      ( k1_relset_1(sK0,sK1,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
% 3.60/0.99      inference(superposition,[status(thm)],[c_7691,c_1689]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_11712,plain,
% 3.60/0.99      ( k1_relset_1(sK0,k1_xboole_0,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
% 3.60/0.99      inference(demodulation,[status(thm)],[c_11692,c_7700]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_32,negated_conjecture,
% 3.60/0.99      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 3.60/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_11733,plain,
% 3.60/0.99      ( sK0 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.60/0.99      inference(demodulation,[status(thm)],[c_11692,c_32]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_11734,plain,
% 3.60/0.99      ( sK0 = k1_xboole_0 ),
% 3.60/0.99      inference(equality_resolution_simp,[status(thm)],[c_11733]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_11814,plain,
% 3.60/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
% 3.60/0.99      inference(light_normalisation,[status(thm)],[c_11712,c_11734]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_11716,plain,
% 3.60/0.99      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
% 3.60/0.99      inference(demodulation,[status(thm)],[c_11692,c_7691]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_11791,plain,
% 3.60/0.99      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.60/0.99      inference(light_normalisation,[status(thm)],[c_11716,c_11734]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_6,plain,
% 3.60/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.60/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_11793,plain,
% 3.60/0.99      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.60/0.99      inference(demodulation,[status(thm)],[c_11791,c_6]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_19,plain,
% 3.60/0.99      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
% 3.60/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 3.60/0.99      | k1_xboole_0 = X0 ),
% 3.60/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_449,plain,
% 3.60/0.99      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.60/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 3.60/0.99      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.60/0.99      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 3.60/0.99      | sK2 != X0
% 3.60/0.99      | sK1 != k1_xboole_0
% 3.60/0.99      | k1_xboole_0 = X0 ),
% 3.60/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_31]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_450,plain,
% 3.60/0.99      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.60/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
% 3.60/0.99      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.60/0.99      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 3.60/0.99      | sK1 != k1_xboole_0
% 3.60/0.99      | k1_xboole_0 = sK2 ),
% 3.60/0.99      inference(unflattening,[status(thm)],[c_449]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_1680,plain,
% 3.60/0.99      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 3.60/0.99      | sK1 != k1_xboole_0
% 3.60/0.99      | k1_xboole_0 = sK2
% 3.60/0.99      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.60/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
% 3.60/0.99      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.60/0.99      inference(predicate_to_equality,[status(thm)],[c_450]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_5,plain,
% 3.60/0.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.60/0.99      inference(cnf_transformation,[],[f89]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_1869,plain,
% 3.60/0.99      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 3.60/0.99      | sK2 = k1_xboole_0
% 3.60/0.99      | sK1 != k1_xboole_0
% 3.60/0.99      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.60/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.60/0.99      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.60/0.99      inference(demodulation,[status(thm)],[c_1680,c_5]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_8,plain,
% 3.60/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.60/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_104,plain,
% 3.60/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.60/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 3.60/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_106,plain,
% 3.60/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.60/0.99      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.60/0.99      inference(instantiation,[status(thm)],[c_104]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_4,plain,
% 3.60/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 3.60/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_109,plain,
% 3.60/0.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.60/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_111,plain,
% 3.60/0.99      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.60/0.99      inference(instantiation,[status(thm)],[c_109]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_2250,plain,
% 3.60/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.60/0.99      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.60/0.99      | ~ v1_funct_1(sK3) ),
% 3.60/0.99      inference(instantiation,[status(thm)],[c_2123]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_2251,plain,
% 3.60/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.60/0.99      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) = iProver_top
% 3.60/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.60/0.99      inference(predicate_to_equality,[status(thm)],[c_2250]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_2322,plain,
% 3.60/0.99      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 3.60/0.99      | sK2 = k1_xboole_0
% 3.60/0.99      | sK1 != k1_xboole_0
% 3.60/0.99      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.60/0.99      inference(global_propositional_subsumption,
% 3.60/0.99                [status(thm)],
% 3.60/0.99                [c_1869,c_37,c_39,c_106,c_111,c_2251]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_5838,plain,
% 3.60/0.99      ( k7_relat_1(sK3,sK2) != k1_xboole_0
% 3.60/0.99      | sK2 = k1_xboole_0
% 3.60/0.99      | sK1 != k1_xboole_0
% 3.60/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.60/0.99      inference(demodulation,[status(thm)],[c_5833,c_2322]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_7,plain,
% 3.60/0.99      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.60/0.99      | k1_xboole_0 = X1
% 3.60/0.99      | k1_xboole_0 = X0 ),
% 3.60/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_107,plain,
% 3.60/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.60/0.99      | k1_xboole_0 = k1_xboole_0 ),
% 3.60/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_108,plain,
% 3.60/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.60/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_110,plain,
% 3.60/0.99      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 3.60/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_0,plain,
% 3.60/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.60/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_1992,plain,
% 3.60/0.99      ( ~ r1_tarski(sK2,k1_xboole_0)
% 3.60/0.99      | ~ r1_tarski(k1_xboole_0,sK2)
% 3.60/0.99      | sK2 = k1_xboole_0 ),
% 3.60/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_992,plain,
% 3.60/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.60/0.99      theory(equality) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_2260,plain,
% 3.60/0.99      ( ~ r1_tarski(X0,X1)
% 3.60/0.99      | r1_tarski(sK0,k1_xboole_0)
% 3.60/0.99      | sK0 != X0
% 3.60/0.99      | k1_xboole_0 != X1 ),
% 3.60/0.99      inference(instantiation,[status(thm)],[c_992]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_2262,plain,
% 3.60/0.99      ( r1_tarski(sK0,k1_xboole_0)
% 3.60/0.99      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 3.60/0.99      | sK0 != k1_xboole_0
% 3.60/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.60/0.99      inference(instantiation,[status(thm)],[c_2260]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_991,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_2008,plain,
% 3.60/0.99      ( sK0 != X0 | sK0 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 3.60/0.99      inference(instantiation,[status(thm)],[c_991]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_2345,plain,
% 3.60/0.99      ( sK0 != sK0 | sK0 = k1_xboole_0 | k1_xboole_0 != sK0 ),
% 3.60/0.99      inference(instantiation,[status(thm)],[c_2008]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_990,plain,( X0 = X0 ),theory(equality) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_2346,plain,
% 3.60/0.99      ( sK0 = sK0 ),
% 3.60/0.99      inference(instantiation,[status(thm)],[c_990]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_3,plain,
% 3.60/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 3.60/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_2182,plain,
% 3.60/0.99      ( ~ r1_tarski(X0,k1_xboole_0)
% 3.60/0.99      | ~ r1_tarski(sK2,X0)
% 3.60/0.99      | r1_tarski(sK2,k1_xboole_0) ),
% 3.60/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_2512,plain,
% 3.60/0.99      ( ~ r1_tarski(sK2,sK0)
% 3.60/0.99      | r1_tarski(sK2,k1_xboole_0)
% 3.60/0.99      | ~ r1_tarski(sK0,k1_xboole_0) ),
% 3.60/0.99      inference(instantiation,[status(thm)],[c_2182]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_3032,plain,
% 3.60/0.99      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 3.60/0.99      inference(instantiation,[status(thm)],[c_991]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_3033,plain,
% 3.60/0.99      ( sK1 != k1_xboole_0 | k1_xboole_0 = sK1 | k1_xboole_0 != k1_xboole_0 ),
% 3.60/0.99      inference(instantiation,[status(thm)],[c_3032]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_3932,plain,
% 3.60/0.99      ( r1_tarski(k1_xboole_0,sK2) ),
% 3.60/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_5969,plain,
% 3.60/0.99      ( sK2 = k1_xboole_0
% 3.60/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.60/0.99      inference(global_propositional_subsumption,
% 3.60/0.99                [status(thm)],
% 3.60/0.99                [c_5838,c_33,c_32,c_107,c_108,c_110,c_1992,c_2262,c_2345,
% 3.60/0.99                 c_2346,c_2512,c_3033,c_3932,c_5483,c_5856]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_11719,plain,
% 3.60/0.99      ( sK2 = k1_xboole_0
% 3.60/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
% 3.60/0.99      inference(demodulation,[status(thm)],[c_11692,c_5969]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_11782,plain,
% 3.60/0.99      ( sK2 = k1_xboole_0
% 3.60/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.60/0.99      inference(demodulation,[status(thm)],[c_11719,c_5]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_11795,plain,
% 3.60/0.99      ( sK2 = k1_xboole_0 ),
% 3.60/0.99      inference(backward_subsumption_resolution,
% 3.60/0.99                [status(thm)],
% 3.60/0.99                [c_11793,c_11782]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_21,plain,
% 3.60/0.99      ( v1_funct_2(X0,k1_xboole_0,X1)
% 3.60/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.60/0.99      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 3.60/0.99      inference(cnf_transformation,[],[f94]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_546,plain,
% 3.60/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.60/0.99      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.60/0.99      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.60/0.99      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 3.60/0.99      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 3.60/0.99      | sK2 != k1_xboole_0
% 3.60/0.99      | sK1 != X1 ),
% 3.60/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_31]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_547,plain,
% 3.60/0.99      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.60/0.99      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 3.60/0.99      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.60/0.99      | k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
% 3.60/0.99      | sK2 != k1_xboole_0 ),
% 3.60/0.99      inference(unflattening,[status(thm)],[c_546]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_1676,plain,
% 3.60/0.99      ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
% 3.60/0.99      | sK2 != k1_xboole_0
% 3.60/0.99      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.60/0.99      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
% 3.60/0.99      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.60/0.99      inference(predicate_to_equality,[status(thm)],[c_547]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_1882,plain,
% 3.60/0.99      ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
% 3.60/0.99      | sK2 != k1_xboole_0
% 3.60/0.99      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.60/0.99      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.60/0.99      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.60/0.99      inference(demodulation,[status(thm)],[c_1676,c_6]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_2390,plain,
% 3.60/0.99      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.60/0.99      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.60/0.99      | sK2 != k1_xboole_0
% 3.60/0.99      | k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0 ),
% 3.60/0.99      inference(global_propositional_subsumption,
% 3.60/0.99                [status(thm)],
% 3.60/0.99                [c_1882,c_37,c_39,c_2251]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_2391,plain,
% 3.60/0.99      ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
% 3.60/0.99      | sK2 != k1_xboole_0
% 3.60/0.99      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.60/0.99      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.60/0.99      inference(renaming,[status(thm)],[c_2390]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_5837,plain,
% 3.60/0.99      ( k1_relset_1(k1_xboole_0,sK1,k7_relat_1(sK3,sK2)) != k1_xboole_0
% 3.60/0.99      | sK2 != k1_xboole_0
% 3.60/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.60/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.60/0.99      inference(demodulation,[status(thm)],[c_5833,c_2391]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_6204,plain,
% 3.60/0.99      ( k1_relset_1(k1_xboole_0,sK1,k7_relat_1(sK3,sK2)) != k1_xboole_0
% 3.60/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.60/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.60/0.99      inference(global_propositional_subsumption,[status(thm)],[c_5837,c_5969]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_11718,plain,
% 3.60/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,sK2)) != k1_xboole_0
% 3.60/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
% 3.60/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.60/0.99      inference(demodulation,[status(thm)],[c_11692,c_6204]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_11788,plain,
% 3.60/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,sK2)) != k1_xboole_0
% 3.60/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.60/0.99      inference(demodulation,[status(thm)],[c_11718,c_5]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_11796,plain,
% 3.60/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,sK2)) != k1_xboole_0 ),
% 3.60/0.99      inference(backward_subsumption_resolution,
% 3.60/0.99                [status(thm)],
% 3.60/0.99                [c_11793,c_11788]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_11800,plain,
% 3.60/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0 ),
% 3.60/0.99      inference(demodulation,[status(thm)],[c_11795,c_11796]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_11816,plain,
% 3.60/0.99      ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0 ),
% 3.60/0.99      inference(demodulation,[status(thm)],[c_11814,c_11800]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_1696,plain,
% 3.60/0.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.60/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_5482,plain,
% 3.60/0.99      ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0
% 3.60/0.99      | sK1 = k1_xboole_0 ),
% 3.60/0.99      inference(superposition,[status(thm)],[c_1696,c_5473]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_2049,plain,
% 3.60/0.99      ( ~ r1_tarski(X0,k1_relat_1(sK3))
% 3.60/0.99      | ~ v1_relat_1(sK3)
% 3.60/0.99      | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
% 3.60/0.99      inference(instantiation,[status(thm)],[c_14]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_2051,plain,
% 3.60/0.99      ( ~ r1_tarski(k1_xboole_0,k1_relat_1(sK3))
% 3.60/0.99      | ~ v1_relat_1(sK3)
% 3.60/0.99      | k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
% 3.60/0.99      inference(instantiation,[status(thm)],[c_2049]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_2381,plain,
% 3.60/0.99      ( r1_tarski(k1_xboole_0,k1_relat_1(sK3)) ),
% 3.60/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_9091,plain,
% 3.60/0.99      ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
% 3.60/0.99      inference(global_propositional_subsumption,
% 3.60/0.99                [status(thm)],
% 3.60/0.99                [c_5482,c_34,c_1970,c_2051,c_2381]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_11819,plain,
% 3.60/0.99      ( k1_xboole_0 != k1_xboole_0 ),
% 3.60/0.99      inference(light_normalisation,[status(thm)],[c_11816,c_9091]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_11820,plain,
% 3.60/0.99      ( $false ),
% 3.60/0.99      inference(equality_resolution_simp,[status(thm)],[c_11819]) ).
% 3.60/0.99  
% 3.60/0.99  
% 3.60/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.60/0.99  
% 3.60/0.99  ------                               Statistics
% 3.60/0.99  
% 3.60/0.99  ------ General
% 3.60/0.99  
% 3.60/0.99  abstr_ref_over_cycles:                  0
% 3.60/0.99  abstr_ref_under_cycles:                 0
% 3.60/0.99  gc_basic_clause_elim:                   0
% 3.60/0.99  forced_gc_time:                         0
% 3.60/0.99  parsing_time:                           0.008
% 3.60/0.99  unif_index_cands_time:                  0.
% 3.60/0.99  unif_index_add_time:                    0.
% 3.60/0.99  orderings_time:                         0.
% 3.60/0.99  out_proof_time:                         0.013
% 3.60/0.99  total_time:                             0.303
% 3.60/0.99  num_of_symbols:                         49
% 3.60/0.99  num_of_terms:                           9590
% 3.60/0.99  
% 3.60/0.99  ------ Preprocessing
% 3.60/0.99  
% 3.60/0.99  num_of_splits:                          0
% 3.60/0.99  num_of_split_atoms:                     0
% 3.60/0.99  num_of_reused_defs:                     0
% 3.60/0.99  num_eq_ax_congr_red:                    7
% 3.60/0.99  num_of_sem_filtered_clauses:            1
% 3.60/0.99  num_of_subtypes:                        0
% 3.60/0.99  monotx_restored_types:                  0
% 3.60/0.99  sat_num_of_epr_types:                   0
% 3.60/0.99  sat_num_of_non_cyclic_types:            0
% 3.60/0.99  sat_guarded_non_collapsed_types:        0
% 3.60/0.99  num_pure_diseq_elim:                    0
% 3.60/0.99  simp_replaced_by:                       0
% 3.60/0.99  res_preprocessed:                       167
% 3.60/0.99  prep_upred:                             0
% 3.60/0.99  prep_unflattend:                        43
% 3.60/0.99  smt_new_axioms:                         0
% 3.60/0.99  pred_elim_cands:                        4
% 3.60/0.99  pred_elim:                              2
% 3.60/0.99  pred_elim_cl:                           0
% 3.60/0.99  pred_elim_cycles:                       4
% 3.60/0.99  merged_defs:                            8
% 3.60/0.99  merged_defs_ncl:                        0
% 3.60/0.99  bin_hyper_res:                          8
% 3.60/0.99  prep_cycles:                            4
% 3.60/0.99  pred_elim_time:                         0.009
% 3.60/0.99  splitting_time:                         0.
% 3.60/0.99  sem_filter_time:                        0.
% 3.60/0.99  monotx_time:                            0.
% 3.60/0.99  subtype_inf_time:                       0.
% 3.60/0.99  
% 3.60/0.99  ------ Problem properties
% 3.60/0.99  
% 3.60/0.99  clauses:                                35
% 3.60/0.99  conjectures:                            4
% 3.60/0.99  epr:                                    7
% 3.60/0.99  horn:                                   30
% 3.60/0.99  ground:                                 12
% 3.60/0.99  unary:                                  8
% 3.60/0.99  binary:                                 9
% 3.60/0.99  lits:                                   94
% 3.60/0.99  lits_eq:                                35
% 3.60/0.99  fd_pure:                                0
% 3.60/0.99  fd_pseudo:                              0
% 3.60/0.99  fd_cond:                                3
% 3.60/0.99  fd_pseudo_cond:                         1
% 3.60/0.99  ac_symbols:                             0
% 3.60/0.99  
% 3.60/0.99  ------ Propositional Solver
% 3.60/0.99  
% 3.60/0.99  prop_solver_calls:                      27
% 3.60/0.99  prop_fast_solver_calls:                 1322
% 3.60/0.99  smt_solver_calls:                       0
% 3.60/0.99  smt_fast_solver_calls:                  0
% 3.60/0.99  prop_num_of_clauses:                    4191
% 3.60/0.99  prop_preprocess_simplified:             11024
% 3.60/0.99  prop_fo_subsumed:                       34
% 3.60/0.99  prop_solver_time:                       0.
% 3.60/0.99  smt_solver_time:                        0.
% 3.60/0.99  smt_fast_solver_time:                   0.
% 3.60/0.99  prop_fast_solver_time:                  0.
% 3.60/0.99  prop_unsat_core_time:                   0.
% 3.60/0.99  
% 3.60/0.99  ------ QBF
% 3.60/0.99  
% 3.60/0.99  qbf_q_res:                              0
% 3.60/0.99  qbf_num_tautologies:                    0
% 3.60/0.99  qbf_prep_cycles:                        0
% 3.60/0.99  
% 3.60/0.99  ------ BMC1
% 3.60/0.99  
% 3.60/0.99  bmc1_current_bound:                     -1
% 3.60/0.99  bmc1_last_solved_bound:                 -1
% 3.60/0.99  bmc1_unsat_core_size:                   -1
% 3.60/0.99  bmc1_unsat_core_parents_size:           -1
% 3.60/0.99  bmc1_merge_next_fun:                    0
% 3.60/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.60/0.99  
% 3.60/0.99  ------ Instantiation
% 3.60/0.99  
% 3.60/0.99  inst_num_of_clauses:                    1231
% 3.60/0.99  inst_num_in_passive:                    265
% 3.60/0.99  inst_num_in_active:                     574
% 3.60/0.99  inst_num_in_unprocessed:                393
% 3.60/0.99  inst_num_of_loops:                      600
% 3.60/0.99  inst_num_of_learning_restarts:          0
% 3.60/0.99  inst_num_moves_active_passive:          25
% 3.60/0.99  inst_lit_activity:                      0
% 3.60/0.99  inst_lit_activity_moves:                0
% 3.60/0.99  inst_num_tautologies:                   0
% 3.60/0.99  inst_num_prop_implied:                  0
% 3.60/0.99  inst_num_existing_simplified:           0
% 3.60/0.99  inst_num_eq_res_simplified:             0
% 3.60/0.99  inst_num_child_elim:                    0
% 3.60/0.99  inst_num_of_dismatching_blockings:      532
% 3.60/0.99  inst_num_of_non_proper_insts:           1620
% 3.60/0.99  inst_num_of_duplicates:                 0
% 3.60/1.00  inst_inst_num_from_inst_to_res:         0
% 3.60/1.00  inst_dismatching_checking_time:         0.
% 3.60/1.00  
% 3.60/1.00  ------ Resolution
% 3.60/1.00  
% 3.60/1.00  res_num_of_clauses:                     0
% 3.60/1.00  res_num_in_passive:                     0
% 3.60/1.00  res_num_in_active:                      0
% 3.60/1.00  res_num_of_loops:                       171
% 3.60/1.00  res_forward_subset_subsumed:            72
% 3.60/1.00  res_backward_subset_subsumed:           2
% 3.60/1.00  res_forward_subsumed:                   0
% 3.60/1.00  res_backward_subsumed:                  0
% 3.60/1.00  res_forward_subsumption_resolution:     5
% 3.60/1.00  res_backward_subsumption_resolution:    0
% 3.60/1.00  res_clause_to_clause_subsumption:       696
% 3.60/1.00  res_orphan_elimination:                 0
% 3.60/1.00  res_tautology_del:                      152
% 3.60/1.00  res_num_eq_res_simplified:              1
% 3.60/1.00  res_num_sel_changes:                    0
% 3.60/1.00  res_moves_from_active_to_pass:          0
% 3.60/1.00  
% 3.60/1.00  ------ Superposition
% 3.60/1.00  
% 3.60/1.00  sup_time_total:                         0.
% 3.60/1.00  sup_time_generating:                    0.
% 3.60/1.00  sup_time_sim_full:                      0.
% 3.60/1.00  sup_time_sim_immed:                     0.
% 3.60/1.00  
% 3.60/1.00  sup_num_of_clauses:                     152
% 3.60/1.00  sup_num_in_active:                      62
% 3.60/1.00  sup_num_in_passive:                     90
% 3.60/1.00  sup_num_of_loops:                       119
% 3.60/1.00  sup_fw_superposition:                   115
% 3.60/1.00  sup_bw_superposition:                   108
% 3.60/1.00  sup_immediate_simplified:               28
% 3.60/1.00  sup_given_eliminated:                   0
% 3.60/1.00  comparisons_done:                       0
% 3.60/1.00  comparisons_avoided:                    34
% 3.60/1.00  
% 3.60/1.00  ------ Simplifications
% 3.60/1.00  
% 3.60/1.00  
% 3.60/1.00  sim_fw_subset_subsumed:                 8
% 3.60/1.00  sim_bw_subset_subsumed:                 18
% 3.60/1.00  sim_fw_subsumed:                        8
% 3.60/1.00  sim_bw_subsumed:                        0
% 3.60/1.00  sim_fw_subsumption_res:                 9
% 3.60/1.00  sim_bw_subsumption_res:                 2
% 3.60/1.00  sim_tautology_del:                      7
% 3.60/1.00  sim_eq_tautology_del:                   9
% 3.60/1.00  sim_eq_res_simp:                        3
% 3.60/1.00  sim_fw_demodulated:                     17
% 3.60/1.00  sim_bw_demodulated:                     51
% 3.60/1.00  sim_light_normalised:                   17
% 3.60/1.00  sim_joinable_taut:                      0
% 3.60/1.00  sim_joinable_simp:                      0
% 3.60/1.00  sim_ac_normalised:                      0
% 3.60/1.00  sim_smt_subsumption:                    0
% 3.60/1.00  
%------------------------------------------------------------------------------
