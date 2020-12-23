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

% Result     : Theorem 3.11s
% Output     : CNFRefutation 3.11s
% Verified   : 
% Statistics : Number of formulae       :  215 (10188 expanded)
%              Number of clauses        :  142 (3334 expanded)
%              Number of leaves         :   16 (1902 expanded)
%              Depth                    :   28
%              Number of atoms          :  612 (56644 expanded)
%              Number of equality atoms :  314 (15035 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
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

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

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
    inference(ennf_transformation,[],[f18])).

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

fof(f50,plain,
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
   => ( ( ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
        | ~ v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK3,sK2)
        | ~ v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3)) )
      & ( k1_xboole_0 = sK1
        | k1_xboole_0 != sK2 )
      & r1_tarski(sK3,sK1)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK4,sK1,sK2)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
      | ~ v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK3,sK2)
      | ~ v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3)) )
    & ( k1_xboole_0 = sK1
      | k1_xboole_0 != sK2 )
    & r1_tarski(sK3,sK1)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f38,f50])).

fof(f87,plain,(
    r1_tarski(sK3,sK1) ),
    inference(cnf_transformation,[],[f51])).

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

fof(f29,plain,(
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
    inference(flattening,[],[f29])).

fof(f49,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f85,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f86,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f51])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

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

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f83,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f84,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f82,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f89,plain,
    ( ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK3,sK2)
    | ~ v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3)) ),
    inference(cnf_transformation,[],[f51])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f88,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f51])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f45])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f93,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f60])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f97,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f75])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f92,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f61])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f43])).

fof(f57,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f47])).

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

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f98,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f73])).

cnf(c_34,negated_conjecture,
    ( r1_tarski(sK3,sK1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1763,plain,
    ( r1_tarski(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_36,negated_conjecture,
    ( v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_640,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X0
    | sK2 != X2
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_36])).

cnf(c_641,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_640])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_643,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_641,c_35])).

cnf(c_1762,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1768,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3167,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1762,c_1768])).

cnf(c_3283,plain,
    ( k1_relat_1(sK4) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_643,c_3167])).

cnf(c_16,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1770,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4100,plain,
    ( k1_relat_1(k7_relat_1(sK4,X0)) = X0
    | sK2 = k1_xboole_0
    | r1_tarski(X0,sK1) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3283,c_1770])).

cnf(c_40,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2062,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2063,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2062])).

cnf(c_4303,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | sK2 = k1_xboole_0
    | k1_relat_1(k7_relat_1(sK4,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4100,c_40,c_2063])).

cnf(c_4304,plain,
    ( k1_relat_1(k7_relat_1(sK4,X0)) = X0
    | sK2 = k1_xboole_0
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_4303])).

cnf(c_4315,plain,
    ( k1_relat_1(k7_relat_1(sK4,sK3)) = sK3
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1763,c_4304])).

cnf(c_29,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1764,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_4676,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK4,sK3)),X0) != iProver_top
    | v1_funct_1(k7_relat_1(sK4,sK3)) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4315,c_1764])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1765,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_4802,plain,
    ( k2_partfun1(sK1,sK2,sK4,X0) = k7_relat_1(sK4,X0)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1762,c_1765])).

cnf(c_37,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2136,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_2261,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(sK1,sK2,sK4,X0) = k7_relat_1(sK4,X0) ),
    inference(instantiation,[status(thm)],[c_2136])).

cnf(c_4889,plain,
    ( k2_partfun1(sK1,sK2,sK4,X0) = k7_relat_1(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4802,c_37,c_35,c_2261])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1766,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_4140,plain,
    ( v1_funct_1(k2_partfun1(sK1,sK2,sK4,X0)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1762,c_1766])).

cnf(c_38,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_2112,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(k2_partfun1(X0,X1,sK4,X2))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_2222,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_funct_1(k2_partfun1(sK1,sK2,sK4,X0))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2112])).

cnf(c_2223,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_funct_1(k2_partfun1(sK1,sK2,sK4,X0)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2222])).

cnf(c_4268,plain,
    ( v1_funct_1(k2_partfun1(sK1,sK2,sK4,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4140,c_38,c_40,c_2223])).

cnf(c_4898,plain,
    ( v1_funct_1(k7_relat_1(sK4,X0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4889,c_4268])).

cnf(c_5414,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK4,sK3)),X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,sK3)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4676,c_4898])).

cnf(c_30,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_32,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK3,sK2)
    | ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_651,plain,
    ( ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3))
    | ~ v1_relat_1(X0)
    | k2_partfun1(sK1,sK2,sK4,sK3) != X0
    | k1_relat_1(X0) != sK3
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_32])).

cnf(c_652,plain,
    ( ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ r1_tarski(k2_relat_1(k2_partfun1(sK1,sK2,sK4,sK3)),sK2)
    | ~ v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3))
    | ~ v1_relat_1(k2_partfun1(sK1,sK2,sK4,sK3))
    | k1_relat_1(k2_partfun1(sK1,sK2,sK4,sK3)) != sK3 ),
    inference(unflattening,[status(thm)],[c_651])).

cnf(c_18,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_13,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_439,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_18,c_13])).

cnf(c_443,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_439,c_17])).

cnf(c_444,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_443])).

cnf(c_664,plain,
    ( ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3))
    | k1_relat_1(k2_partfun1(sK1,sK2,sK4,sK3)) != sK3 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_652,c_17,c_444])).

cnf(c_1751,plain,
    ( k1_relat_1(k2_partfun1(sK1,sK2,sK4,sK3)) != sK3
    | m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_664])).

cnf(c_4896,plain,
    ( k1_relat_1(k7_relat_1(sK4,sK3)) != sK3
    | m1_subset_1(k7_relat_1(sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | v1_funct_1(k7_relat_1(sK4,sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4889,c_1751])).

cnf(c_4912,plain,
    ( k1_relat_1(k7_relat_1(sK4,sK3)) != sK3
    | m1_subset_1(k7_relat_1(sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4896,c_4898])).

cnf(c_5485,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4315,c_4912])).

cnf(c_5658,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k2_relat_1(k7_relat_1(sK4,sK3)),sK2) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5414,c_5485])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1767,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_5675,plain,
    ( m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4889,c_1767])).

cnf(c_6266,plain,
    ( m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5675,c_38,c_40])).

cnf(c_1769,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_6276,plain,
    ( v1_relat_1(k7_relat_1(sK4,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6266,c_1769])).

cnf(c_1760,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_444])).

cnf(c_6275,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK4,X0)),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_6266,c_1760])).

cnf(c_6557,plain,
    ( sK2 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5658,c_6276,c_6275])).

cnf(c_6278,plain,
    ( k1_relset_1(sK1,sK2,k7_relat_1(sK4,X0)) = k1_relat_1(k7_relat_1(sK4,X0)) ),
    inference(superposition,[status(thm)],[c_6266,c_1768])).

cnf(c_6559,plain,
    ( k1_relset_1(sK1,k1_xboole_0,k7_relat_1(sK4,X0)) = k1_relat_1(k7_relat_1(sK4,X0)) ),
    inference(demodulation,[status(thm)],[c_6557,c_6278])).

cnf(c_33,negated_conjecture,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_6578,plain,
    ( sK1 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6557,c_33])).

cnf(c_6579,plain,
    ( sK1 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_6578])).

cnf(c_6658,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK4,X0)) = k1_relat_1(k7_relat_1(sK4,X0)) ),
    inference(light_normalisation,[status(thm)],[c_6559,c_6579])).

cnf(c_6562,plain,
    ( m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6557,c_6266])).

cnf(c_6635,plain,
    ( m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6562,c_6579])).

cnf(c_8,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_6637,plain,
    ( m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6635,c_8])).

cnf(c_22,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_565,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3))
    | k2_partfun1(sK1,sK2,sK4,sK3) != X0
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | sK3 != k1_xboole_0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_32])).

cnf(c_566,plain,
    ( ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | ~ v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3))
    | k1_relset_1(k1_xboole_0,sK2,k2_partfun1(sK1,sK2,sK4,sK3)) != k1_xboole_0
    | sK3 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_565])).

cnf(c_1755,plain,
    ( k1_relset_1(k1_xboole_0,sK2,k2_partfun1(sK1,sK2,sK4,sK3)) != k1_xboole_0
    | sK3 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top
    | v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_566])).

cnf(c_1969,plain,
    ( k1_relset_1(k1_xboole_0,sK2,k2_partfun1(sK1,sK2,sK4,sK3)) != k1_xboole_0
    | sK3 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1755,c_8])).

cnf(c_2352,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2222])).

cnf(c_2353,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2352])).

cnf(c_2484,plain,
    ( m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | sK3 != k1_xboole_0
    | k1_relset_1(k1_xboole_0,sK2,k2_partfun1(sK1,sK2,sK4,sK3)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1969,c_38,c_40,c_2353])).

cnf(c_2485,plain,
    ( k1_relset_1(k1_xboole_0,sK2,k2_partfun1(sK1,sK2,sK4,sK3)) != k1_xboole_0
    | sK3 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2484])).

cnf(c_4893,plain,
    ( k1_relset_1(k1_xboole_0,sK2,k7_relat_1(sK4,sK3)) != k1_xboole_0
    | sK3 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | m1_subset_1(k7_relat_1(sK4,sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4889,c_2485])).

cnf(c_6564,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK4,sK3)) != k1_xboole_0
    | sK3 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) != iProver_top
    | m1_subset_1(k7_relat_1(sK4,sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6557,c_4893])).

cnf(c_7,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_6626,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK4,sK3)) != k1_xboole_0
    | sK3 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK4,sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6564,c_7])).

cnf(c_6641,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK4,sK3)) != k1_xboole_0
    | sK3 != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_6637,c_6626])).

cnf(c_6660,plain,
    ( k1_relat_1(k7_relat_1(sK4,sK3)) != k1_xboole_0
    | sK3 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6658,c_6641])).

cnf(c_6,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_3076,plain,
    ( r1_tarski(k1_xboole_0,sK3) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_3077,plain,
    ( r1_tarski(k1_xboole_0,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3076])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1777,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3256,plain,
    ( sK3 = sK1
    | r1_tarski(sK1,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1763,c_1777])).

cnf(c_7164,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6579,c_3256])).

cnf(c_8822,plain,
    ( k1_relat_1(k7_relat_1(sK4,sK3)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6660,c_3077,c_7164])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1773,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2657,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1762,c_1773])).

cnf(c_6573,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(sK1,k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6557,c_2657])).

cnf(c_6593,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6573,c_6579])).

cnf(c_6595,plain,
    ( r1_tarski(sK4,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6593,c_8])).

cnf(c_1775,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3254,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1775,c_1777])).

cnf(c_6854,plain,
    ( sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6595,c_3254])).

cnf(c_7165,plain,
    ( r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6579,c_1763])).

cnf(c_7256,plain,
    ( sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7165,c_3254])).

cnf(c_8824,plain,
    ( k1_relat_1(k7_relat_1(k1_xboole_0,k1_xboole_0)) != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_8822,c_6854,c_7256])).

cnf(c_15,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1771,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3559,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1771,c_3254])).

cnf(c_83,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_85,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_83])).

cnf(c_10,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2057,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2058,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2057])).

cnf(c_2060,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
    | r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2058])).

cnf(c_2211,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2214,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2211])).

cnf(c_2216,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2214])).

cnf(c_3624,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3559,c_85,c_2060,c_2216])).

cnf(c_6572,plain,
    ( k1_relset_1(sK1,k1_xboole_0,sK4) = k1_relat_1(sK4) ),
    inference(demodulation,[status(thm)],[c_6557,c_3167])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_584,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | sK4 != X0
    | sK2 != X1
    | sK1 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_36])).

cnf(c_585,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_584])).

cnf(c_1754,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_585])).

cnf(c_1863,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1754,c_8])).

cnf(c_6575,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6557,c_1863])).

cnf(c_6586,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6575,c_6579])).

cnf(c_6587,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_6586])).

cnf(c_6577,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6557,c_1762])).

cnf(c_6582,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6577,c_6579])).

cnf(c_6584,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6582,c_8])).

cnf(c_6590,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6587,c_6584])).

cnf(c_6597,plain,
    ( k1_relat_1(sK4) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_6572,c_6579,c_6590])).

cnf(c_8145,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6854,c_6597])).

cnf(c_8825,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8824,c_3624,c_8145])).

cnf(c_8826,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_8825])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:27:31 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.11/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.11/1.00  
% 3.11/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.11/1.00  
% 3.11/1.00  ------  iProver source info
% 3.11/1.00  
% 3.11/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.11/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.11/1.00  git: non_committed_changes: false
% 3.11/1.00  git: last_make_outside_of_git: false
% 3.11/1.00  
% 3.11/1.00  ------ 
% 3.11/1.00  
% 3.11/1.00  ------ Input Options
% 3.11/1.00  
% 3.11/1.00  --out_options                           all
% 3.11/1.00  --tptp_safe_out                         true
% 3.11/1.00  --problem_path                          ""
% 3.11/1.00  --include_path                          ""
% 3.11/1.00  --clausifier                            res/vclausify_rel
% 3.11/1.00  --clausifier_options                    --mode clausify
% 3.11/1.00  --stdin                                 false
% 3.11/1.00  --stats_out                             all
% 3.11/1.00  
% 3.11/1.00  ------ General Options
% 3.11/1.00  
% 3.11/1.00  --fof                                   false
% 3.11/1.00  --time_out_real                         305.
% 3.11/1.00  --time_out_virtual                      -1.
% 3.11/1.00  --symbol_type_check                     false
% 3.11/1.00  --clausify_out                          false
% 3.11/1.00  --sig_cnt_out                           false
% 3.11/1.00  --trig_cnt_out                          false
% 3.11/1.00  --trig_cnt_out_tolerance                1.
% 3.11/1.00  --trig_cnt_out_sk_spl                   false
% 3.11/1.00  --abstr_cl_out                          false
% 3.11/1.00  
% 3.11/1.00  ------ Global Options
% 3.11/1.00  
% 3.11/1.00  --schedule                              default
% 3.11/1.00  --add_important_lit                     false
% 3.11/1.00  --prop_solver_per_cl                    1000
% 3.11/1.00  --min_unsat_core                        false
% 3.11/1.00  --soft_assumptions                      false
% 3.11/1.00  --soft_lemma_size                       3
% 3.11/1.00  --prop_impl_unit_size                   0
% 3.11/1.00  --prop_impl_unit                        []
% 3.11/1.00  --share_sel_clauses                     true
% 3.11/1.00  --reset_solvers                         false
% 3.11/1.00  --bc_imp_inh                            [conj_cone]
% 3.11/1.00  --conj_cone_tolerance                   3.
% 3.11/1.00  --extra_neg_conj                        none
% 3.11/1.00  --large_theory_mode                     true
% 3.11/1.00  --prolific_symb_bound                   200
% 3.11/1.00  --lt_threshold                          2000
% 3.11/1.00  --clause_weak_htbl                      true
% 3.11/1.00  --gc_record_bc_elim                     false
% 3.11/1.00  
% 3.11/1.00  ------ Preprocessing Options
% 3.11/1.00  
% 3.11/1.00  --preprocessing_flag                    true
% 3.11/1.00  --time_out_prep_mult                    0.1
% 3.11/1.00  --splitting_mode                        input
% 3.11/1.00  --splitting_grd                         true
% 3.11/1.00  --splitting_cvd                         false
% 3.11/1.00  --splitting_cvd_svl                     false
% 3.11/1.00  --splitting_nvd                         32
% 3.11/1.00  --sub_typing                            true
% 3.11/1.00  --prep_gs_sim                           true
% 3.11/1.00  --prep_unflatten                        true
% 3.11/1.00  --prep_res_sim                          true
% 3.11/1.00  --prep_upred                            true
% 3.11/1.00  --prep_sem_filter                       exhaustive
% 3.11/1.00  --prep_sem_filter_out                   false
% 3.11/1.00  --pred_elim                             true
% 3.11/1.00  --res_sim_input                         true
% 3.11/1.00  --eq_ax_congr_red                       true
% 3.11/1.00  --pure_diseq_elim                       true
% 3.11/1.00  --brand_transform                       false
% 3.11/1.00  --non_eq_to_eq                          false
% 3.11/1.00  --prep_def_merge                        true
% 3.11/1.00  --prep_def_merge_prop_impl              false
% 3.11/1.00  --prep_def_merge_mbd                    true
% 3.11/1.00  --prep_def_merge_tr_red                 false
% 3.11/1.00  --prep_def_merge_tr_cl                  false
% 3.11/1.00  --smt_preprocessing                     true
% 3.11/1.00  --smt_ac_axioms                         fast
% 3.11/1.00  --preprocessed_out                      false
% 3.11/1.00  --preprocessed_stats                    false
% 3.11/1.00  
% 3.11/1.00  ------ Abstraction refinement Options
% 3.11/1.00  
% 3.11/1.00  --abstr_ref                             []
% 3.11/1.00  --abstr_ref_prep                        false
% 3.11/1.00  --abstr_ref_until_sat                   false
% 3.11/1.00  --abstr_ref_sig_restrict                funpre
% 3.11/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.11/1.00  --abstr_ref_under                       []
% 3.11/1.00  
% 3.11/1.00  ------ SAT Options
% 3.11/1.00  
% 3.11/1.00  --sat_mode                              false
% 3.11/1.00  --sat_fm_restart_options                ""
% 3.11/1.00  --sat_gr_def                            false
% 3.11/1.00  --sat_epr_types                         true
% 3.11/1.00  --sat_non_cyclic_types                  false
% 3.11/1.00  --sat_finite_models                     false
% 3.11/1.00  --sat_fm_lemmas                         false
% 3.11/1.00  --sat_fm_prep                           false
% 3.11/1.00  --sat_fm_uc_incr                        true
% 3.11/1.00  --sat_out_model                         small
% 3.11/1.00  --sat_out_clauses                       false
% 3.11/1.00  
% 3.11/1.00  ------ QBF Options
% 3.11/1.00  
% 3.11/1.00  --qbf_mode                              false
% 3.11/1.00  --qbf_elim_univ                         false
% 3.11/1.00  --qbf_dom_inst                          none
% 3.11/1.00  --qbf_dom_pre_inst                      false
% 3.11/1.00  --qbf_sk_in                             false
% 3.11/1.00  --qbf_pred_elim                         true
% 3.11/1.00  --qbf_split                             512
% 3.11/1.00  
% 3.11/1.00  ------ BMC1 Options
% 3.11/1.00  
% 3.11/1.00  --bmc1_incremental                      false
% 3.11/1.00  --bmc1_axioms                           reachable_all
% 3.11/1.00  --bmc1_min_bound                        0
% 3.11/1.00  --bmc1_max_bound                        -1
% 3.11/1.00  --bmc1_max_bound_default                -1
% 3.11/1.00  --bmc1_symbol_reachability              true
% 3.11/1.00  --bmc1_property_lemmas                  false
% 3.11/1.00  --bmc1_k_induction                      false
% 3.11/1.00  --bmc1_non_equiv_states                 false
% 3.11/1.00  --bmc1_deadlock                         false
% 3.11/1.00  --bmc1_ucm                              false
% 3.11/1.00  --bmc1_add_unsat_core                   none
% 3.11/1.00  --bmc1_unsat_core_children              false
% 3.11/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.11/1.00  --bmc1_out_stat                         full
% 3.11/1.00  --bmc1_ground_init                      false
% 3.11/1.00  --bmc1_pre_inst_next_state              false
% 3.11/1.00  --bmc1_pre_inst_state                   false
% 3.11/1.00  --bmc1_pre_inst_reach_state             false
% 3.11/1.00  --bmc1_out_unsat_core                   false
% 3.11/1.00  --bmc1_aig_witness_out                  false
% 3.11/1.00  --bmc1_verbose                          false
% 3.11/1.00  --bmc1_dump_clauses_tptp                false
% 3.11/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.11/1.00  --bmc1_dump_file                        -
% 3.11/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.11/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.11/1.00  --bmc1_ucm_extend_mode                  1
% 3.11/1.00  --bmc1_ucm_init_mode                    2
% 3.11/1.00  --bmc1_ucm_cone_mode                    none
% 3.11/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.11/1.00  --bmc1_ucm_relax_model                  4
% 3.11/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.11/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.11/1.00  --bmc1_ucm_layered_model                none
% 3.11/1.00  --bmc1_ucm_max_lemma_size               10
% 3.11/1.00  
% 3.11/1.00  ------ AIG Options
% 3.11/1.00  
% 3.11/1.00  --aig_mode                              false
% 3.11/1.00  
% 3.11/1.00  ------ Instantiation Options
% 3.11/1.00  
% 3.11/1.00  --instantiation_flag                    true
% 3.11/1.00  --inst_sos_flag                         false
% 3.11/1.00  --inst_sos_phase                        true
% 3.11/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.11/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.11/1.00  --inst_lit_sel_side                     num_symb
% 3.11/1.00  --inst_solver_per_active                1400
% 3.11/1.00  --inst_solver_calls_frac                1.
% 3.11/1.00  --inst_passive_queue_type               priority_queues
% 3.11/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.11/1.00  --inst_passive_queues_freq              [25;2]
% 3.11/1.00  --inst_dismatching                      true
% 3.11/1.00  --inst_eager_unprocessed_to_passive     true
% 3.11/1.00  --inst_prop_sim_given                   true
% 3.11/1.00  --inst_prop_sim_new                     false
% 3.11/1.00  --inst_subs_new                         false
% 3.11/1.00  --inst_eq_res_simp                      false
% 3.11/1.00  --inst_subs_given                       false
% 3.11/1.00  --inst_orphan_elimination               true
% 3.11/1.00  --inst_learning_loop_flag               true
% 3.11/1.00  --inst_learning_start                   3000
% 3.11/1.00  --inst_learning_factor                  2
% 3.11/1.00  --inst_start_prop_sim_after_learn       3
% 3.11/1.00  --inst_sel_renew                        solver
% 3.11/1.00  --inst_lit_activity_flag                true
% 3.11/1.00  --inst_restr_to_given                   false
% 3.11/1.00  --inst_activity_threshold               500
% 3.11/1.00  --inst_out_proof                        true
% 3.11/1.00  
% 3.11/1.00  ------ Resolution Options
% 3.11/1.00  
% 3.11/1.00  --resolution_flag                       true
% 3.11/1.00  --res_lit_sel                           adaptive
% 3.11/1.00  --res_lit_sel_side                      none
% 3.11/1.00  --res_ordering                          kbo
% 3.11/1.00  --res_to_prop_solver                    active
% 3.11/1.00  --res_prop_simpl_new                    false
% 3.11/1.00  --res_prop_simpl_given                  true
% 3.11/1.00  --res_passive_queue_type                priority_queues
% 3.11/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.11/1.00  --res_passive_queues_freq               [15;5]
% 3.11/1.00  --res_forward_subs                      full
% 3.11/1.00  --res_backward_subs                     full
% 3.11/1.00  --res_forward_subs_resolution           true
% 3.11/1.00  --res_backward_subs_resolution          true
% 3.11/1.00  --res_orphan_elimination                true
% 3.11/1.00  --res_time_limit                        2.
% 3.11/1.00  --res_out_proof                         true
% 3.11/1.00  
% 3.11/1.00  ------ Superposition Options
% 3.11/1.00  
% 3.11/1.00  --superposition_flag                    true
% 3.11/1.00  --sup_passive_queue_type                priority_queues
% 3.11/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.11/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.11/1.00  --demod_completeness_check              fast
% 3.11/1.00  --demod_use_ground                      true
% 3.11/1.00  --sup_to_prop_solver                    passive
% 3.11/1.00  --sup_prop_simpl_new                    true
% 3.11/1.00  --sup_prop_simpl_given                  true
% 3.11/1.00  --sup_fun_splitting                     false
% 3.11/1.00  --sup_smt_interval                      50000
% 3.11/1.00  
% 3.11/1.00  ------ Superposition Simplification Setup
% 3.11/1.00  
% 3.11/1.00  --sup_indices_passive                   []
% 3.11/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.11/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.11/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.11/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.11/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.11/1.00  --sup_full_bw                           [BwDemod]
% 3.11/1.00  --sup_immed_triv                        [TrivRules]
% 3.11/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.11/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.11/1.00  --sup_immed_bw_main                     []
% 3.11/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.11/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.11/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.11/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.11/1.00  
% 3.11/1.00  ------ Combination Options
% 3.11/1.00  
% 3.11/1.00  --comb_res_mult                         3
% 3.11/1.00  --comb_sup_mult                         2
% 3.11/1.00  --comb_inst_mult                        10
% 3.11/1.00  
% 3.11/1.00  ------ Debug Options
% 3.11/1.00  
% 3.11/1.00  --dbg_backtrace                         false
% 3.11/1.00  --dbg_dump_prop_clauses                 false
% 3.11/1.00  --dbg_dump_prop_clauses_file            -
% 3.11/1.00  --dbg_out_stat                          false
% 3.11/1.00  ------ Parsing...
% 3.11/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.11/1.00  
% 3.11/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.11/1.00  
% 3.11/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.11/1.00  
% 3.11/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.11/1.00  ------ Proving...
% 3.11/1.00  ------ Problem Properties 
% 3.11/1.00  
% 3.11/1.00  
% 3.11/1.00  clauses                                 36
% 3.11/1.00  conjectures                             4
% 3.11/1.00  EPR                                     7
% 3.11/1.00  Horn                                    30
% 3.11/1.00  unary                                   7
% 3.11/1.00  binary                                  11
% 3.11/1.00  lits                                    97
% 3.11/1.00  lits eq                                 34
% 3.11/1.00  fd_pure                                 0
% 3.11/1.00  fd_pseudo                               0
% 3.11/1.00  fd_cond                                 3
% 3.11/1.00  fd_pseudo_cond                          1
% 3.11/1.00  AC symbols                              0
% 3.11/1.00  
% 3.11/1.00  ------ Schedule dynamic 5 is on 
% 3.11/1.00  
% 3.11/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.11/1.00  
% 3.11/1.00  
% 3.11/1.00  ------ 
% 3.11/1.00  Current options:
% 3.11/1.00  ------ 
% 3.11/1.00  
% 3.11/1.00  ------ Input Options
% 3.11/1.00  
% 3.11/1.00  --out_options                           all
% 3.11/1.00  --tptp_safe_out                         true
% 3.11/1.00  --problem_path                          ""
% 3.11/1.00  --include_path                          ""
% 3.11/1.00  --clausifier                            res/vclausify_rel
% 3.11/1.00  --clausifier_options                    --mode clausify
% 3.11/1.00  --stdin                                 false
% 3.11/1.00  --stats_out                             all
% 3.11/1.00  
% 3.11/1.00  ------ General Options
% 3.11/1.00  
% 3.11/1.00  --fof                                   false
% 3.11/1.00  --time_out_real                         305.
% 3.11/1.00  --time_out_virtual                      -1.
% 3.11/1.00  --symbol_type_check                     false
% 3.11/1.00  --clausify_out                          false
% 3.11/1.00  --sig_cnt_out                           false
% 3.11/1.00  --trig_cnt_out                          false
% 3.11/1.00  --trig_cnt_out_tolerance                1.
% 3.11/1.00  --trig_cnt_out_sk_spl                   false
% 3.11/1.00  --abstr_cl_out                          false
% 3.11/1.00  
% 3.11/1.00  ------ Global Options
% 3.11/1.00  
% 3.11/1.00  --schedule                              default
% 3.11/1.00  --add_important_lit                     false
% 3.11/1.00  --prop_solver_per_cl                    1000
% 3.11/1.00  --min_unsat_core                        false
% 3.11/1.00  --soft_assumptions                      false
% 3.11/1.00  --soft_lemma_size                       3
% 3.11/1.00  --prop_impl_unit_size                   0
% 3.11/1.00  --prop_impl_unit                        []
% 3.11/1.00  --share_sel_clauses                     true
% 3.11/1.00  --reset_solvers                         false
% 3.11/1.00  --bc_imp_inh                            [conj_cone]
% 3.11/1.00  --conj_cone_tolerance                   3.
% 3.11/1.00  --extra_neg_conj                        none
% 3.11/1.00  --large_theory_mode                     true
% 3.11/1.00  --prolific_symb_bound                   200
% 3.11/1.00  --lt_threshold                          2000
% 3.11/1.00  --clause_weak_htbl                      true
% 3.11/1.00  --gc_record_bc_elim                     false
% 3.11/1.00  
% 3.11/1.00  ------ Preprocessing Options
% 3.11/1.00  
% 3.11/1.00  --preprocessing_flag                    true
% 3.11/1.00  --time_out_prep_mult                    0.1
% 3.11/1.00  --splitting_mode                        input
% 3.11/1.00  --splitting_grd                         true
% 3.11/1.00  --splitting_cvd                         false
% 3.11/1.00  --splitting_cvd_svl                     false
% 3.11/1.00  --splitting_nvd                         32
% 3.11/1.00  --sub_typing                            true
% 3.11/1.00  --prep_gs_sim                           true
% 3.11/1.00  --prep_unflatten                        true
% 3.11/1.00  --prep_res_sim                          true
% 3.11/1.00  --prep_upred                            true
% 3.11/1.00  --prep_sem_filter                       exhaustive
% 3.11/1.00  --prep_sem_filter_out                   false
% 3.11/1.00  --pred_elim                             true
% 3.11/1.00  --res_sim_input                         true
% 3.11/1.00  --eq_ax_congr_red                       true
% 3.11/1.00  --pure_diseq_elim                       true
% 3.11/1.00  --brand_transform                       false
% 3.11/1.00  --non_eq_to_eq                          false
% 3.11/1.00  --prep_def_merge                        true
% 3.11/1.00  --prep_def_merge_prop_impl              false
% 3.11/1.00  --prep_def_merge_mbd                    true
% 3.11/1.00  --prep_def_merge_tr_red                 false
% 3.11/1.00  --prep_def_merge_tr_cl                  false
% 3.11/1.00  --smt_preprocessing                     true
% 3.11/1.00  --smt_ac_axioms                         fast
% 3.11/1.00  --preprocessed_out                      false
% 3.11/1.00  --preprocessed_stats                    false
% 3.11/1.00  
% 3.11/1.00  ------ Abstraction refinement Options
% 3.11/1.00  
% 3.11/1.00  --abstr_ref                             []
% 3.11/1.00  --abstr_ref_prep                        false
% 3.11/1.00  --abstr_ref_until_sat                   false
% 3.11/1.00  --abstr_ref_sig_restrict                funpre
% 3.11/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.11/1.00  --abstr_ref_under                       []
% 3.11/1.00  
% 3.11/1.00  ------ SAT Options
% 3.11/1.00  
% 3.11/1.00  --sat_mode                              false
% 3.11/1.00  --sat_fm_restart_options                ""
% 3.11/1.00  --sat_gr_def                            false
% 3.11/1.00  --sat_epr_types                         true
% 3.11/1.00  --sat_non_cyclic_types                  false
% 3.11/1.00  --sat_finite_models                     false
% 3.11/1.00  --sat_fm_lemmas                         false
% 3.11/1.00  --sat_fm_prep                           false
% 3.11/1.00  --sat_fm_uc_incr                        true
% 3.11/1.00  --sat_out_model                         small
% 3.11/1.00  --sat_out_clauses                       false
% 3.11/1.00  
% 3.11/1.00  ------ QBF Options
% 3.11/1.00  
% 3.11/1.00  --qbf_mode                              false
% 3.11/1.00  --qbf_elim_univ                         false
% 3.11/1.00  --qbf_dom_inst                          none
% 3.11/1.00  --qbf_dom_pre_inst                      false
% 3.11/1.00  --qbf_sk_in                             false
% 3.11/1.00  --qbf_pred_elim                         true
% 3.11/1.00  --qbf_split                             512
% 3.11/1.00  
% 3.11/1.00  ------ BMC1 Options
% 3.11/1.00  
% 3.11/1.00  --bmc1_incremental                      false
% 3.11/1.00  --bmc1_axioms                           reachable_all
% 3.11/1.00  --bmc1_min_bound                        0
% 3.11/1.00  --bmc1_max_bound                        -1
% 3.11/1.00  --bmc1_max_bound_default                -1
% 3.11/1.00  --bmc1_symbol_reachability              true
% 3.11/1.00  --bmc1_property_lemmas                  false
% 3.11/1.00  --bmc1_k_induction                      false
% 3.11/1.00  --bmc1_non_equiv_states                 false
% 3.11/1.00  --bmc1_deadlock                         false
% 3.11/1.00  --bmc1_ucm                              false
% 3.11/1.00  --bmc1_add_unsat_core                   none
% 3.11/1.00  --bmc1_unsat_core_children              false
% 3.11/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.11/1.00  --bmc1_out_stat                         full
% 3.11/1.00  --bmc1_ground_init                      false
% 3.11/1.00  --bmc1_pre_inst_next_state              false
% 3.11/1.00  --bmc1_pre_inst_state                   false
% 3.11/1.00  --bmc1_pre_inst_reach_state             false
% 3.11/1.00  --bmc1_out_unsat_core                   false
% 3.11/1.00  --bmc1_aig_witness_out                  false
% 3.11/1.00  --bmc1_verbose                          false
% 3.11/1.00  --bmc1_dump_clauses_tptp                false
% 3.11/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.11/1.00  --bmc1_dump_file                        -
% 3.11/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.11/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.11/1.00  --bmc1_ucm_extend_mode                  1
% 3.11/1.00  --bmc1_ucm_init_mode                    2
% 3.11/1.00  --bmc1_ucm_cone_mode                    none
% 3.11/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.11/1.00  --bmc1_ucm_relax_model                  4
% 3.11/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.11/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.11/1.00  --bmc1_ucm_layered_model                none
% 3.11/1.00  --bmc1_ucm_max_lemma_size               10
% 3.11/1.00  
% 3.11/1.00  ------ AIG Options
% 3.11/1.00  
% 3.11/1.00  --aig_mode                              false
% 3.11/1.00  
% 3.11/1.00  ------ Instantiation Options
% 3.11/1.00  
% 3.11/1.00  --instantiation_flag                    true
% 3.11/1.00  --inst_sos_flag                         false
% 3.11/1.00  --inst_sos_phase                        true
% 3.11/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.11/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.11/1.00  --inst_lit_sel_side                     none
% 3.11/1.00  --inst_solver_per_active                1400
% 3.11/1.00  --inst_solver_calls_frac                1.
% 3.11/1.00  --inst_passive_queue_type               priority_queues
% 3.11/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.11/1.00  --inst_passive_queues_freq              [25;2]
% 3.11/1.00  --inst_dismatching                      true
% 3.11/1.00  --inst_eager_unprocessed_to_passive     true
% 3.11/1.00  --inst_prop_sim_given                   true
% 3.11/1.00  --inst_prop_sim_new                     false
% 3.11/1.00  --inst_subs_new                         false
% 3.11/1.00  --inst_eq_res_simp                      false
% 3.11/1.00  --inst_subs_given                       false
% 3.11/1.00  --inst_orphan_elimination               true
% 3.11/1.00  --inst_learning_loop_flag               true
% 3.11/1.00  --inst_learning_start                   3000
% 3.11/1.00  --inst_learning_factor                  2
% 3.11/1.00  --inst_start_prop_sim_after_learn       3
% 3.11/1.00  --inst_sel_renew                        solver
% 3.11/1.00  --inst_lit_activity_flag                true
% 3.11/1.00  --inst_restr_to_given                   false
% 3.11/1.00  --inst_activity_threshold               500
% 3.11/1.00  --inst_out_proof                        true
% 3.11/1.00  
% 3.11/1.00  ------ Resolution Options
% 3.11/1.00  
% 3.11/1.00  --resolution_flag                       false
% 3.11/1.00  --res_lit_sel                           adaptive
% 3.11/1.00  --res_lit_sel_side                      none
% 3.11/1.00  --res_ordering                          kbo
% 3.11/1.00  --res_to_prop_solver                    active
% 3.11/1.00  --res_prop_simpl_new                    false
% 3.11/1.00  --res_prop_simpl_given                  true
% 3.11/1.00  --res_passive_queue_type                priority_queues
% 3.11/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.11/1.00  --res_passive_queues_freq               [15;5]
% 3.11/1.00  --res_forward_subs                      full
% 3.11/1.00  --res_backward_subs                     full
% 3.11/1.00  --res_forward_subs_resolution           true
% 3.11/1.00  --res_backward_subs_resolution          true
% 3.11/1.00  --res_orphan_elimination                true
% 3.11/1.00  --res_time_limit                        2.
% 3.11/1.00  --res_out_proof                         true
% 3.11/1.00  
% 3.11/1.00  ------ Superposition Options
% 3.11/1.00  
% 3.11/1.00  --superposition_flag                    true
% 3.11/1.00  --sup_passive_queue_type                priority_queues
% 3.11/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.11/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.11/1.00  --demod_completeness_check              fast
% 3.11/1.00  --demod_use_ground                      true
% 3.11/1.00  --sup_to_prop_solver                    passive
% 3.11/1.00  --sup_prop_simpl_new                    true
% 3.11/1.00  --sup_prop_simpl_given                  true
% 3.11/1.00  --sup_fun_splitting                     false
% 3.11/1.00  --sup_smt_interval                      50000
% 3.11/1.00  
% 3.11/1.00  ------ Superposition Simplification Setup
% 3.11/1.00  
% 3.11/1.00  --sup_indices_passive                   []
% 3.11/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.11/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.11/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.11/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.11/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.11/1.00  --sup_full_bw                           [BwDemod]
% 3.11/1.00  --sup_immed_triv                        [TrivRules]
% 3.11/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.11/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.11/1.00  --sup_immed_bw_main                     []
% 3.11/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.11/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.11/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.11/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.11/1.00  
% 3.11/1.00  ------ Combination Options
% 3.11/1.00  
% 3.11/1.00  --comb_res_mult                         3
% 3.11/1.00  --comb_sup_mult                         2
% 3.11/1.00  --comb_inst_mult                        10
% 3.11/1.00  
% 3.11/1.00  ------ Debug Options
% 3.11/1.00  
% 3.11/1.00  --dbg_backtrace                         false
% 3.11/1.00  --dbg_dump_prop_clauses                 false
% 3.11/1.00  --dbg_dump_prop_clauses_file            -
% 3.11/1.00  --dbg_out_stat                          false
% 3.11/1.00  
% 3.11/1.00  
% 3.11/1.00  
% 3.11/1.00  
% 3.11/1.00  ------ Proving...
% 3.11/1.00  
% 3.11/1.00  
% 3.11/1.00  % SZS status Theorem for theBenchmark.p
% 3.11/1.00  
% 3.11/1.00   Resolution empty clause
% 3.11/1.00  
% 3.11/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.11/1.00  
% 3.11/1.00  fof(f17,conjecture,(
% 3.11/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.11/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/1.00  
% 3.11/1.00  fof(f18,negated_conjecture,(
% 3.11/1.00    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.11/1.00    inference(negated_conjecture,[],[f17])).
% 3.11/1.00  
% 3.11/1.00  fof(f37,plain,(
% 3.11/1.00    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.11/1.00    inference(ennf_transformation,[],[f18])).
% 3.11/1.00  
% 3.11/1.00  fof(f38,plain,(
% 3.11/1.00    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.11/1.00    inference(flattening,[],[f37])).
% 3.11/1.00  
% 3.11/1.00  fof(f50,plain,(
% 3.11/1.00    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) | ~v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK3,sK2) | ~v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3))) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & r1_tarski(sK3,sK1) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4))),
% 3.11/1.00    introduced(choice_axiom,[])).
% 3.11/1.00  
% 3.11/1.00  fof(f51,plain,(
% 3.11/1.00    (~m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) | ~v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK3,sK2) | ~v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3))) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & r1_tarski(sK3,sK1) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)),
% 3.11/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f38,f50])).
% 3.11/1.00  
% 3.11/1.00  fof(f87,plain,(
% 3.11/1.00    r1_tarski(sK3,sK1)),
% 3.11/1.00    inference(cnf_transformation,[],[f51])).
% 3.11/1.00  
% 3.11/1.00  fof(f13,axiom,(
% 3.11/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.11/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/1.00  
% 3.11/1.00  fof(f29,plain,(
% 3.11/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.11/1.00    inference(ennf_transformation,[],[f13])).
% 3.11/1.00  
% 3.11/1.00  fof(f30,plain,(
% 3.11/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.11/1.00    inference(flattening,[],[f29])).
% 3.11/1.00  
% 3.11/1.00  fof(f49,plain,(
% 3.11/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.11/1.00    inference(nnf_transformation,[],[f30])).
% 3.11/1.00  
% 3.11/1.00  fof(f72,plain,(
% 3.11/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.11/1.00    inference(cnf_transformation,[],[f49])).
% 3.11/1.00  
% 3.11/1.00  fof(f85,plain,(
% 3.11/1.00    v1_funct_2(sK4,sK1,sK2)),
% 3.11/1.00    inference(cnf_transformation,[],[f51])).
% 3.11/1.00  
% 3.11/1.00  fof(f86,plain,(
% 3.11/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 3.11/1.00    inference(cnf_transformation,[],[f51])).
% 3.11/1.00  
% 3.11/1.00  fof(f12,axiom,(
% 3.11/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.11/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/1.00  
% 3.11/1.00  fof(f28,plain,(
% 3.11/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.11/1.00    inference(ennf_transformation,[],[f12])).
% 3.11/1.00  
% 3.11/1.00  fof(f71,plain,(
% 3.11/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.11/1.00    inference(cnf_transformation,[],[f28])).
% 3.11/1.00  
% 3.11/1.00  fof(f9,axiom,(
% 3.11/1.00    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 3.11/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/1.00  
% 3.11/1.00  fof(f24,plain,(
% 3.11/1.00    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 3.11/1.00    inference(ennf_transformation,[],[f9])).
% 3.11/1.00  
% 3.11/1.00  fof(f25,plain,(
% 3.11/1.00    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.11/1.00    inference(flattening,[],[f24])).
% 3.11/1.00  
% 3.11/1.00  fof(f68,plain,(
% 3.11/1.00    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.11/1.00    inference(cnf_transformation,[],[f25])).
% 3.11/1.00  
% 3.11/1.00  fof(f10,axiom,(
% 3.11/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.11/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/1.00  
% 3.11/1.00  fof(f26,plain,(
% 3.11/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.11/1.00    inference(ennf_transformation,[],[f10])).
% 3.11/1.00  
% 3.11/1.00  fof(f69,plain,(
% 3.11/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.11/1.00    inference(cnf_transformation,[],[f26])).
% 3.11/1.00  
% 3.11/1.00  fof(f16,axiom,(
% 3.11/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 3.11/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/1.00  
% 3.11/1.00  fof(f35,plain,(
% 3.11/1.00    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.11/1.00    inference(ennf_transformation,[],[f16])).
% 3.11/1.00  
% 3.11/1.00  fof(f36,plain,(
% 3.11/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.11/1.00    inference(flattening,[],[f35])).
% 3.11/1.00  
% 3.11/1.00  fof(f83,plain,(
% 3.11/1.00    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.11/1.00    inference(cnf_transformation,[],[f36])).
% 3.11/1.00  
% 3.11/1.00  fof(f15,axiom,(
% 3.11/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 3.11/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/1.00  
% 3.11/1.00  fof(f33,plain,(
% 3.11/1.00    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.11/1.00    inference(ennf_transformation,[],[f15])).
% 3.11/1.00  
% 3.11/1.00  fof(f34,plain,(
% 3.11/1.00    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.11/1.00    inference(flattening,[],[f33])).
% 3.11/1.00  
% 3.11/1.00  fof(f80,plain,(
% 3.11/1.00    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.11/1.00    inference(cnf_transformation,[],[f34])).
% 3.11/1.00  
% 3.11/1.00  fof(f84,plain,(
% 3.11/1.00    v1_funct_1(sK4)),
% 3.11/1.00    inference(cnf_transformation,[],[f51])).
% 3.11/1.00  
% 3.11/1.00  fof(f14,axiom,(
% 3.11/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 3.11/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/1.00  
% 3.11/1.00  fof(f31,plain,(
% 3.11/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.11/1.00    inference(ennf_transformation,[],[f14])).
% 3.11/1.00  
% 3.11/1.00  fof(f32,plain,(
% 3.11/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.11/1.00    inference(flattening,[],[f31])).
% 3.11/1.00  
% 3.11/1.00  fof(f78,plain,(
% 3.11/1.00    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.11/1.00    inference(cnf_transformation,[],[f32])).
% 3.11/1.00  
% 3.11/1.00  fof(f82,plain,(
% 3.11/1.00    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.11/1.00    inference(cnf_transformation,[],[f36])).
% 3.11/1.00  
% 3.11/1.00  fof(f89,plain,(
% 3.11/1.00    ~m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) | ~v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK3,sK2) | ~v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3))),
% 3.11/1.00    inference(cnf_transformation,[],[f51])).
% 3.11/1.00  
% 3.11/1.00  fof(f11,axiom,(
% 3.11/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.11/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/1.00  
% 3.11/1.00  fof(f19,plain,(
% 3.11/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.11/1.00    inference(pure_predicate_removal,[],[f11])).
% 3.11/1.00  
% 3.11/1.00  fof(f27,plain,(
% 3.11/1.00    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.11/1.00    inference(ennf_transformation,[],[f19])).
% 3.11/1.00  
% 3.11/1.00  fof(f70,plain,(
% 3.11/1.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.11/1.01    inference(cnf_transformation,[],[f27])).
% 3.11/1.01  
% 3.11/1.01  fof(f6,axiom,(
% 3.11/1.01    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.11/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/1.01  
% 3.11/1.01  fof(f21,plain,(
% 3.11/1.01    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.11/1.01    inference(ennf_transformation,[],[f6])).
% 3.11/1.01  
% 3.11/1.01  fof(f48,plain,(
% 3.11/1.01    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.11/1.01    inference(nnf_transformation,[],[f21])).
% 3.11/1.01  
% 3.11/1.01  fof(f64,plain,(
% 3.11/1.01    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.11/1.01    inference(cnf_transformation,[],[f48])).
% 3.11/1.01  
% 3.11/1.01  fof(f79,plain,(
% 3.11/1.01    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.11/1.01    inference(cnf_transformation,[],[f32])).
% 3.11/1.01  
% 3.11/1.01  fof(f88,plain,(
% 3.11/1.01    k1_xboole_0 = sK1 | k1_xboole_0 != sK2),
% 3.11/1.01    inference(cnf_transformation,[],[f51])).
% 3.11/1.01  
% 3.11/1.01  fof(f4,axiom,(
% 3.11/1.01    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.11/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/1.01  
% 3.11/1.01  fof(f45,plain,(
% 3.11/1.01    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.11/1.01    inference(nnf_transformation,[],[f4])).
% 3.11/1.01  
% 3.11/1.01  fof(f46,plain,(
% 3.11/1.01    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.11/1.01    inference(flattening,[],[f45])).
% 3.11/1.01  
% 3.11/1.01  fof(f60,plain,(
% 3.11/1.01    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.11/1.01    inference(cnf_transformation,[],[f46])).
% 3.11/1.01  
% 3.11/1.01  fof(f93,plain,(
% 3.11/1.01    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.11/1.01    inference(equality_resolution,[],[f60])).
% 3.11/1.01  
% 3.11/1.01  fof(f75,plain,(
% 3.11/1.01    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.11/1.01    inference(cnf_transformation,[],[f49])).
% 3.11/1.01  
% 3.11/1.01  fof(f97,plain,(
% 3.11/1.01    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.11/1.01    inference(equality_resolution,[],[f75])).
% 3.11/1.01  
% 3.11/1.01  fof(f61,plain,(
% 3.11/1.01    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.11/1.01    inference(cnf_transformation,[],[f46])).
% 3.11/1.01  
% 3.11/1.01  fof(f92,plain,(
% 3.11/1.01    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.11/1.01    inference(equality_resolution,[],[f61])).
% 3.11/1.01  
% 3.11/1.01  fof(f3,axiom,(
% 3.11/1.01    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.11/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/1.01  
% 3.11/1.01  fof(f58,plain,(
% 3.11/1.01    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.11/1.01    inference(cnf_transformation,[],[f3])).
% 3.11/1.01  
% 3.11/1.01  fof(f2,axiom,(
% 3.11/1.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.11/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/1.01  
% 3.11/1.01  fof(f43,plain,(
% 3.11/1.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.11/1.01    inference(nnf_transformation,[],[f2])).
% 3.11/1.01  
% 3.11/1.01  fof(f44,plain,(
% 3.11/1.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.11/1.01    inference(flattening,[],[f43])).
% 3.11/1.01  
% 3.11/1.01  fof(f57,plain,(
% 3.11/1.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.11/1.01    inference(cnf_transformation,[],[f44])).
% 3.11/1.01  
% 3.11/1.01  fof(f5,axiom,(
% 3.11/1.01    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.11/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/1.01  
% 3.11/1.01  fof(f47,plain,(
% 3.11/1.01    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.11/1.01    inference(nnf_transformation,[],[f5])).
% 3.11/1.01  
% 3.11/1.01  fof(f62,plain,(
% 3.11/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.11/1.01    inference(cnf_transformation,[],[f47])).
% 3.11/1.01  
% 3.11/1.01  fof(f8,axiom,(
% 3.11/1.01    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 3.11/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.11/1.01  
% 3.11/1.01  fof(f23,plain,(
% 3.11/1.01    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 3.11/1.01    inference(ennf_transformation,[],[f8])).
% 3.11/1.01  
% 3.11/1.01  fof(f67,plain,(
% 3.11/1.01    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 3.11/1.01    inference(cnf_transformation,[],[f23])).
% 3.11/1.01  
% 3.11/1.01  fof(f63,plain,(
% 3.11/1.01    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.11/1.01    inference(cnf_transformation,[],[f47])).
% 3.11/1.01  
% 3.11/1.01  fof(f73,plain,(
% 3.11/1.01    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.11/1.01    inference(cnf_transformation,[],[f49])).
% 3.11/1.01  
% 3.11/1.01  fof(f98,plain,(
% 3.11/1.01    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.11/1.01    inference(equality_resolution,[],[f73])).
% 3.11/1.01  
% 3.11/1.01  cnf(c_34,negated_conjecture,
% 3.11/1.01      ( r1_tarski(sK3,sK1) ),
% 3.11/1.01      inference(cnf_transformation,[],[f87]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_1763,plain,
% 3.11/1.01      ( r1_tarski(sK3,sK1) = iProver_top ),
% 3.11/1.01      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_25,plain,
% 3.11/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 3.11/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.11/1.01      | k1_relset_1(X1,X2,X0) = X1
% 3.11/1.01      | k1_xboole_0 = X2 ),
% 3.11/1.01      inference(cnf_transformation,[],[f72]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_36,negated_conjecture,
% 3.11/1.01      ( v1_funct_2(sK4,sK1,sK2) ),
% 3.11/1.01      inference(cnf_transformation,[],[f85]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_640,plain,
% 3.11/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.11/1.01      | k1_relset_1(X1,X2,X0) = X1
% 3.11/1.01      | sK4 != X0
% 3.11/1.01      | sK2 != X2
% 3.11/1.01      | sK1 != X1
% 3.11/1.01      | k1_xboole_0 = X2 ),
% 3.11/1.01      inference(resolution_lifted,[status(thm)],[c_25,c_36]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_641,plain,
% 3.11/1.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.11/1.01      | k1_relset_1(sK1,sK2,sK4) = sK1
% 3.11/1.01      | k1_xboole_0 = sK2 ),
% 3.11/1.01      inference(unflattening,[status(thm)],[c_640]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_35,negated_conjecture,
% 3.11/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 3.11/1.01      inference(cnf_transformation,[],[f86]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_643,plain,
% 3.11/1.01      ( k1_relset_1(sK1,sK2,sK4) = sK1 | k1_xboole_0 = sK2 ),
% 3.11/1.01      inference(global_propositional_subsumption,[status(thm)],[c_641,c_35]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_1762,plain,
% 3.11/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.11/1.01      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_19,plain,
% 3.11/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.11/1.01      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.11/1.01      inference(cnf_transformation,[],[f71]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_1768,plain,
% 3.11/1.01      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.11/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.11/1.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_3167,plain,
% 3.11/1.01      ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
% 3.11/1.01      inference(superposition,[status(thm)],[c_1762,c_1768]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_3283,plain,
% 3.11/1.01      ( k1_relat_1(sK4) = sK1 | sK2 = k1_xboole_0 ),
% 3.11/1.01      inference(superposition,[status(thm)],[c_643,c_3167]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_16,plain,
% 3.11/1.01      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 3.11/1.01      | ~ v1_relat_1(X1)
% 3.11/1.01      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 3.11/1.01      inference(cnf_transformation,[],[f68]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_1770,plain,
% 3.11/1.01      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 3.11/1.01      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 3.11/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.11/1.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_4100,plain,
% 3.11/1.01      ( k1_relat_1(k7_relat_1(sK4,X0)) = X0
% 3.11/1.01      | sK2 = k1_xboole_0
% 3.11/1.01      | r1_tarski(X0,sK1) != iProver_top
% 3.11/1.01      | v1_relat_1(sK4) != iProver_top ),
% 3.11/1.01      inference(superposition,[status(thm)],[c_3283,c_1770]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_40,plain,
% 3.11/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.11/1.01      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_17,plain,
% 3.11/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 3.11/1.01      inference(cnf_transformation,[],[f69]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_2062,plain,
% 3.11/1.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.11/1.01      | v1_relat_1(sK4) ),
% 3.11/1.01      inference(instantiation,[status(thm)],[c_17]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_2063,plain,
% 3.11/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.11/1.01      | v1_relat_1(sK4) = iProver_top ),
% 3.11/1.01      inference(predicate_to_equality,[status(thm)],[c_2062]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_4303,plain,
% 3.11/1.01      ( r1_tarski(X0,sK1) != iProver_top
% 3.11/1.01      | sK2 = k1_xboole_0
% 3.11/1.01      | k1_relat_1(k7_relat_1(sK4,X0)) = X0 ),
% 3.11/1.01      inference(global_propositional_subsumption,
% 3.11/1.01                [status(thm)],
% 3.11/1.01                [c_4100,c_40,c_2063]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_4304,plain,
% 3.11/1.01      ( k1_relat_1(k7_relat_1(sK4,X0)) = X0
% 3.11/1.01      | sK2 = k1_xboole_0
% 3.11/1.01      | r1_tarski(X0,sK1) != iProver_top ),
% 3.11/1.01      inference(renaming,[status(thm)],[c_4303]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_4315,plain,
% 3.11/1.01      ( k1_relat_1(k7_relat_1(sK4,sK3)) = sK3 | sK2 = k1_xboole_0 ),
% 3.11/1.01      inference(superposition,[status(thm)],[c_1763,c_4304]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_29,plain,
% 3.11/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.11/1.01      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.11/1.01      | ~ v1_funct_1(X0)
% 3.11/1.01      | ~ v1_relat_1(X0) ),
% 3.11/1.01      inference(cnf_transformation,[],[f83]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_1764,plain,
% 3.11/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
% 3.11/1.01      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 3.11/1.01      | v1_funct_1(X0) != iProver_top
% 3.11/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.11/1.01      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_4676,plain,
% 3.11/1.01      ( sK2 = k1_xboole_0
% 3.11/1.01      | m1_subset_1(k7_relat_1(sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
% 3.11/1.01      | r1_tarski(k2_relat_1(k7_relat_1(sK4,sK3)),X0) != iProver_top
% 3.11/1.01      | v1_funct_1(k7_relat_1(sK4,sK3)) != iProver_top
% 3.11/1.01      | v1_relat_1(k7_relat_1(sK4,sK3)) != iProver_top ),
% 3.11/1.01      inference(superposition,[status(thm)],[c_4315,c_1764]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_28,plain,
% 3.11/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.11/1.01      | ~ v1_funct_1(X0)
% 3.11/1.01      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 3.11/1.01      inference(cnf_transformation,[],[f80]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_1765,plain,
% 3.11/1.01      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 3.11/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.11/1.01      | v1_funct_1(X2) != iProver_top ),
% 3.11/1.01      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_4802,plain,
% 3.11/1.01      ( k2_partfun1(sK1,sK2,sK4,X0) = k7_relat_1(sK4,X0)
% 3.11/1.01      | v1_funct_1(sK4) != iProver_top ),
% 3.11/1.01      inference(superposition,[status(thm)],[c_1762,c_1765]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_37,negated_conjecture,
% 3.11/1.01      ( v1_funct_1(sK4) ),
% 3.11/1.01      inference(cnf_transformation,[],[f84]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_2136,plain,
% 3.11/1.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.11/1.01      | ~ v1_funct_1(sK4)
% 3.11/1.01      | k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2) ),
% 3.11/1.01      inference(instantiation,[status(thm)],[c_28]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_2261,plain,
% 3.11/1.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.11/1.01      | ~ v1_funct_1(sK4)
% 3.11/1.01      | k2_partfun1(sK1,sK2,sK4,X0) = k7_relat_1(sK4,X0) ),
% 3.11/1.01      inference(instantiation,[status(thm)],[c_2136]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_4889,plain,
% 3.11/1.01      ( k2_partfun1(sK1,sK2,sK4,X0) = k7_relat_1(sK4,X0) ),
% 3.11/1.01      inference(global_propositional_subsumption,
% 3.11/1.01                [status(thm)],
% 3.11/1.01                [c_4802,c_37,c_35,c_2261]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_27,plain,
% 3.11/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.11/1.01      | ~ v1_funct_1(X0)
% 3.11/1.01      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
% 3.11/1.01      inference(cnf_transformation,[],[f78]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_1766,plain,
% 3.11/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.11/1.01      | v1_funct_1(X0) != iProver_top
% 3.11/1.01      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
% 3.11/1.01      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_4140,plain,
% 3.11/1.01      ( v1_funct_1(k2_partfun1(sK1,sK2,sK4,X0)) = iProver_top
% 3.11/1.01      | v1_funct_1(sK4) != iProver_top ),
% 3.11/1.01      inference(superposition,[status(thm)],[c_1762,c_1766]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_38,plain,
% 3.11/1.01      ( v1_funct_1(sK4) = iProver_top ),
% 3.11/1.01      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_2112,plain,
% 3.11/1.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.11/1.01      | v1_funct_1(k2_partfun1(X0,X1,sK4,X2))
% 3.11/1.01      | ~ v1_funct_1(sK4) ),
% 3.11/1.01      inference(instantiation,[status(thm)],[c_27]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_2222,plain,
% 3.11/1.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.11/1.01      | v1_funct_1(k2_partfun1(sK1,sK2,sK4,X0))
% 3.11/1.01      | ~ v1_funct_1(sK4) ),
% 3.11/1.01      inference(instantiation,[status(thm)],[c_2112]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_2223,plain,
% 3.11/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.11/1.01      | v1_funct_1(k2_partfun1(sK1,sK2,sK4,X0)) = iProver_top
% 3.11/1.01      | v1_funct_1(sK4) != iProver_top ),
% 3.11/1.01      inference(predicate_to_equality,[status(thm)],[c_2222]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_4268,plain,
% 3.11/1.01      ( v1_funct_1(k2_partfun1(sK1,sK2,sK4,X0)) = iProver_top ),
% 3.11/1.01      inference(global_propositional_subsumption,
% 3.11/1.01                [status(thm)],
% 3.11/1.01                [c_4140,c_38,c_40,c_2223]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_4898,plain,
% 3.11/1.01      ( v1_funct_1(k7_relat_1(sK4,X0)) = iProver_top ),
% 3.11/1.01      inference(demodulation,[status(thm)],[c_4889,c_4268]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_5414,plain,
% 3.11/1.01      ( sK2 = k1_xboole_0
% 3.11/1.01      | m1_subset_1(k7_relat_1(sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) = iProver_top
% 3.11/1.01      | r1_tarski(k2_relat_1(k7_relat_1(sK4,sK3)),X0) != iProver_top
% 3.11/1.01      | v1_relat_1(k7_relat_1(sK4,sK3)) != iProver_top ),
% 3.11/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_4676,c_4898]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_30,plain,
% 3.11/1.01      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 3.11/1.01      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.11/1.01      | ~ v1_funct_1(X0)
% 3.11/1.01      | ~ v1_relat_1(X0) ),
% 3.11/1.01      inference(cnf_transformation,[],[f82]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_32,negated_conjecture,
% 3.11/1.01      ( ~ v1_funct_2(k2_partfun1(sK1,sK2,sK4,sK3),sK3,sK2)
% 3.11/1.01      | ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 3.11/1.01      | ~ v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3)) ),
% 3.11/1.01      inference(cnf_transformation,[],[f89]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_651,plain,
% 3.11/1.01      ( ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 3.11/1.01      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.11/1.01      | ~ v1_funct_1(X0)
% 3.11/1.01      | ~ v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3))
% 3.11/1.01      | ~ v1_relat_1(X0)
% 3.11/1.01      | k2_partfun1(sK1,sK2,sK4,sK3) != X0
% 3.11/1.01      | k1_relat_1(X0) != sK3
% 3.11/1.01      | sK2 != X1 ),
% 3.11/1.01      inference(resolution_lifted,[status(thm)],[c_30,c_32]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_652,plain,
% 3.11/1.01      ( ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 3.11/1.01      | ~ r1_tarski(k2_relat_1(k2_partfun1(sK1,sK2,sK4,sK3)),sK2)
% 3.11/1.01      | ~ v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3))
% 3.11/1.01      | ~ v1_relat_1(k2_partfun1(sK1,sK2,sK4,sK3))
% 3.11/1.01      | k1_relat_1(k2_partfun1(sK1,sK2,sK4,sK3)) != sK3 ),
% 3.11/1.01      inference(unflattening,[status(thm)],[c_651]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_18,plain,
% 3.11/1.01      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.11/1.01      inference(cnf_transformation,[],[f70]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_13,plain,
% 3.11/1.01      ( ~ v5_relat_1(X0,X1) | r1_tarski(k2_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 3.11/1.01      inference(cnf_transformation,[],[f64]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_439,plain,
% 3.11/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.11/1.01      | r1_tarski(k2_relat_1(X0),X2)
% 3.11/1.01      | ~ v1_relat_1(X0) ),
% 3.11/1.01      inference(resolution,[status(thm)],[c_18,c_13]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_443,plain,
% 3.11/1.01      ( r1_tarski(k2_relat_1(X0),X2)
% 3.11/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.11/1.01      inference(global_propositional_subsumption,[status(thm)],[c_439,c_17]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_444,plain,
% 3.11/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.11/1.01      | r1_tarski(k2_relat_1(X0),X2) ),
% 3.11/1.01      inference(renaming,[status(thm)],[c_443]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_664,plain,
% 3.11/1.01      ( ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 3.11/1.01      | ~ v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3))
% 3.11/1.01      | k1_relat_1(k2_partfun1(sK1,sK2,sK4,sK3)) != sK3 ),
% 3.11/1.01      inference(forward_subsumption_resolution,
% 3.11/1.01                [status(thm)],
% 3.11/1.01                [c_652,c_17,c_444]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_1751,plain,
% 3.11/1.01      ( k1_relat_1(k2_partfun1(sK1,sK2,sK4,sK3)) != sK3
% 3.11/1.01      | m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 3.11/1.01      | v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3)) != iProver_top ),
% 3.11/1.01      inference(predicate_to_equality,[status(thm)],[c_664]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_4896,plain,
% 3.11/1.01      ( k1_relat_1(k7_relat_1(sK4,sK3)) != sK3
% 3.11/1.01      | m1_subset_1(k7_relat_1(sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 3.11/1.01      | v1_funct_1(k7_relat_1(sK4,sK3)) != iProver_top ),
% 3.11/1.01      inference(demodulation,[status(thm)],[c_4889,c_1751]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_4912,plain,
% 3.11/1.01      ( k1_relat_1(k7_relat_1(sK4,sK3)) != sK3
% 3.11/1.01      | m1_subset_1(k7_relat_1(sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
% 3.11/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_4896,c_4898]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_5485,plain,
% 3.11/1.01      ( sK2 = k1_xboole_0
% 3.11/1.01      | m1_subset_1(k7_relat_1(sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
% 3.11/1.01      inference(superposition,[status(thm)],[c_4315,c_4912]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_5658,plain,
% 3.11/1.01      ( sK2 = k1_xboole_0
% 3.11/1.01      | r1_tarski(k2_relat_1(k7_relat_1(sK4,sK3)),sK2) != iProver_top
% 3.11/1.01      | v1_relat_1(k7_relat_1(sK4,sK3)) != iProver_top ),
% 3.11/1.01      inference(superposition,[status(thm)],[c_5414,c_5485]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_26,plain,
% 3.11/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.11/1.01      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.11/1.01      | ~ v1_funct_1(X0) ),
% 3.11/1.01      inference(cnf_transformation,[],[f79]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_1767,plain,
% 3.11/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.11/1.01      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 3.11/1.01      | v1_funct_1(X0) != iProver_top ),
% 3.11/1.01      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_5675,plain,
% 3.11/1.01      ( m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top
% 3.11/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.11/1.01      | v1_funct_1(sK4) != iProver_top ),
% 3.11/1.01      inference(superposition,[status(thm)],[c_4889,c_1767]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_6266,plain,
% 3.11/1.01      ( m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.11/1.01      inference(global_propositional_subsumption,
% 3.11/1.01                [status(thm)],
% 3.11/1.01                [c_5675,c_38,c_40]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_1769,plain,
% 3.11/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.11/1.01      | v1_relat_1(X0) = iProver_top ),
% 3.11/1.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_6276,plain,
% 3.11/1.01      ( v1_relat_1(k7_relat_1(sK4,X0)) = iProver_top ),
% 3.11/1.01      inference(superposition,[status(thm)],[c_6266,c_1769]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_1760,plain,
% 3.11/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.11/1.01      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 3.11/1.01      inference(predicate_to_equality,[status(thm)],[c_444]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_6275,plain,
% 3.11/1.01      ( r1_tarski(k2_relat_1(k7_relat_1(sK4,X0)),sK2) = iProver_top ),
% 3.11/1.01      inference(superposition,[status(thm)],[c_6266,c_1760]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_6557,plain,
% 3.11/1.01      ( sK2 = k1_xboole_0 ),
% 3.11/1.01      inference(forward_subsumption_resolution,
% 3.11/1.01                [status(thm)],
% 3.11/1.01                [c_5658,c_6276,c_6275]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_6278,plain,
% 3.11/1.01      ( k1_relset_1(sK1,sK2,k7_relat_1(sK4,X0)) = k1_relat_1(k7_relat_1(sK4,X0)) ),
% 3.11/1.01      inference(superposition,[status(thm)],[c_6266,c_1768]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_6559,plain,
% 3.11/1.01      ( k1_relset_1(sK1,k1_xboole_0,k7_relat_1(sK4,X0)) = k1_relat_1(k7_relat_1(sK4,X0)) ),
% 3.11/1.01      inference(demodulation,[status(thm)],[c_6557,c_6278]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_33,negated_conjecture,
% 3.11/1.01      ( k1_xboole_0 != sK2 | k1_xboole_0 = sK1 ),
% 3.11/1.01      inference(cnf_transformation,[],[f88]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_6578,plain,
% 3.11/1.01      ( sK1 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.11/1.01      inference(demodulation,[status(thm)],[c_6557,c_33]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_6579,plain,
% 3.11/1.01      ( sK1 = k1_xboole_0 ),
% 3.11/1.01      inference(equality_resolution_simp,[status(thm)],[c_6578]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_6658,plain,
% 3.11/1.01      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK4,X0)) = k1_relat_1(k7_relat_1(sK4,X0)) ),
% 3.11/1.01      inference(light_normalisation,[status(thm)],[c_6559,c_6579]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_6562,plain,
% 3.11/1.01      ( m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
% 3.11/1.01      inference(demodulation,[status(thm)],[c_6557,c_6266]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_6635,plain,
% 3.11/1.01      ( m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.11/1.01      inference(light_normalisation,[status(thm)],[c_6562,c_6579]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_8,plain,
% 3.11/1.01      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.11/1.01      inference(cnf_transformation,[],[f93]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_6637,plain,
% 3.11/1.01      ( m1_subset_1(k7_relat_1(sK4,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.11/1.01      inference(demodulation,[status(thm)],[c_6635,c_8]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_22,plain,
% 3.11/1.01      ( v1_funct_2(X0,k1_xboole_0,X1)
% 3.11/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.11/1.01      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 3.11/1.01      inference(cnf_transformation,[],[f97]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_565,plain,
% 3.11/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.11/1.01      | ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 3.11/1.01      | ~ v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3))
% 3.11/1.01      | k2_partfun1(sK1,sK2,sK4,sK3) != X0
% 3.11/1.01      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 3.11/1.01      | sK3 != k1_xboole_0
% 3.11/1.01      | sK2 != X1 ),
% 3.11/1.01      inference(resolution_lifted,[status(thm)],[c_22,c_32]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_566,plain,
% 3.11/1.01      ( ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 3.11/1.01      | ~ m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
% 3.11/1.01      | ~ v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3))
% 3.11/1.01      | k1_relset_1(k1_xboole_0,sK2,k2_partfun1(sK1,sK2,sK4,sK3)) != k1_xboole_0
% 3.11/1.01      | sK3 != k1_xboole_0 ),
% 3.11/1.01      inference(unflattening,[status(thm)],[c_565]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_1755,plain,
% 3.11/1.01      ( k1_relset_1(k1_xboole_0,sK2,k2_partfun1(sK1,sK2,sK4,sK3)) != k1_xboole_0
% 3.11/1.01      | sK3 != k1_xboole_0
% 3.11/1.01      | m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 3.11/1.01      | m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top
% 3.11/1.01      | v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3)) != iProver_top ),
% 3.11/1.01      inference(predicate_to_equality,[status(thm)],[c_566]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_1969,plain,
% 3.11/1.01      ( k1_relset_1(k1_xboole_0,sK2,k2_partfun1(sK1,sK2,sK4,sK3)) != k1_xboole_0
% 3.11/1.01      | sK3 != k1_xboole_0
% 3.11/1.01      | m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 3.11/1.01      | m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.11/1.01      | v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3)) != iProver_top ),
% 3.11/1.01      inference(demodulation,[status(thm)],[c_1755,c_8]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_2352,plain,
% 3.11/1.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.11/1.01      | v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3))
% 3.11/1.01      | ~ v1_funct_1(sK4) ),
% 3.11/1.01      inference(instantiation,[status(thm)],[c_2222]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_2353,plain,
% 3.11/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.11/1.01      | v1_funct_1(k2_partfun1(sK1,sK2,sK4,sK3)) = iProver_top
% 3.11/1.01      | v1_funct_1(sK4) != iProver_top ),
% 3.11/1.01      inference(predicate_to_equality,[status(thm)],[c_2352]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_2484,plain,
% 3.11/1.01      ( m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.11/1.01      | m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 3.11/1.01      | sK3 != k1_xboole_0
% 3.11/1.01      | k1_relset_1(k1_xboole_0,sK2,k2_partfun1(sK1,sK2,sK4,sK3)) != k1_xboole_0 ),
% 3.11/1.01      inference(global_propositional_subsumption,
% 3.11/1.01                [status(thm)],
% 3.11/1.01                [c_1969,c_38,c_40,c_2353]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_2485,plain,
% 3.11/1.01      ( k1_relset_1(k1_xboole_0,sK2,k2_partfun1(sK1,sK2,sK4,sK3)) != k1_xboole_0
% 3.11/1.01      | sK3 != k1_xboole_0
% 3.11/1.01      | m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 3.11/1.01      | m1_subset_1(k2_partfun1(sK1,sK2,sK4,sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.11/1.01      inference(renaming,[status(thm)],[c_2484]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_4893,plain,
% 3.11/1.01      ( k1_relset_1(k1_xboole_0,sK2,k7_relat_1(sK4,sK3)) != k1_xboole_0
% 3.11/1.01      | sK3 != k1_xboole_0
% 3.11/1.01      | m1_subset_1(k7_relat_1(sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 3.11/1.01      | m1_subset_1(k7_relat_1(sK4,sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.11/1.01      inference(demodulation,[status(thm)],[c_4889,c_2485]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_6564,plain,
% 3.11/1.01      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK4,sK3)) != k1_xboole_0
% 3.11/1.01      | sK3 != k1_xboole_0
% 3.11/1.01      | m1_subset_1(k7_relat_1(sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) != iProver_top
% 3.11/1.01      | m1_subset_1(k7_relat_1(sK4,sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.11/1.01      inference(demodulation,[status(thm)],[c_6557,c_4893]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_7,plain,
% 3.11/1.01      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.11/1.01      inference(cnf_transformation,[],[f92]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_6626,plain,
% 3.11/1.01      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK4,sK3)) != k1_xboole_0
% 3.11/1.01      | sK3 != k1_xboole_0
% 3.11/1.01      | m1_subset_1(k7_relat_1(sK4,sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.11/1.01      inference(demodulation,[status(thm)],[c_6564,c_7]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_6641,plain,
% 3.11/1.01      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK4,sK3)) != k1_xboole_0
% 3.11/1.01      | sK3 != k1_xboole_0 ),
% 3.11/1.01      inference(backward_subsumption_resolution,[status(thm)],[c_6637,c_6626]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_6660,plain,
% 3.11/1.01      ( k1_relat_1(k7_relat_1(sK4,sK3)) != k1_xboole_0 | sK3 != k1_xboole_0 ),
% 3.11/1.01      inference(demodulation,[status(thm)],[c_6658,c_6641]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_6,plain,
% 3.11/1.01      ( r1_tarski(k1_xboole_0,X0) ),
% 3.11/1.01      inference(cnf_transformation,[],[f58]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_3076,plain,
% 3.11/1.01      ( r1_tarski(k1_xboole_0,sK3) ),
% 3.11/1.01      inference(instantiation,[status(thm)],[c_6]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_3077,plain,
% 3.11/1.01      ( r1_tarski(k1_xboole_0,sK3) = iProver_top ),
% 3.11/1.01      inference(predicate_to_equality,[status(thm)],[c_3076]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_3,plain,
% 3.11/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.11/1.01      inference(cnf_transformation,[],[f57]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_1777,plain,
% 3.11/1.01      ( X0 = X1
% 3.11/1.01      | r1_tarski(X1,X0) != iProver_top
% 3.11/1.01      | r1_tarski(X0,X1) != iProver_top ),
% 3.11/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_3256,plain,
% 3.11/1.01      ( sK3 = sK1 | r1_tarski(sK1,sK3) != iProver_top ),
% 3.11/1.01      inference(superposition,[status(thm)],[c_1763,c_1777]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_7164,plain,
% 3.11/1.01      ( sK3 = k1_xboole_0 | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
% 3.11/1.01      inference(demodulation,[status(thm)],[c_6579,c_3256]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_8822,plain,
% 3.11/1.01      ( k1_relat_1(k7_relat_1(sK4,sK3)) != k1_xboole_0 ),
% 3.11/1.01      inference(global_propositional_subsumption,
% 3.11/1.01                [status(thm)],
% 3.11/1.01                [c_6660,c_3077,c_7164]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_11,plain,
% 3.11/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.11/1.01      inference(cnf_transformation,[],[f62]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_1773,plain,
% 3.11/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.11/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 3.11/1.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_2657,plain,
% 3.11/1.01      ( r1_tarski(sK4,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
% 3.11/1.01      inference(superposition,[status(thm)],[c_1762,c_1773]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_6573,plain,
% 3.11/1.01      ( r1_tarski(sK4,k2_zfmisc_1(sK1,k1_xboole_0)) = iProver_top ),
% 3.11/1.01      inference(demodulation,[status(thm)],[c_6557,c_2657]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_6593,plain,
% 3.11/1.01      ( r1_tarski(sK4,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 3.11/1.01      inference(light_normalisation,[status(thm)],[c_6573,c_6579]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_6595,plain,
% 3.11/1.01      ( r1_tarski(sK4,k1_xboole_0) = iProver_top ),
% 3.11/1.01      inference(demodulation,[status(thm)],[c_6593,c_8]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_1775,plain,
% 3.11/1.01      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.11/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_3254,plain,
% 3.11/1.01      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.11/1.01      inference(superposition,[status(thm)],[c_1775,c_1777]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_6854,plain,
% 3.11/1.01      ( sK4 = k1_xboole_0 ),
% 3.11/1.01      inference(superposition,[status(thm)],[c_6595,c_3254]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_7165,plain,
% 3.11/1.01      ( r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 3.11/1.01      inference(demodulation,[status(thm)],[c_6579,c_1763]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_7256,plain,
% 3.11/1.01      ( sK3 = k1_xboole_0 ),
% 3.11/1.01      inference(superposition,[status(thm)],[c_7165,c_3254]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_8824,plain,
% 3.11/1.01      ( k1_relat_1(k7_relat_1(k1_xboole_0,k1_xboole_0)) != k1_xboole_0 ),
% 3.11/1.01      inference(light_normalisation,[status(thm)],[c_8822,c_6854,c_7256]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_15,plain,
% 3.11/1.01      ( r1_tarski(k7_relat_1(X0,X1),X0) | ~ v1_relat_1(X0) ),
% 3.11/1.01      inference(cnf_transformation,[],[f67]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_1771,plain,
% 3.11/1.01      ( r1_tarski(k7_relat_1(X0,X1),X0) = iProver_top
% 3.11/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.11/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_3559,plain,
% 3.11/1.01      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0
% 3.11/1.01      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.11/1.01      inference(superposition,[status(thm)],[c_1771,c_3254]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_83,plain,
% 3.11/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.11/1.01      | v1_relat_1(X0) = iProver_top ),
% 3.11/1.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_85,plain,
% 3.11/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 3.11/1.01      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.11/1.01      inference(instantiation,[status(thm)],[c_83]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_10,plain,
% 3.11/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.11/1.01      inference(cnf_transformation,[],[f63]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_2057,plain,
% 3.11/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.11/1.01      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
% 3.11/1.01      inference(instantiation,[status(thm)],[c_10]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_2058,plain,
% 3.11/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 3.11/1.01      | r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
% 3.11/1.01      inference(predicate_to_equality,[status(thm)],[c_2057]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_2060,plain,
% 3.11/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
% 3.11/1.01      | r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 3.11/1.01      inference(instantiation,[status(thm)],[c_2058]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_2211,plain,
% 3.11/1.01      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) ),
% 3.11/1.01      inference(instantiation,[status(thm)],[c_6]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_2214,plain,
% 3.11/1.01      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.11/1.01      inference(predicate_to_equality,[status(thm)],[c_2211]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_2216,plain,
% 3.11/1.01      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 3.11/1.01      inference(instantiation,[status(thm)],[c_2214]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_3624,plain,
% 3.11/1.01      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.11/1.01      inference(global_propositional_subsumption,
% 3.11/1.01                [status(thm)],
% 3.11/1.01                [c_3559,c_85,c_2060,c_2216]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_6572,plain,
% 3.11/1.01      ( k1_relset_1(sK1,k1_xboole_0,sK4) = k1_relat_1(sK4) ),
% 3.11/1.01      inference(demodulation,[status(thm)],[c_6557,c_3167]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_24,plain,
% 3.11/1.01      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 3.11/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.11/1.01      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 3.11/1.01      inference(cnf_transformation,[],[f98]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_584,plain,
% 3.11/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.11/1.01      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 3.11/1.01      | sK4 != X0
% 3.11/1.01      | sK2 != X1
% 3.11/1.01      | sK1 != k1_xboole_0 ),
% 3.11/1.01      inference(resolution_lifted,[status(thm)],[c_24,c_36]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_585,plain,
% 3.11/1.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
% 3.11/1.01      | k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
% 3.11/1.01      | sK1 != k1_xboole_0 ),
% 3.11/1.01      inference(unflattening,[status(thm)],[c_584]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_1754,plain,
% 3.11/1.01      ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
% 3.11/1.01      | sK1 != k1_xboole_0
% 3.11/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
% 3.11/1.01      inference(predicate_to_equality,[status(thm)],[c_585]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_1863,plain,
% 3.11/1.01      ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_xboole_0
% 3.11/1.01      | sK1 != k1_xboole_0
% 3.11/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.11/1.01      inference(demodulation,[status(thm)],[c_1754,c_8]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_6575,plain,
% 3.11/1.01      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
% 3.11/1.01      | sK1 != k1_xboole_0
% 3.11/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.11/1.01      inference(demodulation,[status(thm)],[c_6557,c_1863]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_6586,plain,
% 3.11/1.01      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
% 3.11/1.01      | k1_xboole_0 != k1_xboole_0
% 3.11/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.11/1.01      inference(light_normalisation,[status(thm)],[c_6575,c_6579]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_6587,plain,
% 3.11/1.01      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0
% 3.11/1.01      | m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.11/1.01      inference(equality_resolution_simp,[status(thm)],[c_6586]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_6577,plain,
% 3.11/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
% 3.11/1.01      inference(demodulation,[status(thm)],[c_6557,c_1762]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_6582,plain,
% 3.11/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.11/1.01      inference(light_normalisation,[status(thm)],[c_6577,c_6579]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_6584,plain,
% 3.11/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.11/1.01      inference(demodulation,[status(thm)],[c_6582,c_8]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_6590,plain,
% 3.11/1.01      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_xboole_0 ),
% 3.11/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_6587,c_6584]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_6597,plain,
% 3.11/1.01      ( k1_relat_1(sK4) = k1_xboole_0 ),
% 3.11/1.01      inference(light_normalisation,[status(thm)],[c_6572,c_6579,c_6590]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_8145,plain,
% 3.11/1.01      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.11/1.01      inference(demodulation,[status(thm)],[c_6854,c_6597]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_8825,plain,
% 3.11/1.01      ( k1_xboole_0 != k1_xboole_0 ),
% 3.11/1.01      inference(demodulation,[status(thm)],[c_8824,c_3624,c_8145]) ).
% 3.11/1.01  
% 3.11/1.01  cnf(c_8826,plain,
% 3.11/1.01      ( $false ),
% 3.11/1.01      inference(equality_resolution_simp,[status(thm)],[c_8825]) ).
% 3.11/1.01  
% 3.11/1.01  
% 3.11/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.11/1.01  
% 3.11/1.01  ------                               Statistics
% 3.11/1.01  
% 3.11/1.01  ------ General
% 3.11/1.01  
% 3.11/1.01  abstr_ref_over_cycles:                  0
% 3.11/1.01  abstr_ref_under_cycles:                 0
% 3.11/1.01  gc_basic_clause_elim:                   0
% 3.11/1.01  forced_gc_time:                         0
% 3.11/1.01  parsing_time:                           0.027
% 3.11/1.01  unif_index_cands_time:                  0.
% 3.11/1.01  unif_index_add_time:                    0.
% 3.11/1.01  orderings_time:                         0.
% 3.11/1.01  out_proof_time:                         0.012
% 3.11/1.01  total_time:                             0.298
% 3.11/1.01  num_of_symbols:                         51
% 3.11/1.01  num_of_terms:                           8791
% 3.11/1.01  
% 3.11/1.01  ------ Preprocessing
% 3.11/1.01  
% 3.11/1.01  num_of_splits:                          0
% 3.11/1.01  num_of_split_atoms:                     0
% 3.11/1.01  num_of_reused_defs:                     0
% 3.11/1.01  num_eq_ax_congr_red:                    22
% 3.11/1.01  num_of_sem_filtered_clauses:            1
% 3.11/1.01  num_of_subtypes:                        0
% 3.11/1.01  monotx_restored_types:                  0
% 3.11/1.01  sat_num_of_epr_types:                   0
% 3.11/1.01  sat_num_of_non_cyclic_types:            0
% 3.11/1.01  sat_guarded_non_collapsed_types:        0
% 3.11/1.01  num_pure_diseq_elim:                    0
% 3.11/1.01  simp_replaced_by:                       0
% 3.11/1.01  res_preprocessed:                       169
% 3.11/1.01  prep_upred:                             0
% 3.11/1.01  prep_unflattend:                        43
% 3.11/1.01  smt_new_axioms:                         0
% 3.11/1.01  pred_elim_cands:                        5
% 3.11/1.01  pred_elim:                              2
% 3.11/1.01  pred_elim_cl:                           0
% 3.11/1.01  pred_elim_cycles:                       4
% 3.11/1.01  merged_defs:                            8
% 3.11/1.01  merged_defs_ncl:                        0
% 3.11/1.01  bin_hyper_res:                          8
% 3.11/1.01  prep_cycles:                            4
% 3.11/1.01  pred_elim_time:                         0.013
% 3.11/1.01  splitting_time:                         0.
% 3.11/1.01  sem_filter_time:                        0.
% 3.11/1.01  monotx_time:                            0.
% 3.11/1.01  subtype_inf_time:                       0.
% 3.11/1.01  
% 3.11/1.01  ------ Problem properties
% 3.11/1.01  
% 3.11/1.01  clauses:                                36
% 3.11/1.01  conjectures:                            4
% 3.11/1.01  epr:                                    7
% 3.11/1.01  horn:                                   30
% 3.11/1.01  ground:                                 12
% 3.11/1.01  unary:                                  7
% 3.11/1.01  binary:                                 11
% 3.11/1.01  lits:                                   97
% 3.11/1.01  lits_eq:                                34
% 3.11/1.01  fd_pure:                                0
% 3.11/1.01  fd_pseudo:                              0
% 3.11/1.01  fd_cond:                                3
% 3.11/1.01  fd_pseudo_cond:                         1
% 3.11/1.01  ac_symbols:                             0
% 3.11/1.01  
% 3.11/1.01  ------ Propositional Solver
% 3.11/1.01  
% 3.11/1.01  prop_solver_calls:                      29
% 3.11/1.01  prop_fast_solver_calls:                 1251
% 3.11/1.01  smt_solver_calls:                       0
% 3.11/1.01  smt_fast_solver_calls:                  0
% 3.11/1.01  prop_num_of_clauses:                    3316
% 3.11/1.01  prop_preprocess_simplified:             8088
% 3.11/1.01  prop_fo_subsumed:                       20
% 3.11/1.01  prop_solver_time:                       0.
% 3.11/1.01  smt_solver_time:                        0.
% 3.11/1.01  smt_fast_solver_time:                   0.
% 3.11/1.01  prop_fast_solver_time:                  0.
% 3.11/1.01  prop_unsat_core_time:                   0.
% 3.11/1.01  
% 3.11/1.01  ------ QBF
% 3.11/1.01  
% 3.11/1.01  qbf_q_res:                              0
% 3.11/1.01  qbf_num_tautologies:                    0
% 3.11/1.01  qbf_prep_cycles:                        0
% 3.11/1.01  
% 3.11/1.01  ------ BMC1
% 3.11/1.01  
% 3.11/1.01  bmc1_current_bound:                     -1
% 3.11/1.01  bmc1_last_solved_bound:                 -1
% 3.11/1.01  bmc1_unsat_core_size:                   -1
% 3.11/1.01  bmc1_unsat_core_parents_size:           -1
% 3.11/1.01  bmc1_merge_next_fun:                    0
% 3.11/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.11/1.01  
% 3.11/1.01  ------ Instantiation
% 3.11/1.01  
% 3.11/1.01  inst_num_of_clauses:                    878
% 3.11/1.01  inst_num_in_passive:                    418
% 3.11/1.01  inst_num_in_active:                     420
% 3.11/1.01  inst_num_in_unprocessed:                40
% 3.11/1.01  inst_num_of_loops:                      540
% 3.11/1.01  inst_num_of_learning_restarts:          0
% 3.11/1.01  inst_num_moves_active_passive:          117
% 3.11/1.01  inst_lit_activity:                      0
% 3.11/1.01  inst_lit_activity_moves:                0
% 3.11/1.01  inst_num_tautologies:                   0
% 3.11/1.01  inst_num_prop_implied:                  0
% 3.11/1.01  inst_num_existing_simplified:           0
% 3.11/1.01  inst_num_eq_res_simplified:             0
% 3.11/1.01  inst_num_child_elim:                    0
% 3.11/1.01  inst_num_of_dismatching_blockings:      543
% 3.11/1.01  inst_num_of_non_proper_insts:           857
% 3.11/1.01  inst_num_of_duplicates:                 0
% 3.11/1.01  inst_inst_num_from_inst_to_res:         0
% 3.11/1.01  inst_dismatching_checking_time:         0.
% 3.11/1.01  
% 3.11/1.01  ------ Resolution
% 3.11/1.01  
% 3.11/1.01  res_num_of_clauses:                     0
% 3.11/1.01  res_num_in_passive:                     0
% 3.11/1.01  res_num_in_active:                      0
% 3.11/1.01  res_num_of_loops:                       173
% 3.11/1.01  res_forward_subset_subsumed:            29
% 3.11/1.01  res_backward_subset_subsumed:           0
% 3.11/1.01  res_forward_subsumed:                   0
% 3.11/1.01  res_backward_subsumed:                  0
% 3.11/1.01  res_forward_subsumption_resolution:     5
% 3.11/1.01  res_backward_subsumption_resolution:    0
% 3.11/1.01  res_clause_to_clause_subsumption:       529
% 3.11/1.01  res_orphan_elimination:                 0
% 3.11/1.01  res_tautology_del:                      50
% 3.11/1.01  res_num_eq_res_simplified:              1
% 3.11/1.01  res_num_sel_changes:                    0
% 3.11/1.01  res_moves_from_active_to_pass:          0
% 3.11/1.01  
% 3.11/1.01  ------ Superposition
% 3.11/1.01  
% 3.11/1.01  sup_time_total:                         0.
% 3.11/1.01  sup_time_generating:                    0.
% 3.11/1.01  sup_time_sim_full:                      0.
% 3.11/1.01  sup_time_sim_immed:                     0.
% 3.11/1.01  
% 3.11/1.01  sup_num_of_clauses:                     138
% 3.11/1.01  sup_num_in_active:                      53
% 3.11/1.01  sup_num_in_passive:                     85
% 3.11/1.01  sup_num_of_loops:                       106
% 3.11/1.01  sup_fw_superposition:                   91
% 3.11/1.01  sup_bw_superposition:                   110
% 3.11/1.01  sup_immediate_simplified:               65
% 3.11/1.01  sup_given_eliminated:                   4
% 3.11/1.01  comparisons_done:                       0
% 3.11/1.01  comparisons_avoided:                    25
% 3.11/1.01  
% 3.11/1.01  ------ Simplifications
% 3.11/1.01  
% 3.11/1.01  
% 3.11/1.01  sim_fw_subset_subsumed:                 14
% 3.11/1.01  sim_bw_subset_subsumed:                 18
% 3.11/1.01  sim_fw_subsumed:                        9
% 3.11/1.01  sim_bw_subsumed:                        0
% 3.11/1.01  sim_fw_subsumption_res:                 7
% 3.11/1.01  sim_bw_subsumption_res:                 3
% 3.11/1.01  sim_tautology_del:                      7
% 3.11/1.01  sim_eq_tautology_del:                   11
% 3.11/1.01  sim_eq_res_simp:                        3
% 3.11/1.01  sim_fw_demodulated:                     20
% 3.11/1.01  sim_bw_demodulated:                     54
% 3.11/1.01  sim_light_normalised:                   32
% 3.11/1.01  sim_joinable_taut:                      0
% 3.11/1.01  sim_joinable_simp:                      0
% 3.11/1.01  sim_ac_normalised:                      0
% 3.11/1.01  sim_smt_subsumption:                    0
% 3.11/1.01  
%------------------------------------------------------------------------------
