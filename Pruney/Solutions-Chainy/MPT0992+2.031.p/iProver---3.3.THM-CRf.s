%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:52 EST 2020

% Result     : Theorem 3.31s
% Output     : CNFRefutation 3.31s
% Verified   : 
% Statistics : Number of formulae       :  189 (4184 expanded)
%              Number of clauses        :  118 (1363 expanded)
%              Number of leaves         :   19 ( 784 expanded)
%              Depth                    :   25
%              Number of atoms          :  583 (23276 expanded)
%              Number of equality atoms :  282 (6199 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   1 average)

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
    inference(ennf_transformation,[],[f19])).

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

fof(f46,plain,
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

fof(f47,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f38,f46])).

fof(f81,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f47])).

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
    inference(ennf_transformation,[],[f14])).

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

fof(f45,plain,(
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

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f79,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f80,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f47])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f10,axiom,(
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
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f17,axiom,(
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
    inference(ennf_transformation,[],[f17])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f77,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f16,axiom,(
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
    inference(ennf_transformation,[],[f16])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f78,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f15,axiom,(
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
    inference(ennf_transformation,[],[f15])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f83,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f47])).

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

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f7,axiom,(
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
    inference(ennf_transformation,[],[f7])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f82,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f47])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f41])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f87,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f53])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f88,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f71])).

fof(f89,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f88])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f39])).

fof(f50,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f86,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f54])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

cnf(c_32,negated_conjecture,
    ( r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1633,plain,
    ( r1_tarski(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_608,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X0
    | sK1 != X2
    | sK0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_34])).

cnf(c_609,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_608])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_611,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_609,c_33])).

cnf(c_1632,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1638,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3157,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1632,c_1638])).

cnf(c_3425,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_611,c_3157])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1640,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3956,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3425,c_1640])).

cnf(c_38,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1911,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1912,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1911])).

cnf(c_4286,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | sK1 = k1_xboole_0
    | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3956,c_38,c_1912])).

cnf(c_4287,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4286])).

cnf(c_4297,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1633,c_4287])).

cnf(c_27,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1634,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_4563,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4297,c_1634])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1635,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4876,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1632,c_1635])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1992,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_2079,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_1992])).

cnf(c_5184,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4876,c_35,c_33,c_2079])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1636,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3988,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1632,c_1636])).

cnf(c_36,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_1965,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(k2_partfun1(X0,X1,sK3,X2))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_2054,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1965])).

cnf(c_2055,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2054])).

cnf(c_4267,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3988,c_36,c_38,c_2055])).

cnf(c_5193,plain,
    ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5184,c_4267])).

cnf(c_5476,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4563,c_5193])).

cnf(c_28,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_30,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_619,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_relat_1(X0)
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_relat_1(X0) != sK2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_30])).

cnf(c_620,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
    inference(unflattening,[status(thm)],[c_619])).

cnf(c_16,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_11,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_407,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_16,c_11])).

cnf(c_411,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_407,c_15])).

cnf(c_412,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_411])).

cnf(c_632,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_620,c_15,c_412])).

cnf(c_1621,plain,
    ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_632])).

cnf(c_5191,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5184,c_1621])).

cnf(c_5207,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5191,c_5193])).

cnf(c_5612,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4297,c_5207])).

cnf(c_6043,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5476,c_5612])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1637,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_5668,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5184,c_1637])).

cnf(c_6134,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5668,c_36,c_38])).

cnf(c_1639,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_6146,plain,
    ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6134,c_1639])).

cnf(c_1630,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_412])).

cnf(c_6145,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_6134,c_1630])).

cnf(c_7194,plain,
    ( sK1 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6043,c_6146,c_6145])).

cnf(c_7201,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7194,c_6134])).

cnf(c_31,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_7218,plain,
    ( sK0 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7194,c_31])).

cnf(c_7219,plain,
    ( sK0 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_7218])).

cnf(c_7277,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7201,c_7219])).

cnf(c_5,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_7279,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7277,c_5])).

cnf(c_18,plain,
    ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_436,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK2 != X0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_30])).

cnf(c_437,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_436])).

cnf(c_7,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_451,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_437,c_7])).

cnf(c_1629,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_451])).

cnf(c_457,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_451])).

cnf(c_2166,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2054])).

cnf(c_2167,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2166])).

cnf(c_2216,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | k1_xboole_0 = sK2
    | sK1 != k1_xboole_0
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1629,c_36,c_38,c_457,c_2167])).

cnf(c_2217,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2216])).

cnf(c_5189,plain,
    ( k7_relat_1(sK3,sK2) != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5184,c_2217])).

cnf(c_6,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_106,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_107,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1935,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK2)
    | sK2 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_965,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2112,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_965])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2382,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2))
    | r1_tarski(X0,sK2) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2384,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2))
    | r1_tarski(k1_xboole_0,sK2) ),
    inference(instantiation,[status(thm)],[c_2382])).

cnf(c_966,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2852,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_966])).

cnf(c_2853,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2852])).

cnf(c_3313,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_967,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2093,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_967])).

cnf(c_2398,plain,
    ( ~ r1_tarski(sK2,X0)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != sK2
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_2093])).

cnf(c_3340,plain,
    ( ~ r1_tarski(sK2,sK0)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != sK2
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_2398])).

cnf(c_5328,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5189,c_32,c_31,c_106,c_107,c_1935,c_2112,c_2384,c_2853,c_3313,c_3340,c_4297,c_5207])).

cnf(c_7205,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7194,c_5328])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_7258,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7205,c_4])).

cnf(c_7281,plain,
    ( sK2 = k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_7279,c_7258])).

cnf(c_7202,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7194,c_5207])).

cnf(c_7274,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7202,c_4])).

cnf(c_7282,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_7279,c_7274])).

cnf(c_7289,plain,
    ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7281,c_7282])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2262,plain,
    ( r1_tarski(k1_xboole_0,k1_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1997,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1999,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1997])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7289,c_2262,c_1999,c_1911,c_33])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 17:51:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.31/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.31/0.99  
% 3.31/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.31/0.99  
% 3.31/0.99  ------  iProver source info
% 3.31/0.99  
% 3.31/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.31/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.31/0.99  git: non_committed_changes: false
% 3.31/0.99  git: last_make_outside_of_git: false
% 3.31/0.99  
% 3.31/0.99  ------ 
% 3.31/0.99  
% 3.31/0.99  ------ Input Options
% 3.31/0.99  
% 3.31/0.99  --out_options                           all
% 3.31/0.99  --tptp_safe_out                         true
% 3.31/0.99  --problem_path                          ""
% 3.31/0.99  --include_path                          ""
% 3.31/0.99  --clausifier                            res/vclausify_rel
% 3.31/0.99  --clausifier_options                    --mode clausify
% 3.31/0.99  --stdin                                 false
% 3.31/0.99  --stats_out                             all
% 3.31/0.99  
% 3.31/0.99  ------ General Options
% 3.31/0.99  
% 3.31/0.99  --fof                                   false
% 3.31/0.99  --time_out_real                         305.
% 3.31/0.99  --time_out_virtual                      -1.
% 3.31/0.99  --symbol_type_check                     false
% 3.31/0.99  --clausify_out                          false
% 3.31/0.99  --sig_cnt_out                           false
% 3.31/0.99  --trig_cnt_out                          false
% 3.31/0.99  --trig_cnt_out_tolerance                1.
% 3.31/0.99  --trig_cnt_out_sk_spl                   false
% 3.31/0.99  --abstr_cl_out                          false
% 3.31/0.99  
% 3.31/0.99  ------ Global Options
% 3.31/0.99  
% 3.31/0.99  --schedule                              default
% 3.31/0.99  --add_important_lit                     false
% 3.31/0.99  --prop_solver_per_cl                    1000
% 3.31/0.99  --min_unsat_core                        false
% 3.31/0.99  --soft_assumptions                      false
% 3.31/0.99  --soft_lemma_size                       3
% 3.31/0.99  --prop_impl_unit_size                   0
% 3.31/0.99  --prop_impl_unit                        []
% 3.31/0.99  --share_sel_clauses                     true
% 3.31/0.99  --reset_solvers                         false
% 3.31/0.99  --bc_imp_inh                            [conj_cone]
% 3.31/0.99  --conj_cone_tolerance                   3.
% 3.31/0.99  --extra_neg_conj                        none
% 3.31/0.99  --large_theory_mode                     true
% 3.31/0.99  --prolific_symb_bound                   200
% 3.31/0.99  --lt_threshold                          2000
% 3.31/0.99  --clause_weak_htbl                      true
% 3.31/0.99  --gc_record_bc_elim                     false
% 3.31/0.99  
% 3.31/0.99  ------ Preprocessing Options
% 3.31/0.99  
% 3.31/0.99  --preprocessing_flag                    true
% 3.31/0.99  --time_out_prep_mult                    0.1
% 3.31/0.99  --splitting_mode                        input
% 3.31/0.99  --splitting_grd                         true
% 3.31/0.99  --splitting_cvd                         false
% 3.31/0.99  --splitting_cvd_svl                     false
% 3.31/0.99  --splitting_nvd                         32
% 3.31/0.99  --sub_typing                            true
% 3.31/0.99  --prep_gs_sim                           true
% 3.31/0.99  --prep_unflatten                        true
% 3.31/0.99  --prep_res_sim                          true
% 3.31/0.99  --prep_upred                            true
% 3.31/0.99  --prep_sem_filter                       exhaustive
% 3.31/0.99  --prep_sem_filter_out                   false
% 3.31/0.99  --pred_elim                             true
% 3.31/0.99  --res_sim_input                         true
% 3.31/0.99  --eq_ax_congr_red                       true
% 3.31/0.99  --pure_diseq_elim                       true
% 3.31/0.99  --brand_transform                       false
% 3.31/0.99  --non_eq_to_eq                          false
% 3.31/0.99  --prep_def_merge                        true
% 3.31/0.99  --prep_def_merge_prop_impl              false
% 3.31/0.99  --prep_def_merge_mbd                    true
% 3.31/0.99  --prep_def_merge_tr_red                 false
% 3.31/0.99  --prep_def_merge_tr_cl                  false
% 3.31/0.99  --smt_preprocessing                     true
% 3.31/0.99  --smt_ac_axioms                         fast
% 3.31/0.99  --preprocessed_out                      false
% 3.31/0.99  --preprocessed_stats                    false
% 3.31/0.99  
% 3.31/0.99  ------ Abstraction refinement Options
% 3.31/0.99  
% 3.31/0.99  --abstr_ref                             []
% 3.31/0.99  --abstr_ref_prep                        false
% 3.31/0.99  --abstr_ref_until_sat                   false
% 3.31/0.99  --abstr_ref_sig_restrict                funpre
% 3.31/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.31/0.99  --abstr_ref_under                       []
% 3.31/0.99  
% 3.31/0.99  ------ SAT Options
% 3.31/0.99  
% 3.31/0.99  --sat_mode                              false
% 3.31/0.99  --sat_fm_restart_options                ""
% 3.31/0.99  --sat_gr_def                            false
% 3.31/0.99  --sat_epr_types                         true
% 3.31/0.99  --sat_non_cyclic_types                  false
% 3.31/0.99  --sat_finite_models                     false
% 3.31/0.99  --sat_fm_lemmas                         false
% 3.31/0.99  --sat_fm_prep                           false
% 3.31/0.99  --sat_fm_uc_incr                        true
% 3.31/0.99  --sat_out_model                         small
% 3.31/0.99  --sat_out_clauses                       false
% 3.31/0.99  
% 3.31/0.99  ------ QBF Options
% 3.31/0.99  
% 3.31/0.99  --qbf_mode                              false
% 3.31/0.99  --qbf_elim_univ                         false
% 3.31/0.99  --qbf_dom_inst                          none
% 3.31/0.99  --qbf_dom_pre_inst                      false
% 3.31/0.99  --qbf_sk_in                             false
% 3.31/0.99  --qbf_pred_elim                         true
% 3.31/0.99  --qbf_split                             512
% 3.31/0.99  
% 3.31/0.99  ------ BMC1 Options
% 3.31/0.99  
% 3.31/0.99  --bmc1_incremental                      false
% 3.31/0.99  --bmc1_axioms                           reachable_all
% 3.31/0.99  --bmc1_min_bound                        0
% 3.31/0.99  --bmc1_max_bound                        -1
% 3.31/0.99  --bmc1_max_bound_default                -1
% 3.31/0.99  --bmc1_symbol_reachability              true
% 3.31/0.99  --bmc1_property_lemmas                  false
% 3.31/0.99  --bmc1_k_induction                      false
% 3.31/0.99  --bmc1_non_equiv_states                 false
% 3.31/0.99  --bmc1_deadlock                         false
% 3.31/0.99  --bmc1_ucm                              false
% 3.31/0.99  --bmc1_add_unsat_core                   none
% 3.31/0.99  --bmc1_unsat_core_children              false
% 3.31/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.31/0.99  --bmc1_out_stat                         full
% 3.31/0.99  --bmc1_ground_init                      false
% 3.31/0.99  --bmc1_pre_inst_next_state              false
% 3.31/0.99  --bmc1_pre_inst_state                   false
% 3.31/0.99  --bmc1_pre_inst_reach_state             false
% 3.31/0.99  --bmc1_out_unsat_core                   false
% 3.31/0.99  --bmc1_aig_witness_out                  false
% 3.31/0.99  --bmc1_verbose                          false
% 3.31/0.99  --bmc1_dump_clauses_tptp                false
% 3.31/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.31/0.99  --bmc1_dump_file                        -
% 3.31/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.31/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.31/0.99  --bmc1_ucm_extend_mode                  1
% 3.31/0.99  --bmc1_ucm_init_mode                    2
% 3.31/0.99  --bmc1_ucm_cone_mode                    none
% 3.31/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.31/0.99  --bmc1_ucm_relax_model                  4
% 3.31/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.31/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.31/0.99  --bmc1_ucm_layered_model                none
% 3.31/0.99  --bmc1_ucm_max_lemma_size               10
% 3.31/0.99  
% 3.31/0.99  ------ AIG Options
% 3.31/0.99  
% 3.31/0.99  --aig_mode                              false
% 3.31/0.99  
% 3.31/0.99  ------ Instantiation Options
% 3.31/0.99  
% 3.31/0.99  --instantiation_flag                    true
% 3.31/0.99  --inst_sos_flag                         false
% 3.31/0.99  --inst_sos_phase                        true
% 3.31/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.31/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.31/0.99  --inst_lit_sel_side                     num_symb
% 3.31/0.99  --inst_solver_per_active                1400
% 3.31/0.99  --inst_solver_calls_frac                1.
% 3.31/0.99  --inst_passive_queue_type               priority_queues
% 3.31/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.31/0.99  --inst_passive_queues_freq              [25;2]
% 3.31/0.99  --inst_dismatching                      true
% 3.31/0.99  --inst_eager_unprocessed_to_passive     true
% 3.31/0.99  --inst_prop_sim_given                   true
% 3.31/0.99  --inst_prop_sim_new                     false
% 3.31/0.99  --inst_subs_new                         false
% 3.31/0.99  --inst_eq_res_simp                      false
% 3.31/0.99  --inst_subs_given                       false
% 3.31/0.99  --inst_orphan_elimination               true
% 3.31/0.99  --inst_learning_loop_flag               true
% 3.31/0.99  --inst_learning_start                   3000
% 3.31/0.99  --inst_learning_factor                  2
% 3.31/0.99  --inst_start_prop_sim_after_learn       3
% 3.31/0.99  --inst_sel_renew                        solver
% 3.31/0.99  --inst_lit_activity_flag                true
% 3.31/0.99  --inst_restr_to_given                   false
% 3.31/0.99  --inst_activity_threshold               500
% 3.31/0.99  --inst_out_proof                        true
% 3.31/0.99  
% 3.31/0.99  ------ Resolution Options
% 3.31/0.99  
% 3.31/0.99  --resolution_flag                       true
% 3.31/0.99  --res_lit_sel                           adaptive
% 3.31/0.99  --res_lit_sel_side                      none
% 3.31/0.99  --res_ordering                          kbo
% 3.31/0.99  --res_to_prop_solver                    active
% 3.31/0.99  --res_prop_simpl_new                    false
% 3.31/0.99  --res_prop_simpl_given                  true
% 3.31/0.99  --res_passive_queue_type                priority_queues
% 3.31/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.31/0.99  --res_passive_queues_freq               [15;5]
% 3.31/0.99  --res_forward_subs                      full
% 3.31/0.99  --res_backward_subs                     full
% 3.31/0.99  --res_forward_subs_resolution           true
% 3.31/0.99  --res_backward_subs_resolution          true
% 3.31/0.99  --res_orphan_elimination                true
% 3.31/0.99  --res_time_limit                        2.
% 3.31/0.99  --res_out_proof                         true
% 3.31/0.99  
% 3.31/0.99  ------ Superposition Options
% 3.31/0.99  
% 3.31/0.99  --superposition_flag                    true
% 3.31/0.99  --sup_passive_queue_type                priority_queues
% 3.31/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.31/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.31/0.99  --demod_completeness_check              fast
% 3.31/0.99  --demod_use_ground                      true
% 3.31/0.99  --sup_to_prop_solver                    passive
% 3.31/0.99  --sup_prop_simpl_new                    true
% 3.31/0.99  --sup_prop_simpl_given                  true
% 3.31/0.99  --sup_fun_splitting                     false
% 3.31/0.99  --sup_smt_interval                      50000
% 3.31/0.99  
% 3.31/0.99  ------ Superposition Simplification Setup
% 3.31/0.99  
% 3.31/0.99  --sup_indices_passive                   []
% 3.31/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.31/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.31/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.31/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.31/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.31/0.99  --sup_full_bw                           [BwDemod]
% 3.31/0.99  --sup_immed_triv                        [TrivRules]
% 3.31/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.31/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.31/0.99  --sup_immed_bw_main                     []
% 3.31/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.31/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.31/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.31/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.31/0.99  
% 3.31/0.99  ------ Combination Options
% 3.31/0.99  
% 3.31/0.99  --comb_res_mult                         3
% 3.31/0.99  --comb_sup_mult                         2
% 3.31/0.99  --comb_inst_mult                        10
% 3.31/0.99  
% 3.31/0.99  ------ Debug Options
% 3.31/0.99  
% 3.31/0.99  --dbg_backtrace                         false
% 3.31/0.99  --dbg_dump_prop_clauses                 false
% 3.31/0.99  --dbg_dump_prop_clauses_file            -
% 3.31/0.99  --dbg_out_stat                          false
% 3.31/0.99  ------ Parsing...
% 3.31/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.31/0.99  
% 3.31/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.31/0.99  
% 3.31/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.31/0.99  
% 3.31/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.31/0.99  ------ Proving...
% 3.31/0.99  ------ Problem Properties 
% 3.31/0.99  
% 3.31/0.99  
% 3.31/0.99  clauses                                 34
% 3.31/0.99  conjectures                             4
% 3.31/0.99  EPR                                     6
% 3.31/0.99  Horn                                    29
% 3.31/0.99  unary                                   9
% 3.31/0.99  binary                                  8
% 3.31/0.99  lits                                    89
% 3.31/0.99  lits eq                                 35
% 3.31/0.99  fd_pure                                 0
% 3.31/0.99  fd_pseudo                               0
% 3.31/0.99  fd_cond                                 3
% 3.31/0.99  fd_pseudo_cond                          1
% 3.31/0.99  AC symbols                              0
% 3.31/0.99  
% 3.31/0.99  ------ Schedule dynamic 5 is on 
% 3.31/0.99  
% 3.31/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.31/0.99  
% 3.31/0.99  
% 3.31/0.99  ------ 
% 3.31/0.99  Current options:
% 3.31/0.99  ------ 
% 3.31/0.99  
% 3.31/0.99  ------ Input Options
% 3.31/0.99  
% 3.31/0.99  --out_options                           all
% 3.31/0.99  --tptp_safe_out                         true
% 3.31/0.99  --problem_path                          ""
% 3.31/0.99  --include_path                          ""
% 3.31/0.99  --clausifier                            res/vclausify_rel
% 3.31/0.99  --clausifier_options                    --mode clausify
% 3.31/0.99  --stdin                                 false
% 3.31/0.99  --stats_out                             all
% 3.31/0.99  
% 3.31/0.99  ------ General Options
% 3.31/0.99  
% 3.31/0.99  --fof                                   false
% 3.31/0.99  --time_out_real                         305.
% 3.31/0.99  --time_out_virtual                      -1.
% 3.31/0.99  --symbol_type_check                     false
% 3.31/0.99  --clausify_out                          false
% 3.31/0.99  --sig_cnt_out                           false
% 3.31/0.99  --trig_cnt_out                          false
% 3.31/0.99  --trig_cnt_out_tolerance                1.
% 3.31/0.99  --trig_cnt_out_sk_spl                   false
% 3.31/0.99  --abstr_cl_out                          false
% 3.31/0.99  
% 3.31/0.99  ------ Global Options
% 3.31/0.99  
% 3.31/0.99  --schedule                              default
% 3.31/0.99  --add_important_lit                     false
% 3.31/0.99  --prop_solver_per_cl                    1000
% 3.31/0.99  --min_unsat_core                        false
% 3.31/0.99  --soft_assumptions                      false
% 3.31/0.99  --soft_lemma_size                       3
% 3.31/0.99  --prop_impl_unit_size                   0
% 3.31/0.99  --prop_impl_unit                        []
% 3.31/0.99  --share_sel_clauses                     true
% 3.31/0.99  --reset_solvers                         false
% 3.31/0.99  --bc_imp_inh                            [conj_cone]
% 3.31/0.99  --conj_cone_tolerance                   3.
% 3.31/0.99  --extra_neg_conj                        none
% 3.31/0.99  --large_theory_mode                     true
% 3.31/0.99  --prolific_symb_bound                   200
% 3.31/0.99  --lt_threshold                          2000
% 3.31/0.99  --clause_weak_htbl                      true
% 3.31/0.99  --gc_record_bc_elim                     false
% 3.31/0.99  
% 3.31/0.99  ------ Preprocessing Options
% 3.31/0.99  
% 3.31/0.99  --preprocessing_flag                    true
% 3.31/0.99  --time_out_prep_mult                    0.1
% 3.31/0.99  --splitting_mode                        input
% 3.31/0.99  --splitting_grd                         true
% 3.31/0.99  --splitting_cvd                         false
% 3.31/0.99  --splitting_cvd_svl                     false
% 3.31/0.99  --splitting_nvd                         32
% 3.31/0.99  --sub_typing                            true
% 3.31/0.99  --prep_gs_sim                           true
% 3.31/0.99  --prep_unflatten                        true
% 3.31/0.99  --prep_res_sim                          true
% 3.31/0.99  --prep_upred                            true
% 3.31/0.99  --prep_sem_filter                       exhaustive
% 3.31/0.99  --prep_sem_filter_out                   false
% 3.31/0.99  --pred_elim                             true
% 3.31/0.99  --res_sim_input                         true
% 3.31/0.99  --eq_ax_congr_red                       true
% 3.31/0.99  --pure_diseq_elim                       true
% 3.31/0.99  --brand_transform                       false
% 3.31/0.99  --non_eq_to_eq                          false
% 3.31/0.99  --prep_def_merge                        true
% 3.31/0.99  --prep_def_merge_prop_impl              false
% 3.31/0.99  --prep_def_merge_mbd                    true
% 3.31/0.99  --prep_def_merge_tr_red                 false
% 3.31/0.99  --prep_def_merge_tr_cl                  false
% 3.31/0.99  --smt_preprocessing                     true
% 3.31/0.99  --smt_ac_axioms                         fast
% 3.31/0.99  --preprocessed_out                      false
% 3.31/0.99  --preprocessed_stats                    false
% 3.31/0.99  
% 3.31/0.99  ------ Abstraction refinement Options
% 3.31/0.99  
% 3.31/0.99  --abstr_ref                             []
% 3.31/0.99  --abstr_ref_prep                        false
% 3.31/0.99  --abstr_ref_until_sat                   false
% 3.31/0.99  --abstr_ref_sig_restrict                funpre
% 3.31/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.31/0.99  --abstr_ref_under                       []
% 3.31/0.99  
% 3.31/0.99  ------ SAT Options
% 3.31/0.99  
% 3.31/0.99  --sat_mode                              false
% 3.31/0.99  --sat_fm_restart_options                ""
% 3.31/0.99  --sat_gr_def                            false
% 3.31/0.99  --sat_epr_types                         true
% 3.31/0.99  --sat_non_cyclic_types                  false
% 3.31/0.99  --sat_finite_models                     false
% 3.31/0.99  --sat_fm_lemmas                         false
% 3.31/0.99  --sat_fm_prep                           false
% 3.31/0.99  --sat_fm_uc_incr                        true
% 3.31/0.99  --sat_out_model                         small
% 3.31/0.99  --sat_out_clauses                       false
% 3.31/0.99  
% 3.31/0.99  ------ QBF Options
% 3.31/0.99  
% 3.31/0.99  --qbf_mode                              false
% 3.31/0.99  --qbf_elim_univ                         false
% 3.31/0.99  --qbf_dom_inst                          none
% 3.31/0.99  --qbf_dom_pre_inst                      false
% 3.31/0.99  --qbf_sk_in                             false
% 3.31/0.99  --qbf_pred_elim                         true
% 3.31/0.99  --qbf_split                             512
% 3.31/0.99  
% 3.31/0.99  ------ BMC1 Options
% 3.31/0.99  
% 3.31/0.99  --bmc1_incremental                      false
% 3.31/0.99  --bmc1_axioms                           reachable_all
% 3.31/0.99  --bmc1_min_bound                        0
% 3.31/0.99  --bmc1_max_bound                        -1
% 3.31/0.99  --bmc1_max_bound_default                -1
% 3.31/0.99  --bmc1_symbol_reachability              true
% 3.31/0.99  --bmc1_property_lemmas                  false
% 3.31/0.99  --bmc1_k_induction                      false
% 3.31/0.99  --bmc1_non_equiv_states                 false
% 3.31/0.99  --bmc1_deadlock                         false
% 3.31/0.99  --bmc1_ucm                              false
% 3.31/0.99  --bmc1_add_unsat_core                   none
% 3.31/0.99  --bmc1_unsat_core_children              false
% 3.31/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.31/0.99  --bmc1_out_stat                         full
% 3.31/0.99  --bmc1_ground_init                      false
% 3.31/0.99  --bmc1_pre_inst_next_state              false
% 3.31/0.99  --bmc1_pre_inst_state                   false
% 3.31/0.99  --bmc1_pre_inst_reach_state             false
% 3.31/0.99  --bmc1_out_unsat_core                   false
% 3.31/0.99  --bmc1_aig_witness_out                  false
% 3.31/0.99  --bmc1_verbose                          false
% 3.31/0.99  --bmc1_dump_clauses_tptp                false
% 3.31/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.31/0.99  --bmc1_dump_file                        -
% 3.31/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.31/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.31/0.99  --bmc1_ucm_extend_mode                  1
% 3.31/0.99  --bmc1_ucm_init_mode                    2
% 3.31/0.99  --bmc1_ucm_cone_mode                    none
% 3.31/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.31/0.99  --bmc1_ucm_relax_model                  4
% 3.31/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.31/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.31/0.99  --bmc1_ucm_layered_model                none
% 3.31/0.99  --bmc1_ucm_max_lemma_size               10
% 3.31/0.99  
% 3.31/0.99  ------ AIG Options
% 3.31/0.99  
% 3.31/0.99  --aig_mode                              false
% 3.31/0.99  
% 3.31/0.99  ------ Instantiation Options
% 3.31/0.99  
% 3.31/0.99  --instantiation_flag                    true
% 3.31/0.99  --inst_sos_flag                         false
% 3.31/0.99  --inst_sos_phase                        true
% 3.31/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.31/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.31/0.99  --inst_lit_sel_side                     none
% 3.31/0.99  --inst_solver_per_active                1400
% 3.31/0.99  --inst_solver_calls_frac                1.
% 3.31/0.99  --inst_passive_queue_type               priority_queues
% 3.31/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.31/0.99  --inst_passive_queues_freq              [25;2]
% 3.31/0.99  --inst_dismatching                      true
% 3.31/0.99  --inst_eager_unprocessed_to_passive     true
% 3.31/0.99  --inst_prop_sim_given                   true
% 3.31/0.99  --inst_prop_sim_new                     false
% 3.31/0.99  --inst_subs_new                         false
% 3.31/0.99  --inst_eq_res_simp                      false
% 3.31/0.99  --inst_subs_given                       false
% 3.31/0.99  --inst_orphan_elimination               true
% 3.31/0.99  --inst_learning_loop_flag               true
% 3.31/0.99  --inst_learning_start                   3000
% 3.31/0.99  --inst_learning_factor                  2
% 3.31/0.99  --inst_start_prop_sim_after_learn       3
% 3.31/0.99  --inst_sel_renew                        solver
% 3.31/0.99  --inst_lit_activity_flag                true
% 3.31/0.99  --inst_restr_to_given                   false
% 3.31/0.99  --inst_activity_threshold               500
% 3.31/0.99  --inst_out_proof                        true
% 3.31/0.99  
% 3.31/0.99  ------ Resolution Options
% 3.31/0.99  
% 3.31/0.99  --resolution_flag                       false
% 3.31/0.99  --res_lit_sel                           adaptive
% 3.31/0.99  --res_lit_sel_side                      none
% 3.31/0.99  --res_ordering                          kbo
% 3.31/0.99  --res_to_prop_solver                    active
% 3.31/0.99  --res_prop_simpl_new                    false
% 3.31/0.99  --res_prop_simpl_given                  true
% 3.31/0.99  --res_passive_queue_type                priority_queues
% 3.31/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.31/0.99  --res_passive_queues_freq               [15;5]
% 3.31/0.99  --res_forward_subs                      full
% 3.31/0.99  --res_backward_subs                     full
% 3.31/0.99  --res_forward_subs_resolution           true
% 3.31/0.99  --res_backward_subs_resolution          true
% 3.31/0.99  --res_orphan_elimination                true
% 3.31/0.99  --res_time_limit                        2.
% 3.31/0.99  --res_out_proof                         true
% 3.31/0.99  
% 3.31/0.99  ------ Superposition Options
% 3.31/0.99  
% 3.31/0.99  --superposition_flag                    true
% 3.31/0.99  --sup_passive_queue_type                priority_queues
% 3.31/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.31/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.31/0.99  --demod_completeness_check              fast
% 3.31/0.99  --demod_use_ground                      true
% 3.31/0.99  --sup_to_prop_solver                    passive
% 3.31/0.99  --sup_prop_simpl_new                    true
% 3.31/0.99  --sup_prop_simpl_given                  true
% 3.31/0.99  --sup_fun_splitting                     false
% 3.31/0.99  --sup_smt_interval                      50000
% 3.31/0.99  
% 3.31/0.99  ------ Superposition Simplification Setup
% 3.31/0.99  
% 3.31/0.99  --sup_indices_passive                   []
% 3.31/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.31/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.31/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.31/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.31/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.31/0.99  --sup_full_bw                           [BwDemod]
% 3.31/0.99  --sup_immed_triv                        [TrivRules]
% 3.31/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.31/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.31/0.99  --sup_immed_bw_main                     []
% 3.31/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.31/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.31/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.31/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.31/0.99  
% 3.31/0.99  ------ Combination Options
% 3.31/0.99  
% 3.31/0.99  --comb_res_mult                         3
% 3.31/0.99  --comb_sup_mult                         2
% 3.31/0.99  --comb_inst_mult                        10
% 3.31/0.99  
% 3.31/0.99  ------ Debug Options
% 3.31/0.99  
% 3.31/0.99  --dbg_backtrace                         false
% 3.31/0.99  --dbg_dump_prop_clauses                 false
% 3.31/0.99  --dbg_dump_prop_clauses_file            -
% 3.31/0.99  --dbg_out_stat                          false
% 3.31/0.99  
% 3.31/0.99  
% 3.31/0.99  
% 3.31/0.99  
% 3.31/0.99  ------ Proving...
% 3.31/0.99  
% 3.31/0.99  
% 3.31/0.99  % SZS status Theorem for theBenchmark.p
% 3.31/0.99  
% 3.31/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.31/0.99  
% 3.31/0.99  fof(f18,conjecture,(
% 3.31/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.31/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/0.99  
% 3.31/0.99  fof(f19,negated_conjecture,(
% 3.31/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.31/0.99    inference(negated_conjecture,[],[f18])).
% 3.31/0.99  
% 3.31/0.99  fof(f37,plain,(
% 3.31/0.99    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.31/0.99    inference(ennf_transformation,[],[f19])).
% 3.31/0.99  
% 3.31/0.99  fof(f38,plain,(
% 3.31/0.99    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.31/0.99    inference(flattening,[],[f37])).
% 3.31/0.99  
% 3.31/0.99  fof(f46,plain,(
% 3.31/0.99    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 3.31/0.99    introduced(choice_axiom,[])).
% 3.31/0.99  
% 3.31/0.99  fof(f47,plain,(
% 3.31/0.99    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 3.31/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f38,f46])).
% 3.31/0.99  
% 3.31/0.99  fof(f81,plain,(
% 3.31/0.99    r1_tarski(sK2,sK0)),
% 3.31/0.99    inference(cnf_transformation,[],[f47])).
% 3.31/0.99  
% 3.31/0.99  fof(f14,axiom,(
% 3.31/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.31/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/0.99  
% 3.31/0.99  fof(f29,plain,(
% 3.31/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.31/0.99    inference(ennf_transformation,[],[f14])).
% 3.31/0.99  
% 3.31/0.99  fof(f30,plain,(
% 3.31/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.31/0.99    inference(flattening,[],[f29])).
% 3.31/0.99  
% 3.31/0.99  fof(f45,plain,(
% 3.31/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.31/0.99    inference(nnf_transformation,[],[f30])).
% 3.31/0.99  
% 3.31/0.99  fof(f66,plain,(
% 3.31/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.31/0.99    inference(cnf_transformation,[],[f45])).
% 3.31/0.99  
% 3.31/0.99  fof(f79,plain,(
% 3.31/0.99    v1_funct_2(sK3,sK0,sK1)),
% 3.31/0.99    inference(cnf_transformation,[],[f47])).
% 3.31/0.99  
% 3.31/0.99  fof(f80,plain,(
% 3.31/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.31/0.99    inference(cnf_transformation,[],[f47])).
% 3.31/0.99  
% 3.31/0.99  fof(f13,axiom,(
% 3.31/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.31/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/0.99  
% 3.31/0.99  fof(f28,plain,(
% 3.31/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.31/0.99    inference(ennf_transformation,[],[f13])).
% 3.31/0.99  
% 3.31/0.99  fof(f65,plain,(
% 3.31/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.31/0.99    inference(cnf_transformation,[],[f28])).
% 3.31/0.99  
% 3.31/0.99  fof(f10,axiom,(
% 3.31/0.99    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 3.31/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/0.99  
% 3.31/0.99  fof(f24,plain,(
% 3.31/0.99    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 3.31/0.99    inference(ennf_transformation,[],[f10])).
% 3.31/0.99  
% 3.31/0.99  fof(f25,plain,(
% 3.31/0.99    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.31/0.99    inference(flattening,[],[f24])).
% 3.31/0.99  
% 3.31/0.99  fof(f62,plain,(
% 3.31/0.99    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.31/0.99    inference(cnf_transformation,[],[f25])).
% 3.31/0.99  
% 3.31/0.99  fof(f11,axiom,(
% 3.31/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.31/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/0.99  
% 3.31/0.99  fof(f26,plain,(
% 3.31/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.31/0.99    inference(ennf_transformation,[],[f11])).
% 3.31/0.99  
% 3.31/0.99  fof(f63,plain,(
% 3.31/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.31/0.99    inference(cnf_transformation,[],[f26])).
% 3.31/0.99  
% 3.31/0.99  fof(f17,axiom,(
% 3.31/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 3.31/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/0.99  
% 3.31/0.99  fof(f35,plain,(
% 3.31/0.99    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.31/0.99    inference(ennf_transformation,[],[f17])).
% 3.31/0.99  
% 3.31/0.99  fof(f36,plain,(
% 3.31/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.31/0.99    inference(flattening,[],[f35])).
% 3.31/0.99  
% 3.31/0.99  fof(f77,plain,(
% 3.31/0.99    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.31/0.99    inference(cnf_transformation,[],[f36])).
% 3.31/0.99  
% 3.31/0.99  fof(f16,axiom,(
% 3.31/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 3.31/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/0.99  
% 3.31/0.99  fof(f33,plain,(
% 3.31/0.99    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.31/0.99    inference(ennf_transformation,[],[f16])).
% 3.31/0.99  
% 3.31/0.99  fof(f34,plain,(
% 3.31/0.99    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.31/0.99    inference(flattening,[],[f33])).
% 3.31/0.99  
% 3.31/0.99  fof(f74,plain,(
% 3.31/0.99    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.31/0.99    inference(cnf_transformation,[],[f34])).
% 3.31/0.99  
% 3.31/0.99  fof(f78,plain,(
% 3.31/0.99    v1_funct_1(sK3)),
% 3.31/0.99    inference(cnf_transformation,[],[f47])).
% 3.31/0.99  
% 3.31/0.99  fof(f15,axiom,(
% 3.31/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 3.31/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/0.99  
% 3.31/0.99  fof(f31,plain,(
% 3.31/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.31/0.99    inference(ennf_transformation,[],[f15])).
% 3.31/0.99  
% 3.31/0.99  fof(f32,plain,(
% 3.31/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.31/0.99    inference(flattening,[],[f31])).
% 3.31/0.99  
% 3.31/0.99  fof(f72,plain,(
% 3.31/0.99    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.31/0.99    inference(cnf_transformation,[],[f32])).
% 3.31/0.99  
% 3.31/0.99  fof(f76,plain,(
% 3.31/0.99    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.31/0.99    inference(cnf_transformation,[],[f36])).
% 3.31/0.99  
% 3.31/0.99  fof(f83,plain,(
% 3.31/0.99    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 3.31/0.99    inference(cnf_transformation,[],[f47])).
% 3.31/0.99  
% 3.31/0.99  fof(f12,axiom,(
% 3.31/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.31/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/0.99  
% 3.31/0.99  fof(f20,plain,(
% 3.31/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.31/0.99    inference(pure_predicate_removal,[],[f12])).
% 3.31/0.99  
% 3.31/0.99  fof(f27,plain,(
% 3.31/0.99    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.31/0.99    inference(ennf_transformation,[],[f20])).
% 3.31/0.99  
% 3.31/0.99  fof(f64,plain,(
% 3.31/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.31/0.99    inference(cnf_transformation,[],[f27])).
% 3.31/0.99  
% 3.31/0.99  fof(f7,axiom,(
% 3.31/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.31/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/0.99  
% 3.31/0.99  fof(f22,plain,(
% 3.31/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.31/0.99    inference(ennf_transformation,[],[f7])).
% 3.31/0.99  
% 3.31/0.99  fof(f44,plain,(
% 3.31/0.99    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.31/0.99    inference(nnf_transformation,[],[f22])).
% 3.31/0.99  
% 3.31/0.99  fof(f58,plain,(
% 3.31/0.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.31/0.99    inference(cnf_transformation,[],[f44])).
% 3.31/0.99  
% 3.31/0.99  fof(f73,plain,(
% 3.31/0.99    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.31/0.99    inference(cnf_transformation,[],[f32])).
% 3.31/0.99  
% 3.31/0.99  fof(f82,plain,(
% 3.31/0.99    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 3.31/0.99    inference(cnf_transformation,[],[f47])).
% 3.31/0.99  
% 3.31/0.99  fof(f3,axiom,(
% 3.31/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.31/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/0.99  
% 3.31/0.99  fof(f41,plain,(
% 3.31/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.31/0.99    inference(nnf_transformation,[],[f3])).
% 3.31/0.99  
% 3.31/0.99  fof(f42,plain,(
% 3.31/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.31/0.99    inference(flattening,[],[f41])).
% 3.31/0.99  
% 3.31/0.99  fof(f53,plain,(
% 3.31/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.31/0.99    inference(cnf_transformation,[],[f42])).
% 3.31/0.99  
% 3.31/0.99  fof(f87,plain,(
% 3.31/0.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.31/0.99    inference(equality_resolution,[],[f53])).
% 3.31/0.99  
% 3.31/0.99  fof(f71,plain,(
% 3.31/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.31/0.99    inference(cnf_transformation,[],[f45])).
% 3.31/0.99  
% 3.31/0.99  fof(f88,plain,(
% 3.31/0.99    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.31/0.99    inference(equality_resolution,[],[f71])).
% 3.31/0.99  
% 3.31/0.99  fof(f89,plain,(
% 3.31/0.99    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.31/0.99    inference(equality_resolution,[],[f88])).
% 3.31/0.99  
% 3.31/0.99  fof(f4,axiom,(
% 3.31/0.99    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.31/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/0.99  
% 3.31/0.99  fof(f55,plain,(
% 3.31/0.99    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.31/0.99    inference(cnf_transformation,[],[f4])).
% 3.31/0.99  
% 3.31/0.99  fof(f52,plain,(
% 3.31/0.99    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.31/0.99    inference(cnf_transformation,[],[f42])).
% 3.31/0.99  
% 3.31/0.99  fof(f1,axiom,(
% 3.31/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.31/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/0.99  
% 3.31/0.99  fof(f39,plain,(
% 3.31/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.31/0.99    inference(nnf_transformation,[],[f1])).
% 3.31/0.99  
% 3.31/0.99  fof(f40,plain,(
% 3.31/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.31/0.99    inference(flattening,[],[f39])).
% 3.31/0.99  
% 3.31/0.99  fof(f50,plain,(
% 3.31/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.31/0.99    inference(cnf_transformation,[],[f40])).
% 3.31/0.99  
% 3.31/0.99  fof(f5,axiom,(
% 3.31/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.31/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/0.99  
% 3.31/0.99  fof(f43,plain,(
% 3.31/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.31/0.99    inference(nnf_transformation,[],[f5])).
% 3.31/0.99  
% 3.31/0.99  fof(f56,plain,(
% 3.31/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.31/0.99    inference(cnf_transformation,[],[f43])).
% 3.31/0.99  
% 3.31/0.99  fof(f54,plain,(
% 3.31/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.31/0.99    inference(cnf_transformation,[],[f42])).
% 3.31/0.99  
% 3.31/0.99  fof(f86,plain,(
% 3.31/0.99    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.31/0.99    inference(equality_resolution,[],[f54])).
% 3.31/0.99  
% 3.31/0.99  fof(f2,axiom,(
% 3.31/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.31/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.31/0.99  
% 3.31/0.99  fof(f51,plain,(
% 3.31/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.31/0.99    inference(cnf_transformation,[],[f2])).
% 3.31/0.99  
% 3.31/0.99  cnf(c_32,negated_conjecture,
% 3.31/0.99      ( r1_tarski(sK2,sK0) ),
% 3.31/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_1633,plain,
% 3.31/0.99      ( r1_tarski(sK2,sK0) = iProver_top ),
% 3.31/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_23,plain,
% 3.31/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.31/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.31/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.31/0.99      | k1_xboole_0 = X2 ),
% 3.31/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_34,negated_conjecture,
% 3.31/0.99      ( v1_funct_2(sK3,sK0,sK1) ),
% 3.31/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_608,plain,
% 3.31/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.31/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.31/0.99      | sK3 != X0
% 3.31/0.99      | sK1 != X2
% 3.31/0.99      | sK0 != X1
% 3.31/0.99      | k1_xboole_0 = X2 ),
% 3.31/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_34]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_609,plain,
% 3.31/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.31/0.99      | k1_relset_1(sK0,sK1,sK3) = sK0
% 3.31/0.99      | k1_xboole_0 = sK1 ),
% 3.31/0.99      inference(unflattening,[status(thm)],[c_608]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_33,negated_conjecture,
% 3.31/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.31/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_611,plain,
% 3.31/0.99      ( k1_relset_1(sK0,sK1,sK3) = sK0 | k1_xboole_0 = sK1 ),
% 3.31/0.99      inference(global_propositional_subsumption,
% 3.31/0.99                [status(thm)],
% 3.31/0.99                [c_609,c_33]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_1632,plain,
% 3.31/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.31/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_17,plain,
% 3.31/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.31/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.31/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_1638,plain,
% 3.31/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.31/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.31/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_3157,plain,
% 3.31/0.99      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 3.31/0.99      inference(superposition,[status(thm)],[c_1632,c_1638]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_3425,plain,
% 3.31/0.99      ( k1_relat_1(sK3) = sK0 | sK1 = k1_xboole_0 ),
% 3.31/0.99      inference(superposition,[status(thm)],[c_611,c_3157]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_14,plain,
% 3.31/0.99      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 3.31/0.99      | ~ v1_relat_1(X1)
% 3.31/0.99      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 3.31/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_1640,plain,
% 3.31/0.99      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 3.31/0.99      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 3.31/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.31/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_3956,plain,
% 3.31/0.99      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 3.31/0.99      | sK1 = k1_xboole_0
% 3.31/0.99      | r1_tarski(X0,sK0) != iProver_top
% 3.31/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.31/0.99      inference(superposition,[status(thm)],[c_3425,c_1640]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_38,plain,
% 3.31/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.31/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_15,plain,
% 3.31/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.31/0.99      | v1_relat_1(X0) ),
% 3.31/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_1911,plain,
% 3.31/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.31/0.99      | v1_relat_1(sK3) ),
% 3.31/0.99      inference(instantiation,[status(thm)],[c_15]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_1912,plain,
% 3.31/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.31/0.99      | v1_relat_1(sK3) = iProver_top ),
% 3.31/0.99      inference(predicate_to_equality,[status(thm)],[c_1911]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_4286,plain,
% 3.31/0.99      ( r1_tarski(X0,sK0) != iProver_top
% 3.31/0.99      | sK1 = k1_xboole_0
% 3.31/0.99      | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
% 3.31/0.99      inference(global_propositional_subsumption,
% 3.31/0.99                [status(thm)],
% 3.31/0.99                [c_3956,c_38,c_1912]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_4287,plain,
% 3.31/0.99      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 3.31/0.99      | sK1 = k1_xboole_0
% 3.31/0.99      | r1_tarski(X0,sK0) != iProver_top ),
% 3.31/0.99      inference(renaming,[status(thm)],[c_4286]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_4297,plain,
% 3.31/0.99      ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2 | sK1 = k1_xboole_0 ),
% 3.31/0.99      inference(superposition,[status(thm)],[c_1633,c_4287]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_27,plain,
% 3.31/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.31/0.99      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.31/0.99      | ~ v1_funct_1(X0)
% 3.31/0.99      | ~ v1_relat_1(X0) ),
% 3.31/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_1634,plain,
% 3.31/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
% 3.31/0.99      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 3.31/0.99      | v1_funct_1(X0) != iProver_top
% 3.31/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.31/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_4563,plain,
% 3.31/0.99      ( sK1 = k1_xboole_0
% 3.31/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 3.31/0.99      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
% 3.31/0.99      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
% 3.31/0.99      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.31/0.99      inference(superposition,[status(thm)],[c_4297,c_1634]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_26,plain,
% 3.31/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.31/0.99      | ~ v1_funct_1(X0)
% 3.31/0.99      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 3.31/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_1635,plain,
% 3.31/0.99      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 3.31/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.31/0.99      | v1_funct_1(X2) != iProver_top ),
% 3.31/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_4876,plain,
% 3.31/0.99      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
% 3.31/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.31/0.99      inference(superposition,[status(thm)],[c_1632,c_1635]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_35,negated_conjecture,
% 3.31/0.99      ( v1_funct_1(sK3) ),
% 3.31/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_1992,plain,
% 3.31/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.31/0.99      | ~ v1_funct_1(sK3)
% 3.31/0.99      | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
% 3.31/0.99      inference(instantiation,[status(thm)],[c_26]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_2079,plain,
% 3.31/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.31/0.99      | ~ v1_funct_1(sK3)
% 3.31/0.99      | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 3.31/0.99      inference(instantiation,[status(thm)],[c_1992]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_5184,plain,
% 3.31/0.99      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 3.31/0.99      inference(global_propositional_subsumption,
% 3.31/0.99                [status(thm)],
% 3.31/0.99                [c_4876,c_35,c_33,c_2079]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_25,plain,
% 3.31/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.31/0.99      | ~ v1_funct_1(X0)
% 3.31/0.99      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
% 3.31/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_1636,plain,
% 3.31/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.31/0.99      | v1_funct_1(X0) != iProver_top
% 3.31/0.99      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
% 3.31/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_3988,plain,
% 3.31/0.99      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
% 3.31/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.31/0.99      inference(superposition,[status(thm)],[c_1632,c_1636]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_36,plain,
% 3.31/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 3.31/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_1965,plain,
% 3.31/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.31/0.99      | v1_funct_1(k2_partfun1(X0,X1,sK3,X2))
% 3.31/0.99      | ~ v1_funct_1(sK3) ),
% 3.31/0.99      inference(instantiation,[status(thm)],[c_25]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_2054,plain,
% 3.31/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.31/0.99      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
% 3.31/0.99      | ~ v1_funct_1(sK3) ),
% 3.31/0.99      inference(instantiation,[status(thm)],[c_1965]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_2055,plain,
% 3.31/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.31/0.99      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
% 3.31/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.31/0.99      inference(predicate_to_equality,[status(thm)],[c_2054]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_4267,plain,
% 3.31/0.99      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
% 3.31/0.99      inference(global_propositional_subsumption,
% 3.31/0.99                [status(thm)],
% 3.31/0.99                [c_3988,c_36,c_38,c_2055]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_5193,plain,
% 3.31/0.99      ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 3.31/0.99      inference(demodulation,[status(thm)],[c_5184,c_4267]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_5476,plain,
% 3.31/0.99      ( sK1 = k1_xboole_0
% 3.31/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 3.31/0.99      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
% 3.31/0.99      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.31/0.99      inference(forward_subsumption_resolution,
% 3.31/0.99                [status(thm)],
% 3.31/0.99                [c_4563,c_5193]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_28,plain,
% 3.31/0.99      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 3.31/0.99      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.31/0.99      | ~ v1_funct_1(X0)
% 3.31/0.99      | ~ v1_relat_1(X0) ),
% 3.31/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_30,negated_conjecture,
% 3.31/0.99      ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
% 3.31/0.99      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.31/0.99      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
% 3.31/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_619,plain,
% 3.31/0.99      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.31/0.99      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.31/0.99      | ~ v1_funct_1(X0)
% 3.31/0.99      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.31/0.99      | ~ v1_relat_1(X0)
% 3.31/0.99      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 3.31/0.99      | k1_relat_1(X0) != sK2
% 3.31/0.99      | sK1 != X1 ),
% 3.31/0.99      inference(resolution_lifted,[status(thm)],[c_28,c_30]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_620,plain,
% 3.31/0.99      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.31/0.99      | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
% 3.31/0.99      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.31/0.99      | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.31/0.99      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
% 3.31/0.99      inference(unflattening,[status(thm)],[c_619]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_16,plain,
% 3.31/0.99      ( v5_relat_1(X0,X1)
% 3.31/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.31/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_11,plain,
% 3.31/0.99      ( ~ v5_relat_1(X0,X1)
% 3.31/0.99      | r1_tarski(k2_relat_1(X0),X1)
% 3.31/0.99      | ~ v1_relat_1(X0) ),
% 3.31/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_407,plain,
% 3.31/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.31/0.99      | r1_tarski(k2_relat_1(X0),X2)
% 3.31/0.99      | ~ v1_relat_1(X0) ),
% 3.31/0.99      inference(resolution,[status(thm)],[c_16,c_11]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_411,plain,
% 3.31/0.99      ( r1_tarski(k2_relat_1(X0),X2)
% 3.31/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.31/0.99      inference(global_propositional_subsumption,
% 3.31/0.99                [status(thm)],
% 3.31/0.99                [c_407,c_15]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_412,plain,
% 3.31/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.31/0.99      | r1_tarski(k2_relat_1(X0),X2) ),
% 3.31/0.99      inference(renaming,[status(thm)],[c_411]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_632,plain,
% 3.31/0.99      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.31/0.99      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.31/0.99      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
% 3.31/0.99      inference(forward_subsumption_resolution,
% 3.31/0.99                [status(thm)],
% 3.31/0.99                [c_620,c_15,c_412]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_1621,plain,
% 3.31/0.99      ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 3.31/0.99      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.31/0.99      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.31/0.99      inference(predicate_to_equality,[status(thm)],[c_632]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_5191,plain,
% 3.31/0.99      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 3.31/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.31/0.99      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.31/0.99      inference(demodulation,[status(thm)],[c_5184,c_1621]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_5207,plain,
% 3.31/0.99      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 3.31/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.31/0.99      inference(forward_subsumption_resolution,
% 3.31/0.99                [status(thm)],
% 3.31/0.99                [c_5191,c_5193]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_5612,plain,
% 3.31/0.99      ( sK1 = k1_xboole_0
% 3.31/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.31/0.99      inference(superposition,[status(thm)],[c_4297,c_5207]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_6043,plain,
% 3.31/0.99      ( sK1 = k1_xboole_0
% 3.31/0.99      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
% 3.31/0.99      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.31/0.99      inference(superposition,[status(thm)],[c_5476,c_5612]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_24,plain,
% 3.31/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.31/0.99      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.31/0.99      | ~ v1_funct_1(X0) ),
% 3.31/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_1637,plain,
% 3.31/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.31/0.99      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 3.31/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.31/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_5668,plain,
% 3.31/0.99      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 3.31/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.31/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.31/0.99      inference(superposition,[status(thm)],[c_5184,c_1637]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_6134,plain,
% 3.31/0.99      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.31/0.99      inference(global_propositional_subsumption,
% 3.31/0.99                [status(thm)],
% 3.31/0.99                [c_5668,c_36,c_38]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_1639,plain,
% 3.31/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.31/0.99      | v1_relat_1(X0) = iProver_top ),
% 3.31/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_6146,plain,
% 3.31/0.99      ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 3.31/0.99      inference(superposition,[status(thm)],[c_6134,c_1639]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_1630,plain,
% 3.31/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.31/0.99      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 3.31/0.99      inference(predicate_to_equality,[status(thm)],[c_412]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_6145,plain,
% 3.31/0.99      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) = iProver_top ),
% 3.31/0.99      inference(superposition,[status(thm)],[c_6134,c_1630]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_7194,plain,
% 3.31/0.99      ( sK1 = k1_xboole_0 ),
% 3.31/0.99      inference(forward_subsumption_resolution,
% 3.31/0.99                [status(thm)],
% 3.31/0.99                [c_6043,c_6146,c_6145]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_7201,plain,
% 3.31/0.99      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
% 3.31/0.99      inference(demodulation,[status(thm)],[c_7194,c_6134]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_31,negated_conjecture,
% 3.31/0.99      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 3.31/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_7218,plain,
% 3.31/0.99      ( sK0 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.31/0.99      inference(demodulation,[status(thm)],[c_7194,c_31]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_7219,plain,
% 3.31/0.99      ( sK0 = k1_xboole_0 ),
% 3.31/0.99      inference(equality_resolution_simp,[status(thm)],[c_7218]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_7277,plain,
% 3.31/0.99      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.31/0.99      inference(light_normalisation,[status(thm)],[c_7201,c_7219]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_5,plain,
% 3.31/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.31/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_7279,plain,
% 3.31/0.99      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.31/0.99      inference(demodulation,[status(thm)],[c_7277,c_5]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_18,plain,
% 3.31/0.99      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
% 3.31/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 3.31/0.99      | k1_xboole_0 = X0 ),
% 3.31/0.99      inference(cnf_transformation,[],[f89]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_436,plain,
% 3.31/0.99      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.31/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 3.31/0.99      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.31/0.99      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 3.31/0.99      | sK2 != X0
% 3.31/0.99      | sK1 != k1_xboole_0
% 3.31/0.99      | k1_xboole_0 = X0 ),
% 3.31/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_30]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_437,plain,
% 3.31/0.99      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.31/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
% 3.31/0.99      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.31/0.99      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 3.31/0.99      | sK1 != k1_xboole_0
% 3.31/0.99      | k1_xboole_0 = sK2 ),
% 3.31/0.99      inference(unflattening,[status(thm)],[c_436]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_7,plain,
% 3.31/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.31/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_451,plain,
% 3.31/0.99      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.31/0.99      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.31/0.99      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 3.31/0.99      | sK1 != k1_xboole_0
% 3.31/0.99      | k1_xboole_0 = sK2 ),
% 3.31/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_437,c_7]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_1629,plain,
% 3.31/0.99      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 3.31/0.99      | sK1 != k1_xboole_0
% 3.31/0.99      | k1_xboole_0 = sK2
% 3.31/0.99      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.31/0.99      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.31/0.99      inference(predicate_to_equality,[status(thm)],[c_451]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_457,plain,
% 3.31/0.99      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 3.31/0.99      | sK1 != k1_xboole_0
% 3.31/0.99      | k1_xboole_0 = sK2
% 3.31/0.99      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.31/0.99      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.31/0.99      inference(predicate_to_equality,[status(thm)],[c_451]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_2166,plain,
% 3.31/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.31/0.99      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.31/0.99      | ~ v1_funct_1(sK3) ),
% 3.31/0.99      inference(instantiation,[status(thm)],[c_2054]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_2167,plain,
% 3.31/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.31/0.99      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) = iProver_top
% 3.31/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.31/0.99      inference(predicate_to_equality,[status(thm)],[c_2166]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_2216,plain,
% 3.31/0.99      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.31/0.99      | k1_xboole_0 = sK2
% 3.31/0.99      | sK1 != k1_xboole_0
% 3.31/0.99      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0 ),
% 3.31/0.99      inference(global_propositional_subsumption,
% 3.31/0.99                [status(thm)],
% 3.31/0.99                [c_1629,c_36,c_38,c_457,c_2167]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_2217,plain,
% 3.31/0.99      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 3.31/0.99      | sK1 != k1_xboole_0
% 3.31/0.99      | k1_xboole_0 = sK2
% 3.31/0.99      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.31/0.99      inference(renaming,[status(thm)],[c_2216]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_5189,plain,
% 3.31/0.99      ( k7_relat_1(sK3,sK2) != k1_xboole_0
% 3.31/0.99      | sK2 = k1_xboole_0
% 3.31/0.99      | sK1 != k1_xboole_0
% 3.31/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.31/0.99      inference(demodulation,[status(thm)],[c_5184,c_2217]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_6,plain,
% 3.31/0.99      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.31/0.99      | k1_xboole_0 = X1
% 3.31/0.99      | k1_xboole_0 = X0 ),
% 3.31/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_106,plain,
% 3.31/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.31/0.99      | k1_xboole_0 = k1_xboole_0 ),
% 3.31/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_107,plain,
% 3.31/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.31/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_0,plain,
% 3.31/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.31/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_1935,plain,
% 3.31/0.99      ( ~ r1_tarski(sK2,k1_xboole_0)
% 3.31/0.99      | ~ r1_tarski(k1_xboole_0,sK2)
% 3.31/0.99      | sK2 = k1_xboole_0 ),
% 3.31/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_965,plain,( X0 = X0 ),theory(equality) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_2112,plain,
% 3.31/0.99      ( sK2 = sK2 ),
% 3.31/0.99      inference(instantiation,[status(thm)],[c_965]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_9,plain,
% 3.31/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.31/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_2382,plain,
% 3.31/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2)) | r1_tarski(X0,sK2) ),
% 3.31/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_2384,plain,
% 3.31/0.99      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2))
% 3.31/0.99      | r1_tarski(k1_xboole_0,sK2) ),
% 3.31/0.99      inference(instantiation,[status(thm)],[c_2382]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_966,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_2852,plain,
% 3.31/0.99      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 3.31/0.99      inference(instantiation,[status(thm)],[c_966]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_2853,plain,
% 3.31/0.99      ( sK1 != k1_xboole_0
% 3.31/0.99      | k1_xboole_0 = sK1
% 3.31/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.31/0.99      inference(instantiation,[status(thm)],[c_2852]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_3313,plain,
% 3.31/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2)) ),
% 3.31/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_967,plain,
% 3.31/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.31/0.99      theory(equality) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_2093,plain,
% 3.31/0.99      ( ~ r1_tarski(X0,X1)
% 3.31/0.99      | r1_tarski(sK2,k1_xboole_0)
% 3.31/0.99      | sK2 != X0
% 3.31/0.99      | k1_xboole_0 != X1 ),
% 3.31/0.99      inference(instantiation,[status(thm)],[c_967]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_2398,plain,
% 3.31/0.99      ( ~ r1_tarski(sK2,X0)
% 3.31/0.99      | r1_tarski(sK2,k1_xboole_0)
% 3.31/0.99      | sK2 != sK2
% 3.31/0.99      | k1_xboole_0 != X0 ),
% 3.31/0.99      inference(instantiation,[status(thm)],[c_2093]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_3340,plain,
% 3.31/0.99      ( ~ r1_tarski(sK2,sK0)
% 3.31/0.99      | r1_tarski(sK2,k1_xboole_0)
% 3.31/0.99      | sK2 != sK2
% 3.31/0.99      | k1_xboole_0 != sK0 ),
% 3.31/0.99      inference(instantiation,[status(thm)],[c_2398]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_5328,plain,
% 3.31/0.99      ( sK2 = k1_xboole_0
% 3.31/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.31/0.99      inference(global_propositional_subsumption,
% 3.31/0.99                [status(thm)],
% 3.31/0.99                [c_5189,c_32,c_31,c_106,c_107,c_1935,c_2112,c_2384,
% 3.31/0.99                 c_2853,c_3313,c_3340,c_4297,c_5207]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_7205,plain,
% 3.31/0.99      ( sK2 = k1_xboole_0
% 3.31/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
% 3.31/0.99      inference(demodulation,[status(thm)],[c_7194,c_5328]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_4,plain,
% 3.31/0.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.31/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_7258,plain,
% 3.31/0.99      ( sK2 = k1_xboole_0
% 3.31/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.31/0.99      inference(demodulation,[status(thm)],[c_7205,c_4]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_7281,plain,
% 3.31/0.99      ( sK2 = k1_xboole_0 ),
% 3.31/0.99      inference(backward_subsumption_resolution,
% 3.31/0.99                [status(thm)],
% 3.31/0.99                [c_7279,c_7258]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_7202,plain,
% 3.31/0.99      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 3.31/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
% 3.31/0.99      inference(demodulation,[status(thm)],[c_7194,c_5207]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_7274,plain,
% 3.31/0.99      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 3.31/0.99      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.31/0.99      inference(demodulation,[status(thm)],[c_7202,c_4]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_7282,plain,
% 3.31/0.99      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2 ),
% 3.31/0.99      inference(backward_subsumption_resolution,
% 3.31/0.99                [status(thm)],
% 3.31/0.99                [c_7279,c_7274]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_7289,plain,
% 3.31/0.99      ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0 ),
% 3.31/0.99      inference(demodulation,[status(thm)],[c_7281,c_7282]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_3,plain,
% 3.31/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 3.31/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_2262,plain,
% 3.31/0.99      ( r1_tarski(k1_xboole_0,k1_relat_1(sK3)) ),
% 3.31/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_1997,plain,
% 3.31/0.99      ( ~ r1_tarski(X0,k1_relat_1(sK3))
% 3.31/0.99      | ~ v1_relat_1(sK3)
% 3.31/0.99      | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
% 3.31/0.99      inference(instantiation,[status(thm)],[c_14]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_1999,plain,
% 3.31/0.99      ( ~ r1_tarski(k1_xboole_0,k1_relat_1(sK3))
% 3.31/0.99      | ~ v1_relat_1(sK3)
% 3.31/0.99      | k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
% 3.31/0.99      inference(instantiation,[status(thm)],[c_1997]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(contradiction,plain,
% 3.31/0.99      ( $false ),
% 3.31/0.99      inference(minisat,[status(thm)],[c_7289,c_2262,c_1999,c_1911,c_33]) ).
% 3.31/0.99  
% 3.31/0.99  
% 3.31/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.31/0.99  
% 3.31/0.99  ------                               Statistics
% 3.31/0.99  
% 3.31/0.99  ------ General
% 3.31/0.99  
% 3.31/0.99  abstr_ref_over_cycles:                  0
% 3.31/0.99  abstr_ref_under_cycles:                 0
% 3.31/0.99  gc_basic_clause_elim:                   0
% 3.31/0.99  forced_gc_time:                         0
% 3.31/0.99  parsing_time:                           0.016
% 3.31/0.99  unif_index_cands_time:                  0.
% 3.31/0.99  unif_index_add_time:                    0.
% 3.31/0.99  orderings_time:                         0.
% 3.31/0.99  out_proof_time:                         0.012
% 3.31/0.99  total_time:                             0.247
% 3.31/0.99  num_of_symbols:                         49
% 3.31/0.99  num_of_terms:                           6589
% 3.31/0.99  
% 3.31/0.99  ------ Preprocessing
% 3.31/0.99  
% 3.31/0.99  num_of_splits:                          0
% 3.31/0.99  num_of_split_atoms:                     0
% 3.31/0.99  num_of_reused_defs:                     0
% 3.31/0.99  num_eq_ax_congr_red:                    10
% 3.31/0.99  num_of_sem_filtered_clauses:            1
% 3.31/0.99  num_of_subtypes:                        0
% 3.31/0.99  monotx_restored_types:                  0
% 3.31/0.99  sat_num_of_epr_types:                   0
% 3.31/0.99  sat_num_of_non_cyclic_types:            0
% 3.31/0.99  sat_guarded_non_collapsed_types:        0
% 3.31/0.99  num_pure_diseq_elim:                    0
% 3.31/0.99  simp_replaced_by:                       0
% 3.31/0.99  res_preprocessed:                       161
% 3.31/0.99  prep_upred:                             0
% 3.31/0.99  prep_unflattend:                        43
% 3.31/0.99  smt_new_axioms:                         0
% 3.31/0.99  pred_elim_cands:                        4
% 3.31/0.99  pred_elim:                              2
% 3.31/0.99  pred_elim_cl:                           0
% 3.31/0.99  pred_elim_cycles:                       4
% 3.31/0.99  merged_defs:                            8
% 3.31/0.99  merged_defs_ncl:                        0
% 3.31/0.99  bin_hyper_res:                          8
% 3.31/0.99  prep_cycles:                            4
% 3.31/0.99  pred_elim_time:                         0.009
% 3.31/0.99  splitting_time:                         0.
% 3.31/0.99  sem_filter_time:                        0.
% 3.31/0.99  monotx_time:                            0.
% 3.31/0.99  subtype_inf_time:                       0.
% 3.31/0.99  
% 3.31/0.99  ------ Problem properties
% 3.31/0.99  
% 3.31/0.99  clauses:                                34
% 3.31/0.99  conjectures:                            4
% 3.31/0.99  epr:                                    6
% 3.31/0.99  horn:                                   29
% 3.31/0.99  ground:                                 12
% 3.31/0.99  unary:                                  9
% 3.31/0.99  binary:                                 8
% 3.31/0.99  lits:                                   89
% 3.31/0.99  lits_eq:                                35
% 3.31/0.99  fd_pure:                                0
% 3.31/0.99  fd_pseudo:                              0
% 3.31/0.99  fd_cond:                                3
% 3.31/0.99  fd_pseudo_cond:                         1
% 3.31/0.99  ac_symbols:                             0
% 3.31/0.99  
% 3.31/0.99  ------ Propositional Solver
% 3.31/0.99  
% 3.31/0.99  prop_solver_calls:                      27
% 3.31/0.99  prop_fast_solver_calls:                 1167
% 3.31/0.99  smt_solver_calls:                       0
% 3.31/0.99  smt_fast_solver_calls:                  0
% 3.31/0.99  prop_num_of_clauses:                    2770
% 3.31/0.99  prop_preprocess_simplified:             7395
% 3.31/0.99  prop_fo_subsumed:                       20
% 3.31/0.99  prop_solver_time:                       0.
% 3.31/0.99  smt_solver_time:                        0.
% 3.31/0.99  smt_fast_solver_time:                   0.
% 3.31/0.99  prop_fast_solver_time:                  0.
% 3.31/0.99  prop_unsat_core_time:                   0.
% 3.31/0.99  
% 3.31/0.99  ------ QBF
% 3.31/0.99  
% 3.31/0.99  qbf_q_res:                              0
% 3.31/0.99  qbf_num_tautologies:                    0
% 3.31/0.99  qbf_prep_cycles:                        0
% 3.31/0.99  
% 3.31/0.99  ------ BMC1
% 3.31/0.99  
% 3.31/0.99  bmc1_current_bound:                     -1
% 3.31/0.99  bmc1_last_solved_bound:                 -1
% 3.31/0.99  bmc1_unsat_core_size:                   -1
% 3.31/0.99  bmc1_unsat_core_parents_size:           -1
% 3.31/0.99  bmc1_merge_next_fun:                    0
% 3.31/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.31/0.99  
% 3.31/0.99  ------ Instantiation
% 3.31/0.99  
% 3.31/0.99  inst_num_of_clauses:                    770
% 3.31/0.99  inst_num_in_passive:                    25
% 3.31/0.99  inst_num_in_active:                     363
% 3.31/0.99  inst_num_in_unprocessed:                383
% 3.31/0.99  inst_num_of_loops:                      440
% 3.31/0.99  inst_num_of_learning_restarts:          0
% 3.31/0.99  inst_num_moves_active_passive:          75
% 3.31/0.99  inst_lit_activity:                      0
% 3.31/0.99  inst_lit_activity_moves:                0
% 3.31/0.99  inst_num_tautologies:                   0
% 3.31/0.99  inst_num_prop_implied:                  0
% 3.31/0.99  inst_num_existing_simplified:           0
% 3.31/0.99  inst_num_eq_res_simplified:             0
% 3.31/0.99  inst_num_child_elim:                    0
% 3.31/0.99  inst_num_of_dismatching_blockings:      225
% 3.31/0.99  inst_num_of_non_proper_insts:           684
% 3.31/0.99  inst_num_of_duplicates:                 0
% 3.31/0.99  inst_inst_num_from_inst_to_res:         0
% 3.31/0.99  inst_dismatching_checking_time:         0.
% 3.31/0.99  
% 3.31/0.99  ------ Resolution
% 3.31/0.99  
% 3.31/0.99  res_num_of_clauses:                     0
% 3.31/0.99  res_num_in_passive:                     0
% 3.31/0.99  res_num_in_active:                      0
% 3.31/0.99  res_num_of_loops:                       165
% 3.31/0.99  res_forward_subset_subsumed:            28
% 3.31/0.99  res_backward_subset_subsumed:           2
% 3.31/0.99  res_forward_subsumed:                   0
% 3.31/0.99  res_backward_subsumed:                  0
% 3.31/0.99  res_forward_subsumption_resolution:     6
% 3.31/0.99  res_backward_subsumption_resolution:    0
% 3.31/0.99  res_clause_to_clause_subsumption:       467
% 3.31/0.99  res_orphan_elimination:                 0
% 3.31/0.99  res_tautology_del:                      45
% 3.31/0.99  res_num_eq_res_simplified:              1
% 3.31/0.99  res_num_sel_changes:                    0
% 3.31/0.99  res_moves_from_active_to_pass:          0
% 3.31/0.99  
% 3.31/0.99  ------ Superposition
% 3.31/0.99  
% 3.31/0.99  sup_time_total:                         0.
% 3.31/0.99  sup_time_generating:                    0.
% 3.31/0.99  sup_time_sim_full:                      0.
% 3.31/0.99  sup_time_sim_immed:                     0.
% 3.31/0.99  
% 3.31/0.99  sup_num_of_clauses:                     125
% 3.31/0.99  sup_num_in_active:                      49
% 3.31/0.99  sup_num_in_passive:                     76
% 3.31/0.99  sup_num_of_loops:                       87
% 3.31/0.99  sup_fw_superposition:                   84
% 3.31/0.99  sup_bw_superposition:                   64
% 3.31/0.99  sup_immediate_simplified:               39
% 3.31/0.99  sup_given_eliminated:                   1
% 3.31/0.99  comparisons_done:                       0
% 3.31/0.99  comparisons_avoided:                    16
% 3.31/0.99  
% 3.31/0.99  ------ Simplifications
% 3.31/0.99  
% 3.31/0.99  
% 3.31/0.99  sim_fw_subset_subsumed:                 3
% 3.31/0.99  sim_bw_subset_subsumed:                 15
% 3.31/0.99  sim_fw_subsumed:                        6
% 3.31/0.99  sim_bw_subsumed:                        0
% 3.31/0.99  sim_fw_subsumption_res:                 9
% 3.31/0.99  sim_bw_subsumption_res:                 3
% 3.31/0.99  sim_tautology_del:                      7
% 3.31/0.99  sim_eq_tautology_del:                   10
% 3.31/0.99  sim_eq_res_simp:                        3
% 3.31/0.99  sim_fw_demodulated:                     18
% 3.31/0.99  sim_bw_demodulated:                     35
% 3.31/0.99  sim_light_normalised:                   12
% 3.31/0.99  sim_joinable_taut:                      0
% 3.31/0.99  sim_joinable_simp:                      0
% 3.31/0.99  sim_ac_normalised:                      0
% 3.31/0.99  sim_smt_subsumption:                    0
% 3.31/0.99  
%------------------------------------------------------------------------------
