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
% DateTime   : Thu Dec  3 12:03:46 EST 2020

% Result     : Theorem 3.71s
% Output     : CNFRefutation 3.71s
% Verified   : 
% Statistics : Number of formulae       :  198 (2271 expanded)
%              Number of clauses        :  121 ( 774 expanded)
%              Number of leaves         :   25 ( 426 expanded)
%              Depth                    :   28
%              Number of atoms          :  545 (12018 expanded)
%              Number of equality atoms :  246 (3094 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f23,conjecture,(
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

fof(f24,negated_conjecture,(
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
    inference(negated_conjecture,[],[f23])).

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
    inference(ennf_transformation,[],[f24])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f49,f52])).

fof(f89,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f19,axiom,(
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
    inference(ennf_transformation,[],[f19])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

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
    inference(nnf_transformation,[],[f41])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f87,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f88,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f53])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f46])).

fof(f85,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f44])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f86,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f42])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f84,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f91,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f53])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f59,plain,(
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
    inference(cnf_transformation,[],[f43])).

fof(f9,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f66,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f90,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f53])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f28])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f55,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

cnf(c_34,negated_conjecture,
    ( r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2045,plain,
    ( r1_tarski(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_36,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_754,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X0
    | sK1 != X2
    | sK0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_36])).

cnf(c_755,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_754])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_757,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_755,c_35])).

cnf(c_2044,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2050,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3364,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2044,c_2050])).

cnf(c_3548,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_757,c_3364])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2057,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4067,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3548,c_2057])).

cnf(c_40,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2330,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2331,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2330])).

cnf(c_4547,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | sK1 = k1_xboole_0
    | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4067,c_40,c_2331])).

cnf(c_4548,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4547])).

cnf(c_4556,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2045,c_4548])).

cnf(c_29,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2046,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_4955,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4556,c_2046])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2446,plain,
    ( v1_relat_1(k7_relat_1(sK3,X0))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_5641,plain,
    ( v1_relat_1(k7_relat_1(sK3,sK2))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2446])).

cnf(c_5642,plain,
    ( v1_relat_1(k7_relat_1(sK3,sK2)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5641])).

cnf(c_5715,plain,
    ( v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4955,c_40,c_2331,c_5642])).

cnf(c_5716,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5715])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2047,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_5044,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2044,c_2047])).

cnf(c_37,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2428,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_5313,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5044,c_37,c_35,c_2428])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2048,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_4291,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2044,c_2048])).

cnf(c_38,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_2399,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_2400,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2399])).

cnf(c_4501,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4291,c_38,c_40,c_2400])).

cnf(c_5322,plain,
    ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5313,c_4501])).

cnf(c_5725,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5716,c_5322])).

cnf(c_30,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_32,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_765,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_relat_1(X0)
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_relat_1(X0) != sK2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_32])).

cnf(c_766,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
    inference(unflattening,[status(thm)],[c_765])).

cnf(c_17,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_6,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_395,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_17,c_6])).

cnf(c_399,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_395,c_16])).

cnf(c_400,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_399])).

cnf(c_778,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_766,c_16,c_400])).

cnf(c_2032,plain,
    ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_778])).

cnf(c_782,plain,
    ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_778])).

cnf(c_2468,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2399])).

cnf(c_2469,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2468])).

cnf(c_2625,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2032,c_38,c_40,c_782,c_2469])).

cnf(c_2626,plain,
    ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2625])).

cnf(c_5318,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5313,c_2626])).

cnf(c_5452,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4556,c_5318])).

cnf(c_5736,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5725,c_5452])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2049,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_5371,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5313,c_2049])).

cnf(c_5531,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5371,c_38,c_40])).

cnf(c_2041,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_400])).

cnf(c_5544,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_5531,c_2041])).

cnf(c_6268,plain,
    ( sK1 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5736,c_5544])).

cnf(c_6273,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6268,c_5318])).

cnf(c_9,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_10,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_15,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2053,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2729,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_10,c_2053])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2056,plain,
    ( k7_relat_1(X0,k1_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2952,plain,
    ( k7_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2729,c_2056])).

cnf(c_2954,plain,
    ( k7_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2952,c_9])).

cnf(c_33,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_6285,plain,
    ( sK0 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6268,c_33])).

cnf(c_6286,plain,
    ( sK0 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_6285])).

cnf(c_6417,plain,
    ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6286,c_2045])).

cnf(c_2,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_xboole_0(X0,X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_382,plain,
    ( ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_3])).

cnf(c_383,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_382])).

cnf(c_2042,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_383])).

cnf(c_6436,plain,
    ( v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_6417,c_2042])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2060,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_7015,plain,
    ( sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6436,c_2060])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2051,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3407,plain,
    ( v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2044,c_2051])).

cnf(c_6416,plain,
    ( v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6286,c_3407])).

cnf(c_121,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_123,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1487,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2371,plain,
    ( sK0 != X0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1487])).

cnf(c_2514,plain,
    ( sK0 != sK0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_2371])).

cnf(c_1486,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2515,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1486])).

cnf(c_2687,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1487])).

cnf(c_2688,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2687])).

cnf(c_1488,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2987,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK0)
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_1488])).

cnf(c_2988,plain,
    ( sK0 != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2987])).

cnf(c_2990,plain,
    ( sK0 != k1_xboole_0
    | v1_xboole_0(sK0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2988])).

cnf(c_7343,plain,
    ( v1_xboole_0(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6416,c_33,c_121,c_0,c_123,c_2514,c_2515,c_2688,c_2990,c_3407,c_6268])).

cnf(c_7349,plain,
    ( sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7343,c_2060])).

cnf(c_8214,plain,
    ( k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6273,c_9,c_2954,c_7015,c_7349])).

cnf(c_8215,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_8214])).

cnf(c_4,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2059,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_8217,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8215,c_2059])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:41:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.71/1.04  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.71/1.04  
% 3.71/1.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.71/1.04  
% 3.71/1.04  ------  iProver source info
% 3.71/1.04  
% 3.71/1.04  git: date: 2020-06-30 10:37:57 +0100
% 3.71/1.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.71/1.04  git: non_committed_changes: false
% 3.71/1.04  git: last_make_outside_of_git: false
% 3.71/1.04  
% 3.71/1.04  ------ 
% 3.71/1.04  
% 3.71/1.04  ------ Input Options
% 3.71/1.04  
% 3.71/1.04  --out_options                           all
% 3.71/1.04  --tptp_safe_out                         true
% 3.71/1.04  --problem_path                          ""
% 3.71/1.04  --include_path                          ""
% 3.71/1.04  --clausifier                            res/vclausify_rel
% 3.71/1.04  --clausifier_options                    --mode clausify
% 3.71/1.04  --stdin                                 false
% 3.71/1.04  --stats_out                             all
% 3.71/1.04  
% 3.71/1.04  ------ General Options
% 3.71/1.04  
% 3.71/1.04  --fof                                   false
% 3.71/1.04  --time_out_real                         305.
% 3.71/1.04  --time_out_virtual                      -1.
% 3.71/1.04  --symbol_type_check                     false
% 3.71/1.04  --clausify_out                          false
% 3.71/1.04  --sig_cnt_out                           false
% 3.71/1.04  --trig_cnt_out                          false
% 3.71/1.04  --trig_cnt_out_tolerance                1.
% 3.71/1.04  --trig_cnt_out_sk_spl                   false
% 3.71/1.04  --abstr_cl_out                          false
% 3.71/1.04  
% 3.71/1.04  ------ Global Options
% 3.71/1.04  
% 3.71/1.04  --schedule                              default
% 3.71/1.04  --add_important_lit                     false
% 3.71/1.04  --prop_solver_per_cl                    1000
% 3.71/1.04  --min_unsat_core                        false
% 3.71/1.04  --soft_assumptions                      false
% 3.71/1.04  --soft_lemma_size                       3
% 3.71/1.04  --prop_impl_unit_size                   0
% 3.71/1.04  --prop_impl_unit                        []
% 3.71/1.04  --share_sel_clauses                     true
% 3.71/1.04  --reset_solvers                         false
% 3.71/1.04  --bc_imp_inh                            [conj_cone]
% 3.71/1.04  --conj_cone_tolerance                   3.
% 3.71/1.04  --extra_neg_conj                        none
% 3.71/1.04  --large_theory_mode                     true
% 3.71/1.04  --prolific_symb_bound                   200
% 3.71/1.04  --lt_threshold                          2000
% 3.71/1.04  --clause_weak_htbl                      true
% 3.71/1.04  --gc_record_bc_elim                     false
% 3.71/1.04  
% 3.71/1.04  ------ Preprocessing Options
% 3.71/1.04  
% 3.71/1.04  --preprocessing_flag                    true
% 3.71/1.04  --time_out_prep_mult                    0.1
% 3.71/1.04  --splitting_mode                        input
% 3.71/1.04  --splitting_grd                         true
% 3.71/1.04  --splitting_cvd                         false
% 3.71/1.04  --splitting_cvd_svl                     false
% 3.71/1.04  --splitting_nvd                         32
% 3.71/1.04  --sub_typing                            true
% 3.71/1.04  --prep_gs_sim                           true
% 3.71/1.04  --prep_unflatten                        true
% 3.71/1.04  --prep_res_sim                          true
% 3.71/1.04  --prep_upred                            true
% 3.71/1.04  --prep_sem_filter                       exhaustive
% 3.71/1.04  --prep_sem_filter_out                   false
% 3.71/1.04  --pred_elim                             true
% 3.71/1.04  --res_sim_input                         true
% 3.71/1.04  --eq_ax_congr_red                       true
% 3.71/1.04  --pure_diseq_elim                       true
% 3.71/1.04  --brand_transform                       false
% 3.71/1.04  --non_eq_to_eq                          false
% 3.71/1.04  --prep_def_merge                        true
% 3.71/1.04  --prep_def_merge_prop_impl              false
% 3.71/1.04  --prep_def_merge_mbd                    true
% 3.71/1.04  --prep_def_merge_tr_red                 false
% 3.71/1.04  --prep_def_merge_tr_cl                  false
% 3.71/1.04  --smt_preprocessing                     true
% 3.71/1.04  --smt_ac_axioms                         fast
% 3.71/1.04  --preprocessed_out                      false
% 3.71/1.04  --preprocessed_stats                    false
% 3.71/1.04  
% 3.71/1.04  ------ Abstraction refinement Options
% 3.71/1.04  
% 3.71/1.04  --abstr_ref                             []
% 3.71/1.04  --abstr_ref_prep                        false
% 3.71/1.04  --abstr_ref_until_sat                   false
% 3.71/1.04  --abstr_ref_sig_restrict                funpre
% 3.71/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 3.71/1.04  --abstr_ref_under                       []
% 3.71/1.04  
% 3.71/1.04  ------ SAT Options
% 3.71/1.04  
% 3.71/1.04  --sat_mode                              false
% 3.71/1.04  --sat_fm_restart_options                ""
% 3.71/1.04  --sat_gr_def                            false
% 3.71/1.04  --sat_epr_types                         true
% 3.71/1.04  --sat_non_cyclic_types                  false
% 3.71/1.04  --sat_finite_models                     false
% 3.71/1.04  --sat_fm_lemmas                         false
% 3.71/1.04  --sat_fm_prep                           false
% 3.71/1.04  --sat_fm_uc_incr                        true
% 3.71/1.04  --sat_out_model                         small
% 3.71/1.04  --sat_out_clauses                       false
% 3.71/1.04  
% 3.71/1.04  ------ QBF Options
% 3.71/1.04  
% 3.71/1.04  --qbf_mode                              false
% 3.71/1.04  --qbf_elim_univ                         false
% 3.71/1.04  --qbf_dom_inst                          none
% 3.71/1.04  --qbf_dom_pre_inst                      false
% 3.71/1.04  --qbf_sk_in                             false
% 3.71/1.04  --qbf_pred_elim                         true
% 3.71/1.04  --qbf_split                             512
% 3.71/1.04  
% 3.71/1.04  ------ BMC1 Options
% 3.71/1.04  
% 3.71/1.04  --bmc1_incremental                      false
% 3.71/1.04  --bmc1_axioms                           reachable_all
% 3.71/1.04  --bmc1_min_bound                        0
% 3.71/1.04  --bmc1_max_bound                        -1
% 3.71/1.04  --bmc1_max_bound_default                -1
% 3.71/1.04  --bmc1_symbol_reachability              true
% 3.71/1.04  --bmc1_property_lemmas                  false
% 3.71/1.04  --bmc1_k_induction                      false
% 3.71/1.04  --bmc1_non_equiv_states                 false
% 3.71/1.04  --bmc1_deadlock                         false
% 3.71/1.04  --bmc1_ucm                              false
% 3.71/1.04  --bmc1_add_unsat_core                   none
% 3.71/1.04  --bmc1_unsat_core_children              false
% 3.71/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 3.71/1.04  --bmc1_out_stat                         full
% 3.71/1.04  --bmc1_ground_init                      false
% 3.71/1.04  --bmc1_pre_inst_next_state              false
% 3.71/1.04  --bmc1_pre_inst_state                   false
% 3.71/1.04  --bmc1_pre_inst_reach_state             false
% 3.71/1.04  --bmc1_out_unsat_core                   false
% 3.71/1.04  --bmc1_aig_witness_out                  false
% 3.71/1.04  --bmc1_verbose                          false
% 3.71/1.04  --bmc1_dump_clauses_tptp                false
% 3.71/1.04  --bmc1_dump_unsat_core_tptp             false
% 3.71/1.04  --bmc1_dump_file                        -
% 3.71/1.04  --bmc1_ucm_expand_uc_limit              128
% 3.71/1.04  --bmc1_ucm_n_expand_iterations          6
% 3.71/1.04  --bmc1_ucm_extend_mode                  1
% 3.71/1.04  --bmc1_ucm_init_mode                    2
% 3.71/1.04  --bmc1_ucm_cone_mode                    none
% 3.71/1.04  --bmc1_ucm_reduced_relation_type        0
% 3.71/1.04  --bmc1_ucm_relax_model                  4
% 3.71/1.04  --bmc1_ucm_full_tr_after_sat            true
% 3.71/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 3.71/1.04  --bmc1_ucm_layered_model                none
% 3.71/1.04  --bmc1_ucm_max_lemma_size               10
% 3.71/1.04  
% 3.71/1.04  ------ AIG Options
% 3.71/1.04  
% 3.71/1.04  --aig_mode                              false
% 3.71/1.04  
% 3.71/1.04  ------ Instantiation Options
% 3.71/1.04  
% 3.71/1.04  --instantiation_flag                    true
% 3.71/1.04  --inst_sos_flag                         false
% 3.71/1.04  --inst_sos_phase                        true
% 3.71/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.71/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.71/1.04  --inst_lit_sel_side                     num_symb
% 3.71/1.04  --inst_solver_per_active                1400
% 3.71/1.04  --inst_solver_calls_frac                1.
% 3.71/1.04  --inst_passive_queue_type               priority_queues
% 3.71/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.71/1.04  --inst_passive_queues_freq              [25;2]
% 3.71/1.04  --inst_dismatching                      true
% 3.71/1.04  --inst_eager_unprocessed_to_passive     true
% 3.71/1.04  --inst_prop_sim_given                   true
% 3.71/1.04  --inst_prop_sim_new                     false
% 3.71/1.04  --inst_subs_new                         false
% 3.71/1.04  --inst_eq_res_simp                      false
% 3.71/1.04  --inst_subs_given                       false
% 3.71/1.04  --inst_orphan_elimination               true
% 3.71/1.04  --inst_learning_loop_flag               true
% 3.71/1.04  --inst_learning_start                   3000
% 3.71/1.04  --inst_learning_factor                  2
% 3.71/1.04  --inst_start_prop_sim_after_learn       3
% 3.71/1.04  --inst_sel_renew                        solver
% 3.71/1.04  --inst_lit_activity_flag                true
% 3.71/1.04  --inst_restr_to_given                   false
% 3.71/1.04  --inst_activity_threshold               500
% 3.71/1.04  --inst_out_proof                        true
% 3.71/1.04  
% 3.71/1.04  ------ Resolution Options
% 3.71/1.04  
% 3.71/1.04  --resolution_flag                       true
% 3.71/1.04  --res_lit_sel                           adaptive
% 3.71/1.04  --res_lit_sel_side                      none
% 3.71/1.04  --res_ordering                          kbo
% 3.71/1.04  --res_to_prop_solver                    active
% 3.71/1.04  --res_prop_simpl_new                    false
% 3.71/1.04  --res_prop_simpl_given                  true
% 3.71/1.04  --res_passive_queue_type                priority_queues
% 3.71/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.71/1.04  --res_passive_queues_freq               [15;5]
% 3.71/1.04  --res_forward_subs                      full
% 3.71/1.04  --res_backward_subs                     full
% 3.71/1.04  --res_forward_subs_resolution           true
% 3.71/1.04  --res_backward_subs_resolution          true
% 3.71/1.04  --res_orphan_elimination                true
% 3.71/1.04  --res_time_limit                        2.
% 3.71/1.04  --res_out_proof                         true
% 3.71/1.04  
% 3.71/1.04  ------ Superposition Options
% 3.71/1.04  
% 3.71/1.04  --superposition_flag                    true
% 3.71/1.04  --sup_passive_queue_type                priority_queues
% 3.71/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.71/1.04  --sup_passive_queues_freq               [8;1;4]
% 3.71/1.04  --demod_completeness_check              fast
% 3.71/1.04  --demod_use_ground                      true
% 3.71/1.04  --sup_to_prop_solver                    passive
% 3.71/1.04  --sup_prop_simpl_new                    true
% 3.71/1.04  --sup_prop_simpl_given                  true
% 3.71/1.04  --sup_fun_splitting                     false
% 3.71/1.04  --sup_smt_interval                      50000
% 3.71/1.04  
% 3.71/1.04  ------ Superposition Simplification Setup
% 3.71/1.04  
% 3.71/1.04  --sup_indices_passive                   []
% 3.71/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.71/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.71/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.71/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 3.71/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.71/1.04  --sup_full_bw                           [BwDemod]
% 3.71/1.04  --sup_immed_triv                        [TrivRules]
% 3.71/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.71/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.71/1.04  --sup_immed_bw_main                     []
% 3.71/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.71/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 3.71/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.71/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.71/1.04  
% 3.71/1.04  ------ Combination Options
% 3.71/1.04  
% 3.71/1.04  --comb_res_mult                         3
% 3.71/1.04  --comb_sup_mult                         2
% 3.71/1.04  --comb_inst_mult                        10
% 3.71/1.04  
% 3.71/1.04  ------ Debug Options
% 3.71/1.04  
% 3.71/1.04  --dbg_backtrace                         false
% 3.71/1.04  --dbg_dump_prop_clauses                 false
% 3.71/1.04  --dbg_dump_prop_clauses_file            -
% 3.71/1.04  --dbg_out_stat                          false
% 3.71/1.04  ------ Parsing...
% 3.71/1.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.71/1.04  
% 3.71/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.71/1.04  
% 3.71/1.04  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.71/1.04  
% 3.71/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.71/1.04  ------ Proving...
% 3.71/1.04  ------ Problem Properties 
% 3.71/1.04  
% 3.71/1.04  
% 3.71/1.04  clauses                                 36
% 3.71/1.04  conjectures                             4
% 3.71/1.04  EPR                                     7
% 3.71/1.04  Horn                                    32
% 3.71/1.04  unary                                   10
% 3.71/1.04  binary                                  10
% 3.71/1.04  lits                                    91
% 3.71/1.04  lits eq                                 33
% 3.71/1.04  fd_pure                                 0
% 3.71/1.04  fd_pseudo                               0
% 3.71/1.04  fd_cond                                 3
% 3.71/1.04  fd_pseudo_cond                          0
% 3.71/1.04  AC symbols                              0
% 3.71/1.04  
% 3.71/1.04  ------ Schedule dynamic 5 is on 
% 3.71/1.04  
% 3.71/1.04  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.71/1.04  
% 3.71/1.04  
% 3.71/1.04  ------ 
% 3.71/1.04  Current options:
% 3.71/1.04  ------ 
% 3.71/1.04  
% 3.71/1.04  ------ Input Options
% 3.71/1.04  
% 3.71/1.04  --out_options                           all
% 3.71/1.04  --tptp_safe_out                         true
% 3.71/1.04  --problem_path                          ""
% 3.71/1.04  --include_path                          ""
% 3.71/1.04  --clausifier                            res/vclausify_rel
% 3.71/1.04  --clausifier_options                    --mode clausify
% 3.71/1.04  --stdin                                 false
% 3.71/1.04  --stats_out                             all
% 3.71/1.04  
% 3.71/1.04  ------ General Options
% 3.71/1.04  
% 3.71/1.04  --fof                                   false
% 3.71/1.04  --time_out_real                         305.
% 3.71/1.04  --time_out_virtual                      -1.
% 3.71/1.04  --symbol_type_check                     false
% 3.71/1.04  --clausify_out                          false
% 3.71/1.04  --sig_cnt_out                           false
% 3.71/1.04  --trig_cnt_out                          false
% 3.71/1.04  --trig_cnt_out_tolerance                1.
% 3.71/1.04  --trig_cnt_out_sk_spl                   false
% 3.71/1.04  --abstr_cl_out                          false
% 3.71/1.04  
% 3.71/1.04  ------ Global Options
% 3.71/1.04  
% 3.71/1.04  --schedule                              default
% 3.71/1.04  --add_important_lit                     false
% 3.71/1.04  --prop_solver_per_cl                    1000
% 3.71/1.04  --min_unsat_core                        false
% 3.71/1.04  --soft_assumptions                      false
% 3.71/1.04  --soft_lemma_size                       3
% 3.71/1.04  --prop_impl_unit_size                   0
% 3.71/1.04  --prop_impl_unit                        []
% 3.71/1.04  --share_sel_clauses                     true
% 3.71/1.04  --reset_solvers                         false
% 3.71/1.04  --bc_imp_inh                            [conj_cone]
% 3.71/1.04  --conj_cone_tolerance                   3.
% 3.71/1.04  --extra_neg_conj                        none
% 3.71/1.04  --large_theory_mode                     true
% 3.71/1.04  --prolific_symb_bound                   200
% 3.71/1.04  --lt_threshold                          2000
% 3.71/1.04  --clause_weak_htbl                      true
% 3.71/1.04  --gc_record_bc_elim                     false
% 3.71/1.04  
% 3.71/1.04  ------ Preprocessing Options
% 3.71/1.04  
% 3.71/1.04  --preprocessing_flag                    true
% 3.71/1.04  --time_out_prep_mult                    0.1
% 3.71/1.04  --splitting_mode                        input
% 3.71/1.04  --splitting_grd                         true
% 3.71/1.04  --splitting_cvd                         false
% 3.71/1.04  --splitting_cvd_svl                     false
% 3.71/1.04  --splitting_nvd                         32
% 3.71/1.04  --sub_typing                            true
% 3.71/1.04  --prep_gs_sim                           true
% 3.71/1.04  --prep_unflatten                        true
% 3.71/1.04  --prep_res_sim                          true
% 3.71/1.04  --prep_upred                            true
% 3.71/1.04  --prep_sem_filter                       exhaustive
% 3.71/1.04  --prep_sem_filter_out                   false
% 3.71/1.04  --pred_elim                             true
% 3.71/1.04  --res_sim_input                         true
% 3.71/1.04  --eq_ax_congr_red                       true
% 3.71/1.04  --pure_diseq_elim                       true
% 3.71/1.04  --brand_transform                       false
% 3.71/1.04  --non_eq_to_eq                          false
% 3.71/1.04  --prep_def_merge                        true
% 3.71/1.04  --prep_def_merge_prop_impl              false
% 3.71/1.04  --prep_def_merge_mbd                    true
% 3.71/1.04  --prep_def_merge_tr_red                 false
% 3.71/1.04  --prep_def_merge_tr_cl                  false
% 3.71/1.04  --smt_preprocessing                     true
% 3.71/1.04  --smt_ac_axioms                         fast
% 3.71/1.04  --preprocessed_out                      false
% 3.71/1.04  --preprocessed_stats                    false
% 3.71/1.04  
% 3.71/1.04  ------ Abstraction refinement Options
% 3.71/1.04  
% 3.71/1.04  --abstr_ref                             []
% 3.71/1.04  --abstr_ref_prep                        false
% 3.71/1.04  --abstr_ref_until_sat                   false
% 3.71/1.04  --abstr_ref_sig_restrict                funpre
% 3.71/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 3.71/1.04  --abstr_ref_under                       []
% 3.71/1.04  
% 3.71/1.04  ------ SAT Options
% 3.71/1.04  
% 3.71/1.04  --sat_mode                              false
% 3.71/1.04  --sat_fm_restart_options                ""
% 3.71/1.04  --sat_gr_def                            false
% 3.71/1.04  --sat_epr_types                         true
% 3.71/1.04  --sat_non_cyclic_types                  false
% 3.71/1.04  --sat_finite_models                     false
% 3.71/1.04  --sat_fm_lemmas                         false
% 3.71/1.04  --sat_fm_prep                           false
% 3.71/1.04  --sat_fm_uc_incr                        true
% 3.71/1.04  --sat_out_model                         small
% 3.71/1.04  --sat_out_clauses                       false
% 3.71/1.04  
% 3.71/1.04  ------ QBF Options
% 3.71/1.04  
% 3.71/1.04  --qbf_mode                              false
% 3.71/1.04  --qbf_elim_univ                         false
% 3.71/1.04  --qbf_dom_inst                          none
% 3.71/1.04  --qbf_dom_pre_inst                      false
% 3.71/1.04  --qbf_sk_in                             false
% 3.71/1.04  --qbf_pred_elim                         true
% 3.71/1.04  --qbf_split                             512
% 3.71/1.04  
% 3.71/1.04  ------ BMC1 Options
% 3.71/1.04  
% 3.71/1.04  --bmc1_incremental                      false
% 3.71/1.04  --bmc1_axioms                           reachable_all
% 3.71/1.04  --bmc1_min_bound                        0
% 3.71/1.04  --bmc1_max_bound                        -1
% 3.71/1.04  --bmc1_max_bound_default                -1
% 3.71/1.04  --bmc1_symbol_reachability              true
% 3.71/1.04  --bmc1_property_lemmas                  false
% 3.71/1.04  --bmc1_k_induction                      false
% 3.71/1.04  --bmc1_non_equiv_states                 false
% 3.71/1.04  --bmc1_deadlock                         false
% 3.71/1.04  --bmc1_ucm                              false
% 3.71/1.04  --bmc1_add_unsat_core                   none
% 3.71/1.04  --bmc1_unsat_core_children              false
% 3.71/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 3.71/1.04  --bmc1_out_stat                         full
% 3.71/1.04  --bmc1_ground_init                      false
% 3.71/1.04  --bmc1_pre_inst_next_state              false
% 3.71/1.04  --bmc1_pre_inst_state                   false
% 3.71/1.04  --bmc1_pre_inst_reach_state             false
% 3.71/1.04  --bmc1_out_unsat_core                   false
% 3.71/1.04  --bmc1_aig_witness_out                  false
% 3.71/1.04  --bmc1_verbose                          false
% 3.71/1.04  --bmc1_dump_clauses_tptp                false
% 3.71/1.04  --bmc1_dump_unsat_core_tptp             false
% 3.71/1.04  --bmc1_dump_file                        -
% 3.71/1.04  --bmc1_ucm_expand_uc_limit              128
% 3.71/1.04  --bmc1_ucm_n_expand_iterations          6
% 3.71/1.04  --bmc1_ucm_extend_mode                  1
% 3.71/1.04  --bmc1_ucm_init_mode                    2
% 3.71/1.04  --bmc1_ucm_cone_mode                    none
% 3.71/1.04  --bmc1_ucm_reduced_relation_type        0
% 3.71/1.04  --bmc1_ucm_relax_model                  4
% 3.71/1.04  --bmc1_ucm_full_tr_after_sat            true
% 3.71/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 3.71/1.04  --bmc1_ucm_layered_model                none
% 3.71/1.04  --bmc1_ucm_max_lemma_size               10
% 3.71/1.04  
% 3.71/1.04  ------ AIG Options
% 3.71/1.04  
% 3.71/1.04  --aig_mode                              false
% 3.71/1.04  
% 3.71/1.04  ------ Instantiation Options
% 3.71/1.04  
% 3.71/1.04  --instantiation_flag                    true
% 3.71/1.04  --inst_sos_flag                         false
% 3.71/1.04  --inst_sos_phase                        true
% 3.71/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.71/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.71/1.04  --inst_lit_sel_side                     none
% 3.71/1.04  --inst_solver_per_active                1400
% 3.71/1.04  --inst_solver_calls_frac                1.
% 3.71/1.04  --inst_passive_queue_type               priority_queues
% 3.71/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.71/1.04  --inst_passive_queues_freq              [25;2]
% 3.71/1.04  --inst_dismatching                      true
% 3.71/1.04  --inst_eager_unprocessed_to_passive     true
% 3.71/1.04  --inst_prop_sim_given                   true
% 3.71/1.04  --inst_prop_sim_new                     false
% 3.71/1.04  --inst_subs_new                         false
% 3.71/1.04  --inst_eq_res_simp                      false
% 3.71/1.04  --inst_subs_given                       false
% 3.71/1.04  --inst_orphan_elimination               true
% 3.71/1.04  --inst_learning_loop_flag               true
% 3.71/1.04  --inst_learning_start                   3000
% 3.71/1.04  --inst_learning_factor                  2
% 3.71/1.04  --inst_start_prop_sim_after_learn       3
% 3.71/1.04  --inst_sel_renew                        solver
% 3.71/1.04  --inst_lit_activity_flag                true
% 3.71/1.04  --inst_restr_to_given                   false
% 3.71/1.04  --inst_activity_threshold               500
% 3.71/1.04  --inst_out_proof                        true
% 3.71/1.04  
% 3.71/1.04  ------ Resolution Options
% 3.71/1.04  
% 3.71/1.04  --resolution_flag                       false
% 3.71/1.04  --res_lit_sel                           adaptive
% 3.71/1.04  --res_lit_sel_side                      none
% 3.71/1.04  --res_ordering                          kbo
% 3.71/1.04  --res_to_prop_solver                    active
% 3.71/1.04  --res_prop_simpl_new                    false
% 3.71/1.04  --res_prop_simpl_given                  true
% 3.71/1.04  --res_passive_queue_type                priority_queues
% 3.71/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.71/1.04  --res_passive_queues_freq               [15;5]
% 3.71/1.04  --res_forward_subs                      full
% 3.71/1.04  --res_backward_subs                     full
% 3.71/1.04  --res_forward_subs_resolution           true
% 3.71/1.04  --res_backward_subs_resolution          true
% 3.71/1.04  --res_orphan_elimination                true
% 3.71/1.04  --res_time_limit                        2.
% 3.71/1.04  --res_out_proof                         true
% 3.71/1.04  
% 3.71/1.04  ------ Superposition Options
% 3.71/1.04  
% 3.71/1.04  --superposition_flag                    true
% 3.71/1.04  --sup_passive_queue_type                priority_queues
% 3.71/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.71/1.04  --sup_passive_queues_freq               [8;1;4]
% 3.71/1.04  --demod_completeness_check              fast
% 3.71/1.04  --demod_use_ground                      true
% 3.71/1.04  --sup_to_prop_solver                    passive
% 3.71/1.04  --sup_prop_simpl_new                    true
% 3.71/1.04  --sup_prop_simpl_given                  true
% 3.71/1.04  --sup_fun_splitting                     false
% 3.71/1.04  --sup_smt_interval                      50000
% 3.71/1.04  
% 3.71/1.04  ------ Superposition Simplification Setup
% 3.71/1.04  
% 3.71/1.04  --sup_indices_passive                   []
% 3.71/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.71/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.71/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.71/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 3.71/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.71/1.04  --sup_full_bw                           [BwDemod]
% 3.71/1.04  --sup_immed_triv                        [TrivRules]
% 3.71/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.71/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.71/1.04  --sup_immed_bw_main                     []
% 3.71/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.71/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 3.71/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.71/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.71/1.04  
% 3.71/1.04  ------ Combination Options
% 3.71/1.04  
% 3.71/1.04  --comb_res_mult                         3
% 3.71/1.04  --comb_sup_mult                         2
% 3.71/1.04  --comb_inst_mult                        10
% 3.71/1.04  
% 3.71/1.04  ------ Debug Options
% 3.71/1.04  
% 3.71/1.04  --dbg_backtrace                         false
% 3.71/1.04  --dbg_dump_prop_clauses                 false
% 3.71/1.04  --dbg_dump_prop_clauses_file            -
% 3.71/1.04  --dbg_out_stat                          false
% 3.71/1.04  
% 3.71/1.04  
% 3.71/1.04  
% 3.71/1.04  
% 3.71/1.04  ------ Proving...
% 3.71/1.04  
% 3.71/1.04  
% 3.71/1.04  % SZS status Theorem for theBenchmark.p
% 3.71/1.04  
% 3.71/1.04   Resolution empty clause
% 3.71/1.04  
% 3.71/1.04  % SZS output start CNFRefutation for theBenchmark.p
% 3.71/1.04  
% 3.71/1.04  fof(f23,conjecture,(
% 3.71/1.04    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.71/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.04  
% 3.71/1.04  fof(f24,negated_conjecture,(
% 3.71/1.04    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.71/1.04    inference(negated_conjecture,[],[f23])).
% 3.71/1.04  
% 3.71/1.04  fof(f48,plain,(
% 3.71/1.04    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.71/1.04    inference(ennf_transformation,[],[f24])).
% 3.71/1.04  
% 3.71/1.04  fof(f49,plain,(
% 3.71/1.04    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.71/1.04    inference(flattening,[],[f48])).
% 3.71/1.04  
% 3.71/1.04  fof(f52,plain,(
% 3.71/1.04    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 3.71/1.04    introduced(choice_axiom,[])).
% 3.71/1.04  
% 3.71/1.04  fof(f53,plain,(
% 3.71/1.04    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 3.71/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f49,f52])).
% 3.71/1.04  
% 3.71/1.04  fof(f89,plain,(
% 3.71/1.04    r1_tarski(sK2,sK0)),
% 3.71/1.04    inference(cnf_transformation,[],[f53])).
% 3.71/1.04  
% 3.71/1.04  fof(f19,axiom,(
% 3.71/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.71/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.04  
% 3.71/1.04  fof(f40,plain,(
% 3.71/1.04    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.71/1.04    inference(ennf_transformation,[],[f19])).
% 3.71/1.04  
% 3.71/1.04  fof(f41,plain,(
% 3.71/1.04    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.71/1.04    inference(flattening,[],[f40])).
% 3.71/1.04  
% 3.71/1.04  fof(f51,plain,(
% 3.71/1.04    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.71/1.04    inference(nnf_transformation,[],[f41])).
% 3.71/1.04  
% 3.71/1.04  fof(f74,plain,(
% 3.71/1.04    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.71/1.04    inference(cnf_transformation,[],[f51])).
% 3.71/1.04  
% 3.71/1.04  fof(f87,plain,(
% 3.71/1.04    v1_funct_2(sK3,sK0,sK1)),
% 3.71/1.04    inference(cnf_transformation,[],[f53])).
% 3.71/1.04  
% 3.71/1.04  fof(f88,plain,(
% 3.71/1.04    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.71/1.04    inference(cnf_transformation,[],[f53])).
% 3.71/1.04  
% 3.71/1.04  fof(f18,axiom,(
% 3.71/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.71/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.04  
% 3.71/1.04  fof(f39,plain,(
% 3.71/1.04    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.71/1.04    inference(ennf_transformation,[],[f18])).
% 3.71/1.04  
% 3.71/1.04  fof(f73,plain,(
% 3.71/1.04    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.71/1.04    inference(cnf_transformation,[],[f39])).
% 3.71/1.04  
% 3.71/1.04  fof(f11,axiom,(
% 3.71/1.04    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 3.71/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.04  
% 3.71/1.04  fof(f32,plain,(
% 3.71/1.04    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 3.71/1.04    inference(ennf_transformation,[],[f11])).
% 3.71/1.04  
% 3.71/1.04  fof(f33,plain,(
% 3.71/1.04    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.71/1.04    inference(flattening,[],[f32])).
% 3.71/1.04  
% 3.71/1.04  fof(f65,plain,(
% 3.71/1.04    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.71/1.04    inference(cnf_transformation,[],[f33])).
% 3.71/1.04  
% 3.71/1.04  fof(f15,axiom,(
% 3.71/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.71/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.04  
% 3.71/1.04  fof(f36,plain,(
% 3.71/1.04    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.71/1.04    inference(ennf_transformation,[],[f15])).
% 3.71/1.04  
% 3.71/1.04  fof(f70,plain,(
% 3.71/1.04    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.71/1.04    inference(cnf_transformation,[],[f36])).
% 3.71/1.04  
% 3.71/1.04  fof(f22,axiom,(
% 3.71/1.04    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 3.71/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.04  
% 3.71/1.04  fof(f46,plain,(
% 3.71/1.04    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.71/1.04    inference(ennf_transformation,[],[f22])).
% 3.71/1.04  
% 3.71/1.04  fof(f47,plain,(
% 3.71/1.04    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.71/1.04    inference(flattening,[],[f46])).
% 3.71/1.04  
% 3.71/1.04  fof(f85,plain,(
% 3.71/1.04    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.71/1.04    inference(cnf_transformation,[],[f47])).
% 3.71/1.04  
% 3.71/1.04  fof(f8,axiom,(
% 3.71/1.04    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 3.71/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.04  
% 3.71/1.04  fof(f31,plain,(
% 3.71/1.04    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 3.71/1.04    inference(ennf_transformation,[],[f8])).
% 3.71/1.04  
% 3.71/1.04  fof(f61,plain,(
% 3.71/1.04    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 3.71/1.04    inference(cnf_transformation,[],[f31])).
% 3.71/1.04  
% 3.71/1.04  fof(f21,axiom,(
% 3.71/1.04    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 3.71/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.04  
% 3.71/1.04  fof(f44,plain,(
% 3.71/1.04    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.71/1.04    inference(ennf_transformation,[],[f21])).
% 3.71/1.04  
% 3.71/1.04  fof(f45,plain,(
% 3.71/1.04    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.71/1.04    inference(flattening,[],[f44])).
% 3.71/1.04  
% 3.71/1.04  fof(f82,plain,(
% 3.71/1.04    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.71/1.04    inference(cnf_transformation,[],[f45])).
% 3.71/1.04  
% 3.71/1.04  fof(f86,plain,(
% 3.71/1.04    v1_funct_1(sK3)),
% 3.71/1.04    inference(cnf_transformation,[],[f53])).
% 3.71/1.04  
% 3.71/1.04  fof(f20,axiom,(
% 3.71/1.04    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 3.71/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.04  
% 3.71/1.04  fof(f42,plain,(
% 3.71/1.04    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.71/1.04    inference(ennf_transformation,[],[f20])).
% 3.71/1.04  
% 3.71/1.04  fof(f43,plain,(
% 3.71/1.04    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.71/1.04    inference(flattening,[],[f42])).
% 3.71/1.04  
% 3.71/1.04  fof(f80,plain,(
% 3.71/1.04    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.71/1.04    inference(cnf_transformation,[],[f43])).
% 3.71/1.04  
% 3.71/1.04  fof(f84,plain,(
% 3.71/1.04    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.71/1.04    inference(cnf_transformation,[],[f47])).
% 3.71/1.04  
% 3.71/1.04  fof(f91,plain,(
% 3.71/1.04    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 3.71/1.04    inference(cnf_transformation,[],[f53])).
% 3.71/1.04  
% 3.71/1.04  fof(f16,axiom,(
% 3.71/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.71/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.04  
% 3.71/1.04  fof(f25,plain,(
% 3.71/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.71/1.04    inference(pure_predicate_removal,[],[f16])).
% 3.71/1.04  
% 3.71/1.04  fof(f37,plain,(
% 3.71/1.04    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.71/1.04    inference(ennf_transformation,[],[f25])).
% 3.71/1.04  
% 3.71/1.04  fof(f71,plain,(
% 3.71/1.04    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.71/1.04    inference(cnf_transformation,[],[f37])).
% 3.71/1.04  
% 3.71/1.04  fof(f7,axiom,(
% 3.71/1.04    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.71/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.04  
% 3.71/1.04  fof(f30,plain,(
% 3.71/1.04    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.71/1.04    inference(ennf_transformation,[],[f7])).
% 3.71/1.04  
% 3.71/1.04  fof(f50,plain,(
% 3.71/1.04    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.71/1.04    inference(nnf_transformation,[],[f30])).
% 3.71/1.04  
% 3.71/1.04  fof(f59,plain,(
% 3.71/1.04    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.71/1.04    inference(cnf_transformation,[],[f50])).
% 3.71/1.04  
% 3.71/1.04  fof(f81,plain,(
% 3.71/1.04    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.71/1.04    inference(cnf_transformation,[],[f43])).
% 3.71/1.04  
% 3.71/1.04  fof(f9,axiom,(
% 3.71/1.04    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.71/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.04  
% 3.71/1.04  fof(f62,plain,(
% 3.71/1.04    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.71/1.04    inference(cnf_transformation,[],[f9])).
% 3.71/1.04  
% 3.71/1.04  fof(f10,axiom,(
% 3.71/1.04    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 3.71/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.04  
% 3.71/1.04  fof(f64,plain,(
% 3.71/1.04    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 3.71/1.04    inference(cnf_transformation,[],[f10])).
% 3.71/1.04  
% 3.71/1.04  fof(f14,axiom,(
% 3.71/1.04    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.71/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.04  
% 3.71/1.04  fof(f68,plain,(
% 3.71/1.04    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 3.71/1.04    inference(cnf_transformation,[],[f14])).
% 3.71/1.04  
% 3.71/1.04  fof(f12,axiom,(
% 3.71/1.04    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 3.71/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.04  
% 3.71/1.04  fof(f34,plain,(
% 3.71/1.04    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 3.71/1.04    inference(ennf_transformation,[],[f12])).
% 3.71/1.04  
% 3.71/1.04  fof(f66,plain,(
% 3.71/1.04    ( ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 3.71/1.04    inference(cnf_transformation,[],[f34])).
% 3.71/1.04  
% 3.71/1.04  fof(f90,plain,(
% 3.71/1.04    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 3.71/1.04    inference(cnf_transformation,[],[f53])).
% 3.71/1.04  
% 3.71/1.04  fof(f3,axiom,(
% 3.71/1.04    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 3.71/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.04  
% 3.71/1.04  fof(f56,plain,(
% 3.71/1.04    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 3.71/1.04    inference(cnf_transformation,[],[f3])).
% 3.71/1.04  
% 3.71/1.04  fof(f4,axiom,(
% 3.71/1.04    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 3.71/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.04  
% 3.71/1.04  fof(f28,plain,(
% 3.71/1.04    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 3.71/1.04    inference(ennf_transformation,[],[f4])).
% 3.71/1.04  
% 3.71/1.04  fof(f29,plain,(
% 3.71/1.04    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 3.71/1.04    inference(flattening,[],[f28])).
% 3.71/1.04  
% 3.71/1.04  fof(f57,plain,(
% 3.71/1.04    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 3.71/1.04    inference(cnf_transformation,[],[f29])).
% 3.71/1.04  
% 3.71/1.04  fof(f2,axiom,(
% 3.71/1.04    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.71/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.04  
% 3.71/1.04  fof(f27,plain,(
% 3.71/1.04    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.71/1.04    inference(ennf_transformation,[],[f2])).
% 3.71/1.04  
% 3.71/1.04  fof(f55,plain,(
% 3.71/1.04    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.71/1.04    inference(cnf_transformation,[],[f27])).
% 3.71/1.04  
% 3.71/1.04  fof(f17,axiom,(
% 3.71/1.04    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 3.71/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.04  
% 3.71/1.04  fof(f38,plain,(
% 3.71/1.04    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 3.71/1.04    inference(ennf_transformation,[],[f17])).
% 3.71/1.04  
% 3.71/1.04  fof(f72,plain,(
% 3.71/1.04    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 3.71/1.04    inference(cnf_transformation,[],[f38])).
% 3.71/1.04  
% 3.71/1.04  fof(f1,axiom,(
% 3.71/1.04    v1_xboole_0(k1_xboole_0)),
% 3.71/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.04  
% 3.71/1.04  fof(f54,plain,(
% 3.71/1.04    v1_xboole_0(k1_xboole_0)),
% 3.71/1.04    inference(cnf_transformation,[],[f1])).
% 3.71/1.04  
% 3.71/1.04  fof(f5,axiom,(
% 3.71/1.04    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.71/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.04  
% 3.71/1.04  fof(f58,plain,(
% 3.71/1.04    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.71/1.04    inference(cnf_transformation,[],[f5])).
% 3.71/1.04  
% 3.71/1.04  cnf(c_34,negated_conjecture,
% 3.71/1.04      ( r1_tarski(sK2,sK0) ),
% 3.71/1.04      inference(cnf_transformation,[],[f89]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_2045,plain,
% 3.71/1.04      ( r1_tarski(sK2,sK0) = iProver_top ),
% 3.71/1.04      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_25,plain,
% 3.71/1.04      ( ~ v1_funct_2(X0,X1,X2)
% 3.71/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.71/1.04      | k1_relset_1(X1,X2,X0) = X1
% 3.71/1.04      | k1_xboole_0 = X2 ),
% 3.71/1.04      inference(cnf_transformation,[],[f74]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_36,negated_conjecture,
% 3.71/1.04      ( v1_funct_2(sK3,sK0,sK1) ),
% 3.71/1.04      inference(cnf_transformation,[],[f87]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_754,plain,
% 3.71/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.71/1.04      | k1_relset_1(X1,X2,X0) = X1
% 3.71/1.04      | sK3 != X0
% 3.71/1.04      | sK1 != X2
% 3.71/1.04      | sK0 != X1
% 3.71/1.04      | k1_xboole_0 = X2 ),
% 3.71/1.04      inference(resolution_lifted,[status(thm)],[c_25,c_36]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_755,plain,
% 3.71/1.04      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.71/1.04      | k1_relset_1(sK0,sK1,sK3) = sK0
% 3.71/1.04      | k1_xboole_0 = sK1 ),
% 3.71/1.04      inference(unflattening,[status(thm)],[c_754]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_35,negated_conjecture,
% 3.71/1.04      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.71/1.04      inference(cnf_transformation,[],[f88]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_757,plain,
% 3.71/1.04      ( k1_relset_1(sK0,sK1,sK3) = sK0 | k1_xboole_0 = sK1 ),
% 3.71/1.04      inference(global_propositional_subsumption,[status(thm)],[c_755,c_35]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_2044,plain,
% 3.71/1.04      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.71/1.04      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_19,plain,
% 3.71/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.71/1.04      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.71/1.04      inference(cnf_transformation,[],[f73]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_2050,plain,
% 3.71/1.04      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.71/1.04      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.71/1.04      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_3364,plain,
% 3.71/1.04      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 3.71/1.04      inference(superposition,[status(thm)],[c_2044,c_2050]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_3548,plain,
% 3.71/1.04      ( k1_relat_1(sK3) = sK0 | sK1 = k1_xboole_0 ),
% 3.71/1.04      inference(superposition,[status(thm)],[c_757,c_3364]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_11,plain,
% 3.71/1.04      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 3.71/1.04      | ~ v1_relat_1(X1)
% 3.71/1.04      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 3.71/1.04      inference(cnf_transformation,[],[f65]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_2057,plain,
% 3.71/1.04      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 3.71/1.04      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 3.71/1.04      | v1_relat_1(X0) != iProver_top ),
% 3.71/1.04      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_4067,plain,
% 3.71/1.04      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 3.71/1.04      | sK1 = k1_xboole_0
% 3.71/1.04      | r1_tarski(X0,sK0) != iProver_top
% 3.71/1.04      | v1_relat_1(sK3) != iProver_top ),
% 3.71/1.04      inference(superposition,[status(thm)],[c_3548,c_2057]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_40,plain,
% 3.71/1.04      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.71/1.04      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_16,plain,
% 3.71/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 3.71/1.04      inference(cnf_transformation,[],[f70]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_2330,plain,
% 3.71/1.04      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.71/1.04      | v1_relat_1(sK3) ),
% 3.71/1.04      inference(instantiation,[status(thm)],[c_16]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_2331,plain,
% 3.71/1.04      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.71/1.04      | v1_relat_1(sK3) = iProver_top ),
% 3.71/1.04      inference(predicate_to_equality,[status(thm)],[c_2330]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_4547,plain,
% 3.71/1.04      ( r1_tarski(X0,sK0) != iProver_top
% 3.71/1.04      | sK1 = k1_xboole_0
% 3.71/1.04      | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
% 3.71/1.04      inference(global_propositional_subsumption,
% 3.71/1.04                [status(thm)],
% 3.71/1.04                [c_4067,c_40,c_2331]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_4548,plain,
% 3.71/1.04      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 3.71/1.04      | sK1 = k1_xboole_0
% 3.71/1.04      | r1_tarski(X0,sK0) != iProver_top ),
% 3.71/1.04      inference(renaming,[status(thm)],[c_4547]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_4556,plain,
% 3.71/1.04      ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2 | sK1 = k1_xboole_0 ),
% 3.71/1.04      inference(superposition,[status(thm)],[c_2045,c_4548]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_29,plain,
% 3.71/1.04      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.71/1.04      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.71/1.04      | ~ v1_funct_1(X0)
% 3.71/1.04      | ~ v1_relat_1(X0) ),
% 3.71/1.04      inference(cnf_transformation,[],[f85]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_2046,plain,
% 3.71/1.04      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
% 3.71/1.04      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 3.71/1.04      | v1_funct_1(X0) != iProver_top
% 3.71/1.04      | v1_relat_1(X0) != iProver_top ),
% 3.71/1.04      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_4955,plain,
% 3.71/1.04      ( sK1 = k1_xboole_0
% 3.71/1.04      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 3.71/1.04      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
% 3.71/1.04      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
% 3.71/1.04      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.71/1.04      inference(superposition,[status(thm)],[c_4556,c_2046]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_7,plain,
% 3.71/1.04      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 3.71/1.04      inference(cnf_transformation,[],[f61]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_2446,plain,
% 3.71/1.04      ( v1_relat_1(k7_relat_1(sK3,X0)) | ~ v1_relat_1(sK3) ),
% 3.71/1.04      inference(instantiation,[status(thm)],[c_7]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_5641,plain,
% 3.71/1.04      ( v1_relat_1(k7_relat_1(sK3,sK2)) | ~ v1_relat_1(sK3) ),
% 3.71/1.04      inference(instantiation,[status(thm)],[c_2446]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_5642,plain,
% 3.71/1.04      ( v1_relat_1(k7_relat_1(sK3,sK2)) = iProver_top
% 3.71/1.04      | v1_relat_1(sK3) != iProver_top ),
% 3.71/1.04      inference(predicate_to_equality,[status(thm)],[c_5641]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_5715,plain,
% 3.71/1.04      ( v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
% 3.71/1.04      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
% 3.71/1.04      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 3.71/1.04      | sK1 = k1_xboole_0 ),
% 3.71/1.04      inference(global_propositional_subsumption,
% 3.71/1.04                [status(thm)],
% 3.71/1.04                [c_4955,c_40,c_2331,c_5642]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_5716,plain,
% 3.71/1.04      ( sK1 = k1_xboole_0
% 3.71/1.04      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 3.71/1.04      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
% 3.71/1.04      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.71/1.04      inference(renaming,[status(thm)],[c_5715]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_28,plain,
% 3.71/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.71/1.04      | ~ v1_funct_1(X0)
% 3.71/1.04      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 3.71/1.04      inference(cnf_transformation,[],[f82]) ).
% 3.71/1.04  
% 3.71/1.04  cnf(c_2047,plain,
% 3.71/1.04      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 3.71/1.04      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.71/1.04      | v1_funct_1(X2) != iProver_top ),
% 3.71/1.04      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_5044,plain,
% 3.71/1.05      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
% 3.71/1.05      | v1_funct_1(sK3) != iProver_top ),
% 3.71/1.05      inference(superposition,[status(thm)],[c_2044,c_2047]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_37,negated_conjecture,
% 3.71/1.05      ( v1_funct_1(sK3) ),
% 3.71/1.05      inference(cnf_transformation,[],[f86]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_2428,plain,
% 3.71/1.05      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.71/1.05      | ~ v1_funct_1(sK3)
% 3.71/1.05      | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 3.71/1.05      inference(instantiation,[status(thm)],[c_28]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_5313,plain,
% 3.71/1.05      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 3.71/1.05      inference(global_propositional_subsumption,
% 3.71/1.05                [status(thm)],
% 3.71/1.05                [c_5044,c_37,c_35,c_2428]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_27,plain,
% 3.71/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.71/1.05      | ~ v1_funct_1(X0)
% 3.71/1.05      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
% 3.71/1.05      inference(cnf_transformation,[],[f80]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_2048,plain,
% 3.71/1.05      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.71/1.05      | v1_funct_1(X0) != iProver_top
% 3.71/1.05      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
% 3.71/1.05      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_4291,plain,
% 3.71/1.05      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
% 3.71/1.05      | v1_funct_1(sK3) != iProver_top ),
% 3.71/1.05      inference(superposition,[status(thm)],[c_2044,c_2048]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_38,plain,
% 3.71/1.05      ( v1_funct_1(sK3) = iProver_top ),
% 3.71/1.05      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_2399,plain,
% 3.71/1.05      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.71/1.05      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
% 3.71/1.05      | ~ v1_funct_1(sK3) ),
% 3.71/1.05      inference(instantiation,[status(thm)],[c_27]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_2400,plain,
% 3.71/1.05      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.71/1.05      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
% 3.71/1.05      | v1_funct_1(sK3) != iProver_top ),
% 3.71/1.05      inference(predicate_to_equality,[status(thm)],[c_2399]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_4501,plain,
% 3.71/1.05      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
% 3.71/1.05      inference(global_propositional_subsumption,
% 3.71/1.05                [status(thm)],
% 3.71/1.05                [c_4291,c_38,c_40,c_2400]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_5322,plain,
% 3.71/1.05      ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 3.71/1.05      inference(demodulation,[status(thm)],[c_5313,c_4501]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_5725,plain,
% 3.71/1.05      ( sK1 = k1_xboole_0
% 3.71/1.05      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 3.71/1.05      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top ),
% 3.71/1.05      inference(forward_subsumption_resolution,[status(thm)],[c_5716,c_5322]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_30,plain,
% 3.71/1.05      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 3.71/1.05      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.71/1.05      | ~ v1_funct_1(X0)
% 3.71/1.05      | ~ v1_relat_1(X0) ),
% 3.71/1.05      inference(cnf_transformation,[],[f84]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_32,negated_conjecture,
% 3.71/1.05      ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
% 3.71/1.05      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.71/1.05      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
% 3.71/1.05      inference(cnf_transformation,[],[f91]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_765,plain,
% 3.71/1.05      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.71/1.05      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.71/1.05      | ~ v1_funct_1(X0)
% 3.71/1.05      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.71/1.05      | ~ v1_relat_1(X0)
% 3.71/1.05      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 3.71/1.05      | k1_relat_1(X0) != sK2
% 3.71/1.05      | sK1 != X1 ),
% 3.71/1.05      inference(resolution_lifted,[status(thm)],[c_30,c_32]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_766,plain,
% 3.71/1.05      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.71/1.05      | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
% 3.71/1.05      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.71/1.05      | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.71/1.05      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
% 3.71/1.05      inference(unflattening,[status(thm)],[c_765]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_17,plain,
% 3.71/1.05      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.71/1.05      inference(cnf_transformation,[],[f71]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_6,plain,
% 3.71/1.05      ( ~ v5_relat_1(X0,X1) | r1_tarski(k2_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 3.71/1.05      inference(cnf_transformation,[],[f59]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_395,plain,
% 3.71/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.71/1.05      | r1_tarski(k2_relat_1(X0),X2)
% 3.71/1.05      | ~ v1_relat_1(X0) ),
% 3.71/1.05      inference(resolution,[status(thm)],[c_17,c_6]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_399,plain,
% 3.71/1.05      ( r1_tarski(k2_relat_1(X0),X2)
% 3.71/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.71/1.05      inference(global_propositional_subsumption,[status(thm)],[c_395,c_16]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_400,plain,
% 3.71/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.71/1.05      | r1_tarski(k2_relat_1(X0),X2) ),
% 3.71/1.05      inference(renaming,[status(thm)],[c_399]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_778,plain,
% 3.71/1.05      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.71/1.05      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.71/1.05      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
% 3.71/1.05      inference(forward_subsumption_resolution,
% 3.71/1.05                [status(thm)],
% 3.71/1.05                [c_766,c_16,c_400]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_2032,plain,
% 3.71/1.05      ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 3.71/1.05      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.71/1.05      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.71/1.05      inference(predicate_to_equality,[status(thm)],[c_778]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_782,plain,
% 3.71/1.05      ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 3.71/1.05      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.71/1.05      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.71/1.05      inference(predicate_to_equality,[status(thm)],[c_778]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_2468,plain,
% 3.71/1.05      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.71/1.05      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.71/1.05      | ~ v1_funct_1(sK3) ),
% 3.71/1.05      inference(instantiation,[status(thm)],[c_2399]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_2469,plain,
% 3.71/1.05      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.71/1.05      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) = iProver_top
% 3.71/1.05      | v1_funct_1(sK3) != iProver_top ),
% 3.71/1.05      inference(predicate_to_equality,[status(thm)],[c_2468]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_2625,plain,
% 3.71/1.05      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.71/1.05      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
% 3.71/1.05      inference(global_propositional_subsumption,
% 3.71/1.05                [status(thm)],
% 3.71/1.05                [c_2032,c_38,c_40,c_782,c_2469]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_2626,plain,
% 3.71/1.05      ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 3.71/1.05      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.71/1.05      inference(renaming,[status(thm)],[c_2625]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_5318,plain,
% 3.71/1.05      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 3.71/1.05      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.71/1.05      inference(demodulation,[status(thm)],[c_5313,c_2626]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_5452,plain,
% 3.71/1.05      ( sK1 = k1_xboole_0
% 3.71/1.05      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.71/1.05      inference(superposition,[status(thm)],[c_4556,c_5318]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_5736,plain,
% 3.71/1.05      ( sK1 = k1_xboole_0
% 3.71/1.05      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top ),
% 3.71/1.05      inference(superposition,[status(thm)],[c_5725,c_5452]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_26,plain,
% 3.71/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.71/1.05      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.71/1.05      | ~ v1_funct_1(X0) ),
% 3.71/1.05      inference(cnf_transformation,[],[f81]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_2049,plain,
% 3.71/1.05      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.71/1.05      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 3.71/1.05      | v1_funct_1(X0) != iProver_top ),
% 3.71/1.05      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_5371,plain,
% 3.71/1.05      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 3.71/1.05      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.71/1.05      | v1_funct_1(sK3) != iProver_top ),
% 3.71/1.05      inference(superposition,[status(thm)],[c_5313,c_2049]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_5531,plain,
% 3.71/1.05      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.71/1.05      inference(global_propositional_subsumption,
% 3.71/1.05                [status(thm)],
% 3.71/1.05                [c_5371,c_38,c_40]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_2041,plain,
% 3.71/1.05      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.71/1.05      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 3.71/1.05      inference(predicate_to_equality,[status(thm)],[c_400]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_5544,plain,
% 3.71/1.05      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) = iProver_top ),
% 3.71/1.05      inference(superposition,[status(thm)],[c_5531,c_2041]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_6268,plain,
% 3.71/1.05      ( sK1 = k1_xboole_0 ),
% 3.71/1.05      inference(forward_subsumption_resolution,[status(thm)],[c_5736,c_5544]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_6273,plain,
% 3.71/1.05      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 3.71/1.05      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
% 3.71/1.05      inference(demodulation,[status(thm)],[c_6268,c_5318]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_9,plain,
% 3.71/1.05      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.71/1.05      inference(cnf_transformation,[],[f62]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_10,plain,
% 3.71/1.05      ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.71/1.05      inference(cnf_transformation,[],[f64]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_15,plain,
% 3.71/1.05      ( v1_relat_1(k6_relat_1(X0)) ),
% 3.71/1.05      inference(cnf_transformation,[],[f68]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_2053,plain,
% 3.71/1.05      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 3.71/1.05      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_2729,plain,
% 3.71/1.05      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.71/1.05      inference(superposition,[status(thm)],[c_10,c_2053]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_12,plain,
% 3.71/1.05      ( ~ v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0 ),
% 3.71/1.05      inference(cnf_transformation,[],[f66]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_2056,plain,
% 3.71/1.05      ( k7_relat_1(X0,k1_relat_1(X0)) = X0 | v1_relat_1(X0) != iProver_top ),
% 3.71/1.05      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_2952,plain,
% 3.71/1.05      ( k7_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0)) = k1_xboole_0 ),
% 3.71/1.05      inference(superposition,[status(thm)],[c_2729,c_2056]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_2954,plain,
% 3.71/1.05      ( k7_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.71/1.05      inference(light_normalisation,[status(thm)],[c_2952,c_9]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_33,negated_conjecture,
% 3.71/1.05      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 3.71/1.05      inference(cnf_transformation,[],[f90]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_6285,plain,
% 3.71/1.05      ( sK0 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.71/1.05      inference(demodulation,[status(thm)],[c_6268,c_33]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_6286,plain,
% 3.71/1.05      ( sK0 = k1_xboole_0 ),
% 3.71/1.05      inference(equality_resolution_simp,[status(thm)],[c_6285]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_6417,plain,
% 3.71/1.05      ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
% 3.71/1.05      inference(demodulation,[status(thm)],[c_6286,c_2045]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_2,plain,
% 3.71/1.05      ( r1_xboole_0(X0,k1_xboole_0) ),
% 3.71/1.05      inference(cnf_transformation,[],[f56]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_3,plain,
% 3.71/1.05      ( ~ r1_tarski(X0,X1) | ~ r1_xboole_0(X0,X1) | v1_xboole_0(X0) ),
% 3.71/1.05      inference(cnf_transformation,[],[f57]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_382,plain,
% 3.71/1.05      ( ~ r1_tarski(X0,X1) | v1_xboole_0(X0) | X0 != X2 | k1_xboole_0 != X1 ),
% 3.71/1.05      inference(resolution_lifted,[status(thm)],[c_2,c_3]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_383,plain,
% 3.71/1.05      ( ~ r1_tarski(X0,k1_xboole_0) | v1_xboole_0(X0) ),
% 3.71/1.05      inference(unflattening,[status(thm)],[c_382]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_2042,plain,
% 3.71/1.05      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 3.71/1.05      | v1_xboole_0(X0) = iProver_top ),
% 3.71/1.05      inference(predicate_to_equality,[status(thm)],[c_383]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_6436,plain,
% 3.71/1.05      ( v1_xboole_0(sK2) = iProver_top ),
% 3.71/1.05      inference(superposition,[status(thm)],[c_6417,c_2042]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_1,plain,
% 3.71/1.05      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.71/1.05      inference(cnf_transformation,[],[f55]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_2060,plain,
% 3.71/1.05      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.71/1.05      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_7015,plain,
% 3.71/1.05      ( sK2 = k1_xboole_0 ),
% 3.71/1.05      inference(superposition,[status(thm)],[c_6436,c_2060]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_18,plain,
% 3.71/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.71/1.05      | ~ v1_xboole_0(X1)
% 3.71/1.05      | v1_xboole_0(X0) ),
% 3.71/1.05      inference(cnf_transformation,[],[f72]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_2051,plain,
% 3.71/1.05      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.71/1.05      | v1_xboole_0(X1) != iProver_top
% 3.71/1.05      | v1_xboole_0(X0) = iProver_top ),
% 3.71/1.05      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_3407,plain,
% 3.71/1.05      ( v1_xboole_0(sK3) = iProver_top | v1_xboole_0(sK0) != iProver_top ),
% 3.71/1.05      inference(superposition,[status(thm)],[c_2044,c_2051]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_6416,plain,
% 3.71/1.05      ( v1_xboole_0(sK3) = iProver_top
% 3.71/1.05      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.71/1.05      inference(demodulation,[status(thm)],[c_6286,c_3407]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_121,plain,
% 3.71/1.05      ( ~ v1_xboole_0(k1_xboole_0) | k1_xboole_0 = k1_xboole_0 ),
% 3.71/1.05      inference(instantiation,[status(thm)],[c_1]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_0,plain,
% 3.71/1.05      ( v1_xboole_0(k1_xboole_0) ),
% 3.71/1.05      inference(cnf_transformation,[],[f54]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_123,plain,
% 3.71/1.05      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.71/1.05      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_1487,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_2371,plain,
% 3.71/1.05      ( sK0 != X0 | sK0 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 3.71/1.05      inference(instantiation,[status(thm)],[c_1487]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_2514,plain,
% 3.71/1.05      ( sK0 != sK0 | sK0 = k1_xboole_0 | k1_xboole_0 != sK0 ),
% 3.71/1.05      inference(instantiation,[status(thm)],[c_2371]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_1486,plain,( X0 = X0 ),theory(equality) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_2515,plain,
% 3.71/1.05      ( sK0 = sK0 ),
% 3.71/1.05      inference(instantiation,[status(thm)],[c_1486]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_2687,plain,
% 3.71/1.05      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 3.71/1.05      inference(instantiation,[status(thm)],[c_1487]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_2688,plain,
% 3.71/1.05      ( sK1 != k1_xboole_0 | k1_xboole_0 = sK1 | k1_xboole_0 != k1_xboole_0 ),
% 3.71/1.05      inference(instantiation,[status(thm)],[c_2687]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_1488,plain,
% 3.71/1.05      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.71/1.05      theory(equality) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_2987,plain,
% 3.71/1.05      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK0) | sK0 != X0 ),
% 3.71/1.05      inference(instantiation,[status(thm)],[c_1488]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_2988,plain,
% 3.71/1.05      ( sK0 != X0
% 3.71/1.05      | v1_xboole_0(X0) != iProver_top
% 3.71/1.05      | v1_xboole_0(sK0) = iProver_top ),
% 3.71/1.05      inference(predicate_to_equality,[status(thm)],[c_2987]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_2990,plain,
% 3.71/1.05      ( sK0 != k1_xboole_0
% 3.71/1.05      | v1_xboole_0(sK0) = iProver_top
% 3.71/1.05      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.71/1.05      inference(instantiation,[status(thm)],[c_2988]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_7343,plain,
% 3.71/1.05      ( v1_xboole_0(sK3) = iProver_top ),
% 3.71/1.05      inference(global_propositional_subsumption,
% 3.71/1.05                [status(thm)],
% 3.71/1.05                [c_6416,c_33,c_121,c_0,c_123,c_2514,c_2515,c_2688,c_2990,
% 3.71/1.05                 c_3407,c_6268]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_7349,plain,
% 3.71/1.05      ( sK3 = k1_xboole_0 ),
% 3.71/1.05      inference(superposition,[status(thm)],[c_7343,c_2060]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_8214,plain,
% 3.71/1.05      ( k1_xboole_0 != k1_xboole_0
% 3.71/1.05      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 3.71/1.05      inference(light_normalisation,
% 3.71/1.05                [status(thm)],
% 3.71/1.05                [c_6273,c_9,c_2954,c_7015,c_7349]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_8215,plain,
% 3.71/1.05      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 3.71/1.05      inference(equality_resolution_simp,[status(thm)],[c_8214]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_4,plain,
% 3.71/1.05      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.71/1.05      inference(cnf_transformation,[],[f58]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_2059,plain,
% 3.71/1.05      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.71/1.05      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.71/1.05  
% 3.71/1.05  cnf(c_8217,plain,
% 3.71/1.05      ( $false ),
% 3.71/1.05      inference(forward_subsumption_resolution,[status(thm)],[c_8215,c_2059]) ).
% 3.71/1.05  
% 3.71/1.05  
% 3.71/1.05  % SZS output end CNFRefutation for theBenchmark.p
% 3.71/1.05  
% 3.71/1.05  ------                               Statistics
% 3.71/1.05  
% 3.71/1.05  ------ General
% 3.71/1.05  
% 3.71/1.05  abstr_ref_over_cycles:                  0
% 3.71/1.05  abstr_ref_under_cycles:                 0
% 3.71/1.05  gc_basic_clause_elim:                   0
% 3.71/1.05  forced_gc_time:                         0
% 3.71/1.05  parsing_time:                           0.013
% 3.71/1.05  unif_index_cands_time:                  0.
% 3.71/1.05  unif_index_add_time:                    0.
% 3.71/1.05  orderings_time:                         0.
% 3.71/1.05  out_proof_time:                         0.011
% 3.71/1.05  total_time:                             0.292
% 3.71/1.05  num_of_symbols:                         52
% 3.71/1.05  num_of_terms:                           6286
% 3.71/1.05  
% 3.71/1.05  ------ Preprocessing
% 3.71/1.05  
% 3.71/1.05  num_of_splits:                          0
% 3.71/1.05  num_of_split_atoms:                     0
% 3.71/1.05  num_of_reused_defs:                     0
% 3.71/1.05  num_eq_ax_congr_red:                    8
% 3.71/1.05  num_of_sem_filtered_clauses:            1
% 3.71/1.05  num_of_subtypes:                        0
% 3.71/1.05  monotx_restored_types:                  0
% 3.71/1.05  sat_num_of_epr_types:                   0
% 3.71/1.05  sat_num_of_non_cyclic_types:            0
% 3.71/1.05  sat_guarded_non_collapsed_types:        0
% 3.71/1.05  num_pure_diseq_elim:                    0
% 3.71/1.05  simp_replaced_by:                       0
% 3.71/1.05  res_preprocessed:                       176
% 3.71/1.05  prep_upred:                             0
% 3.71/1.05  prep_unflattend:                        77
% 3.71/1.05  smt_new_axioms:                         0
% 3.71/1.05  pred_elim_cands:                        5
% 3.71/1.05  pred_elim:                              3
% 3.71/1.05  pred_elim_cl:                           1
% 3.71/1.05  pred_elim_cycles:                       6
% 3.71/1.05  merged_defs:                            0
% 3.71/1.05  merged_defs_ncl:                        0
% 3.71/1.05  bin_hyper_res:                          0
% 3.71/1.05  prep_cycles:                            4
% 3.71/1.05  pred_elim_time:                         0.03
% 3.71/1.05  splitting_time:                         0.
% 3.71/1.05  sem_filter_time:                        0.
% 3.71/1.05  monotx_time:                            0.001
% 3.71/1.05  subtype_inf_time:                       0.
% 3.71/1.05  
% 3.71/1.05  ------ Problem properties
% 3.71/1.05  
% 3.71/1.05  clauses:                                36
% 3.71/1.05  conjectures:                            4
% 3.71/1.05  epr:                                    7
% 3.71/1.05  horn:                                   32
% 3.71/1.05  ground:                                 16
% 3.71/1.05  unary:                                  10
% 3.71/1.05  binary:                                 10
% 3.71/1.05  lits:                                   91
% 3.71/1.05  lits_eq:                                33
% 3.71/1.05  fd_pure:                                0
% 3.71/1.05  fd_pseudo:                              0
% 3.71/1.05  fd_cond:                                3
% 3.71/1.05  fd_pseudo_cond:                         0
% 3.71/1.05  ac_symbols:                             0
% 3.71/1.05  
% 3.71/1.05  ------ Propositional Solver
% 3.71/1.05  
% 3.71/1.05  prop_solver_calls:                      28
% 3.71/1.05  prop_fast_solver_calls:                 1346
% 3.71/1.05  smt_solver_calls:                       0
% 3.71/1.05  smt_fast_solver_calls:                  0
% 3.71/1.05  prop_num_of_clauses:                    2895
% 3.71/1.05  prop_preprocess_simplified:             7779
% 3.71/1.05  prop_fo_subsumed:                       30
% 3.71/1.05  prop_solver_time:                       0.
% 3.71/1.05  smt_solver_time:                        0.
% 3.71/1.05  smt_fast_solver_time:                   0.
% 3.71/1.05  prop_fast_solver_time:                  0.
% 3.71/1.05  prop_unsat_core_time:                   0.
% 3.71/1.05  
% 3.71/1.05  ------ QBF
% 3.71/1.05  
% 3.71/1.05  qbf_q_res:                              0
% 3.71/1.05  qbf_num_tautologies:                    0
% 3.71/1.05  qbf_prep_cycles:                        0
% 3.71/1.05  
% 3.71/1.05  ------ BMC1
% 3.71/1.05  
% 3.71/1.05  bmc1_current_bound:                     -1
% 3.71/1.05  bmc1_last_solved_bound:                 -1
% 3.71/1.05  bmc1_unsat_core_size:                   -1
% 3.71/1.05  bmc1_unsat_core_parents_size:           -1
% 3.71/1.05  bmc1_merge_next_fun:                    0
% 3.71/1.05  bmc1_unsat_core_clauses_time:           0.
% 3.71/1.05  
% 3.71/1.05  ------ Instantiation
% 3.71/1.05  
% 3.71/1.05  inst_num_of_clauses:                    858
% 3.71/1.05  inst_num_in_passive:                    427
% 3.71/1.05  inst_num_in_active:                     432
% 3.71/1.05  inst_num_in_unprocessed:                0
% 3.71/1.05  inst_num_of_loops:                      520
% 3.71/1.05  inst_num_of_learning_restarts:          0
% 3.71/1.05  inst_num_moves_active_passive:          85
% 3.71/1.05  inst_lit_activity:                      0
% 3.71/1.05  inst_lit_activity_moves:                0
% 3.71/1.05  inst_num_tautologies:                   0
% 3.71/1.05  inst_num_prop_implied:                  0
% 3.71/1.05  inst_num_existing_simplified:           0
% 3.71/1.05  inst_num_eq_res_simplified:             0
% 3.71/1.05  inst_num_child_elim:                    0
% 3.71/1.05  inst_num_of_dismatching_blockings:      288
% 3.71/1.05  inst_num_of_non_proper_insts:           641
% 3.71/1.05  inst_num_of_duplicates:                 0
% 3.71/1.05  inst_inst_num_from_inst_to_res:         0
% 3.71/1.05  inst_dismatching_checking_time:         0.
% 3.71/1.05  
% 3.71/1.05  ------ Resolution
% 3.71/1.05  
% 3.71/1.05  res_num_of_clauses:                     0
% 3.71/1.05  res_num_in_passive:                     0
% 3.71/1.05  res_num_in_active:                      0
% 3.71/1.05  res_num_of_loops:                       180
% 3.71/1.05  res_forward_subset_subsumed:            46
% 3.71/1.05  res_backward_subset_subsumed:           2
% 3.71/1.05  res_forward_subsumed:                   0
% 3.71/1.05  res_backward_subsumed:                  0
% 3.71/1.05  res_forward_subsumption_resolution:     6
% 3.71/1.05  res_backward_subsumption_resolution:    0
% 3.71/1.05  res_clause_to_clause_subsumption:       317
% 3.71/1.05  res_orphan_elimination:                 0
% 3.71/1.05  res_tautology_del:                      127
% 3.71/1.05  res_num_eq_res_simplified:              1
% 3.71/1.05  res_num_sel_changes:                    0
% 3.71/1.05  res_moves_from_active_to_pass:          0
% 3.71/1.05  
% 3.71/1.05  ------ Superposition
% 3.71/1.05  
% 3.71/1.05  sup_time_total:                         0.
% 3.71/1.05  sup_time_generating:                    0.
% 3.71/1.05  sup_time_sim_full:                      0.
% 3.71/1.05  sup_time_sim_immed:                     0.
% 3.71/1.05  
% 3.71/1.05  sup_num_of_clauses:                     112
% 3.71/1.05  sup_num_in_active:                      48
% 3.71/1.05  sup_num_in_passive:                     64
% 3.71/1.05  sup_num_of_loops:                       102
% 3.71/1.05  sup_fw_superposition:                   81
% 3.71/1.05  sup_bw_superposition:                   104
% 3.71/1.05  sup_immediate_simplified:               51
% 3.71/1.05  sup_given_eliminated:                   2
% 3.71/1.05  comparisons_done:                       0
% 3.71/1.05  comparisons_avoided:                    25
% 3.71/1.05  
% 3.71/1.05  ------ Simplifications
% 3.71/1.05  
% 3.71/1.05  
% 3.71/1.05  sim_fw_subset_subsumed:                 23
% 3.71/1.05  sim_bw_subset_subsumed:                 15
% 3.71/1.05  sim_fw_subsumed:                        10
% 3.71/1.05  sim_bw_subsumed:                        0
% 3.71/1.05  sim_fw_subsumption_res:                 7
% 3.71/1.05  sim_bw_subsumption_res:                 0
% 3.71/1.05  sim_tautology_del:                      9
% 3.71/1.05  sim_eq_tautology_del:                   17
% 3.71/1.05  sim_eq_res_simp:                        4
% 3.71/1.05  sim_fw_demodulated:                     2
% 3.71/1.05  sim_bw_demodulated:                     49
% 3.71/1.05  sim_light_normalised:                   33
% 3.71/1.05  sim_joinable_taut:                      0
% 3.71/1.05  sim_joinable_simp:                      0
% 3.71/1.05  sim_ac_normalised:                      0
% 3.71/1.05  sim_smt_subsumption:                    0
% 3.71/1.05  
%------------------------------------------------------------------------------
