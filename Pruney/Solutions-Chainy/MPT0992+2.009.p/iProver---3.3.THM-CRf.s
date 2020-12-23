%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:47 EST 2020

% Result     : Theorem 3.75s
% Output     : CNFRefutation 3.75s
% Verified   : 
% Statistics : Number of formulae       :  239 (10542 expanded)
%              Number of clauses        :  162 (3675 expanded)
%              Number of leaves         :   19 (1937 expanded)
%              Depth                    :   27
%              Number of atoms          :  729 (54947 expanded)
%              Number of equality atoms :  390 (14562 expanded)
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

fof(f42,plain,(
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
    inference(flattening,[],[f42])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f43,f49])).

fof(f84,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f50])).

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

fof(f34,plain,(
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

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

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
    inference(nnf_transformation,[],[f35])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f82,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f83,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f50])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f40])).

fof(f80,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f81,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f86,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f50])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f85,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f50])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f93,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f70])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f44])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f88,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f54])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f89,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f74])).

fof(f90,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f89])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f87,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f55])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f2,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f52,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f92,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f72])).

cnf(c_32,negated_conjecture,
    ( r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1684,plain,
    ( r1_tarski(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_645,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X0
    | sK1 != X2
    | sK0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_34])).

cnf(c_646,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_645])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_648,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_646,c_33])).

cnf(c_1683,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1689,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3497,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1683,c_1689])).

cnf(c_3627,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_648,c_3497])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1692,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4239,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3627,c_1692])).

cnf(c_38,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1970,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1971,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1970])).

cnf(c_4855,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | sK1 = k1_xboole_0
    | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4239,c_38,c_1971])).

cnf(c_4856,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4855])).

cnf(c_4865,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1684,c_4856])).

cnf(c_27,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_5838,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4865,c_1685])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1686,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_5047,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1683,c_1686])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2042,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_2269,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_2042])).

cnf(c_5253,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5047,c_35,c_33,c_2269])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1687,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_4265,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1683,c_1687])).

cnf(c_36,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_2014,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(k2_partfun1(X0,X1,sK3,X2))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_2517,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2014])).

cnf(c_2518,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2517])).

cnf(c_4634,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4265,c_36,c_38,c_2518])).

cnf(c_5262,plain,
    ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5253,c_4634])).

cnf(c_6744,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5838,c_5262])).

cnf(c_28,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_30,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_656,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_relat_1(X0)
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_relat_1(X0) != sK2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_30])).

cnf(c_657,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
    inference(unflattening,[status(thm)],[c_656])).

cnf(c_15,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_9,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_444,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_15,c_9])).

cnf(c_448,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_444,c_14])).

cnf(c_449,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_448])).

cnf(c_669,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_657,c_14,c_449])).

cnf(c_1670,plain,
    ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_669])).

cnf(c_5260,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5253,c_1670])).

cnf(c_5276,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5260,c_5262])).

cnf(c_8257,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4865,c_5276])).

cnf(c_8263,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6744,c_8257])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1688,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_6367,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5253,c_1688])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1963,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1964,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1963])).

cnf(c_11,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2065,plain,
    ( r1_tarski(k7_relat_1(sK3,X0),sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2066,plain,
    ( r1_tarski(k7_relat_1(sK3,X0),sK3) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2065])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2054,plain,
    ( r1_tarski(X0,k2_zfmisc_1(sK0,sK1))
    | ~ r1_tarski(X0,sK3)
    | ~ r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2400,plain,
    ( r1_tarski(k7_relat_1(sK3,X0),k2_zfmisc_1(sK0,sK1))
    | ~ r1_tarski(k7_relat_1(sK3,X0),sK3)
    | ~ r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_2054])).

cnf(c_2401,plain,
    ( r1_tarski(k7_relat_1(sK3,X0),k2_zfmisc_1(sK0,sK1)) = iProver_top
    | r1_tarski(k7_relat_1(sK3,X0),sK3) != iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2400])).

cnf(c_5,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_3333,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ r1_tarski(k7_relat_1(sK3,X0),k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3334,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | r1_tarski(k7_relat_1(sK3,X0),k2_zfmisc_1(sK0,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3333])).

cnf(c_6504,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6367,c_38,c_1964,c_1971,c_2066,c_2401,c_3334])).

cnf(c_1690,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_6516,plain,
    ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6504,c_1690])).

cnf(c_1679,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_449])).

cnf(c_6514,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_6504,c_1679])).

cnf(c_11462,plain,
    ( sK1 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8263,c_6516,c_6514])).

cnf(c_11500,plain,
    ( k1_relset_1(sK0,k1_xboole_0,sK3) = k1_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_11462,c_3497])).

cnf(c_31,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_11506,plain,
    ( sK0 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_11462,c_31])).

cnf(c_11507,plain,
    ( sK0 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_11506])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_589,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | sK3 != X0
    | sK1 != X1
    | sK0 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_34])).

cnf(c_590,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_589])).

cnf(c_1673,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_590])).

cnf(c_3,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1776,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1673,c_3])).

cnf(c_11503,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11462,c_1776])).

cnf(c_11514,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11503,c_11507])).

cnf(c_11515,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_11514])).

cnf(c_11505,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11462,c_1683])).

cnf(c_11510,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11505,c_11507])).

cnf(c_11512,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11510,c_3])).

cnf(c_11518,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_11515,c_11512])).

cnf(c_11525,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_11500,c_11507,c_11518])).

cnf(c_12165,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_11525,c_1692])).

cnf(c_12185,plain,
    ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_12165])).

cnf(c_6518,plain,
    ( k1_relset_1(sK0,sK1,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_6504,c_1689])).

cnf(c_11485,plain,
    ( k1_relset_1(sK0,k1_xboole_0,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(demodulation,[status(thm)],[c_11462,c_6518])).

cnf(c_11578,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(light_normalisation,[status(thm)],[c_11485,c_11507])).

cnf(c_11490,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11462,c_6504])).

cnf(c_11559,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11490,c_11507])).

cnf(c_11561,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11559,c_3])).

cnf(c_18,plain,
    ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_473,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK2 != X0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_30])).

cnf(c_474,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_473])).

cnf(c_1678,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_474])).

cnf(c_2,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1869,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1678,c_2])).

cnf(c_2163,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2014])).

cnf(c_2164,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2163])).

cnf(c_2339,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | sK1 != k1_xboole_0
    | sK2 = k1_xboole_0
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1869,c_36,c_38,c_2164])).

cnf(c_2340,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2339])).

cnf(c_5258,plain,
    ( k7_relat_1(sK3,sK2) != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5253,c_2340])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_112,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_113,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2229,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1013,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2019,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(sK2,sK0)
    | X0 != sK2
    | X1 != sK0 ),
    inference(instantiation,[status(thm)],[c_1013])).

cnf(c_2237,plain,
    ( r1_tarski(sK2,X0)
    | ~ r1_tarski(sK2,sK0)
    | X0 != sK0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_2019])).

cnf(c_2240,plain,
    ( ~ r1_tarski(sK2,sK0)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != sK2
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_2237])).

cnf(c_1011,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2238,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1011])).

cnf(c_1012,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2002,plain,
    ( sK2 != X0
    | sK2 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1012])).

cnf(c_2630,plain,
    ( sK2 != sK2
    | sK2 = k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_2002])).

cnf(c_2775,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1012])).

cnf(c_2776,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2775])).

cnf(c_5625,plain,
    ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5258,c_32,c_31,c_112,c_113,c_2229,c_2240,c_2238,c_2630,c_2776,c_4865,c_5276])).

cnf(c_5626,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_5625])).

cnf(c_11493,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11462,c_5626])).

cnf(c_11549,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11493,c_2])).

cnf(c_11563,plain,
    ( sK2 = k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_11561,c_11549])).

cnf(c_20,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_570,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | sK2 != k1_xboole_0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_30])).

cnf(c_571,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_570])).

cnf(c_1674,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_571])).

cnf(c_1882,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1674,c_3])).

cnf(c_2349,plain,
    ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | sK2 != k1_xboole_0
    | k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1882,c_36,c_38,c_2164])).

cnf(c_2350,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2349])).

cnf(c_5257,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k7_relat_1(sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5253,c_2350])).

cnf(c_5634,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k7_relat_1(sK3,sK2)) != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5257,c_5626])).

cnf(c_11492,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,sK2)) != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11462,c_5634])).

cnf(c_11555,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,sK2)) != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11492,c_2])).

cnf(c_11564,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,sK2)) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_11561,c_11555])).

cnf(c_11568,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_11563,c_11564])).

cnf(c_11580,plain,
    ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_11578,c_11568])).

cnf(c_2470,plain,
    ( k2_relat_1(sK3) = k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1011])).

cnf(c_2084,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_relat_1(sK3),sK1)
    | X0 != k2_relat_1(sK3)
    | X1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1013])).

cnf(c_2469,plain,
    ( r1_tarski(k2_relat_1(sK3),X0)
    | ~ r1_tarski(k2_relat_1(sK3),sK1)
    | X0 != sK1
    | k2_relat_1(sK3) != k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2084])).

cnf(c_2472,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK1)
    | r1_tarski(k2_relat_1(sK3),k1_xboole_0)
    | k2_relat_1(sK3) != k2_relat_1(sK3)
    | k1_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_2469])).

cnf(c_2461,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k1_xboole_0)
    | k1_xboole_0 = k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2093,plain,
    ( X0 != k2_relat_1(sK3)
    | X1 != sK1
    | r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k2_relat_1(sK3),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2084])).

cnf(c_2095,plain,
    ( k1_xboole_0 != k2_relat_1(sK3)
    | k1_xboole_0 != sK1
    | r1_tarski(k2_relat_1(sK3),sK1) != iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2093])).

cnf(c_1983,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | r1_tarski(k2_relat_1(sK3),sK1) ),
    inference(instantiation,[status(thm)],[c_449])).

cnf(c_1984,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | r1_tarski(k2_relat_1(sK3),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1983])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12185,c_11580,c_11462,c_2776,c_2470,c_2472,c_2461,c_2095,c_1984,c_1983,c_1971,c_113,c_112,c_38,c_33])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:21:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.75/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.75/1.00  
% 3.75/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.75/1.00  
% 3.75/1.00  ------  iProver source info
% 3.75/1.00  
% 3.75/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.75/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.75/1.00  git: non_committed_changes: false
% 3.75/1.00  git: last_make_outside_of_git: false
% 3.75/1.00  
% 3.75/1.00  ------ 
% 3.75/1.00  
% 3.75/1.00  ------ Input Options
% 3.75/1.00  
% 3.75/1.00  --out_options                           all
% 3.75/1.00  --tptp_safe_out                         true
% 3.75/1.00  --problem_path                          ""
% 3.75/1.00  --include_path                          ""
% 3.75/1.00  --clausifier                            res/vclausify_rel
% 3.75/1.00  --clausifier_options                    --mode clausify
% 3.75/1.00  --stdin                                 false
% 3.75/1.00  --stats_out                             all
% 3.75/1.00  
% 3.75/1.00  ------ General Options
% 3.75/1.00  
% 3.75/1.00  --fof                                   false
% 3.75/1.00  --time_out_real                         305.
% 3.75/1.00  --time_out_virtual                      -1.
% 3.75/1.00  --symbol_type_check                     false
% 3.75/1.00  --clausify_out                          false
% 3.75/1.00  --sig_cnt_out                           false
% 3.75/1.00  --trig_cnt_out                          false
% 3.75/1.00  --trig_cnt_out_tolerance                1.
% 3.75/1.00  --trig_cnt_out_sk_spl                   false
% 3.75/1.00  --abstr_cl_out                          false
% 3.75/1.00  
% 3.75/1.00  ------ Global Options
% 3.75/1.00  
% 3.75/1.00  --schedule                              default
% 3.75/1.00  --add_important_lit                     false
% 3.75/1.00  --prop_solver_per_cl                    1000
% 3.75/1.00  --min_unsat_core                        false
% 3.75/1.00  --soft_assumptions                      false
% 3.75/1.00  --soft_lemma_size                       3
% 3.75/1.00  --prop_impl_unit_size                   0
% 3.75/1.00  --prop_impl_unit                        []
% 3.75/1.00  --share_sel_clauses                     true
% 3.75/1.00  --reset_solvers                         false
% 3.75/1.00  --bc_imp_inh                            [conj_cone]
% 3.75/1.00  --conj_cone_tolerance                   3.
% 3.75/1.00  --extra_neg_conj                        none
% 3.75/1.00  --large_theory_mode                     true
% 3.75/1.00  --prolific_symb_bound                   200
% 3.75/1.00  --lt_threshold                          2000
% 3.75/1.00  --clause_weak_htbl                      true
% 3.75/1.00  --gc_record_bc_elim                     false
% 3.75/1.00  
% 3.75/1.00  ------ Preprocessing Options
% 3.75/1.00  
% 3.75/1.00  --preprocessing_flag                    true
% 3.75/1.00  --time_out_prep_mult                    0.1
% 3.75/1.00  --splitting_mode                        input
% 3.75/1.00  --splitting_grd                         true
% 3.75/1.00  --splitting_cvd                         false
% 3.75/1.00  --splitting_cvd_svl                     false
% 3.75/1.00  --splitting_nvd                         32
% 3.75/1.00  --sub_typing                            true
% 3.75/1.00  --prep_gs_sim                           true
% 3.75/1.00  --prep_unflatten                        true
% 3.75/1.00  --prep_res_sim                          true
% 3.75/1.00  --prep_upred                            true
% 3.75/1.00  --prep_sem_filter                       exhaustive
% 3.75/1.00  --prep_sem_filter_out                   false
% 3.75/1.00  --pred_elim                             true
% 3.75/1.00  --res_sim_input                         true
% 3.75/1.00  --eq_ax_congr_red                       true
% 3.75/1.00  --pure_diseq_elim                       true
% 3.75/1.00  --brand_transform                       false
% 3.75/1.00  --non_eq_to_eq                          false
% 3.75/1.00  --prep_def_merge                        true
% 3.75/1.00  --prep_def_merge_prop_impl              false
% 3.75/1.00  --prep_def_merge_mbd                    true
% 3.75/1.00  --prep_def_merge_tr_red                 false
% 3.75/1.00  --prep_def_merge_tr_cl                  false
% 3.75/1.00  --smt_preprocessing                     true
% 3.75/1.00  --smt_ac_axioms                         fast
% 3.75/1.00  --preprocessed_out                      false
% 3.75/1.00  --preprocessed_stats                    false
% 3.75/1.00  
% 3.75/1.00  ------ Abstraction refinement Options
% 3.75/1.00  
% 3.75/1.00  --abstr_ref                             []
% 3.75/1.00  --abstr_ref_prep                        false
% 3.75/1.00  --abstr_ref_until_sat                   false
% 3.75/1.00  --abstr_ref_sig_restrict                funpre
% 3.75/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.75/1.00  --abstr_ref_under                       []
% 3.75/1.00  
% 3.75/1.00  ------ SAT Options
% 3.75/1.00  
% 3.75/1.00  --sat_mode                              false
% 3.75/1.00  --sat_fm_restart_options                ""
% 3.75/1.00  --sat_gr_def                            false
% 3.75/1.00  --sat_epr_types                         true
% 3.75/1.00  --sat_non_cyclic_types                  false
% 3.75/1.00  --sat_finite_models                     false
% 3.75/1.00  --sat_fm_lemmas                         false
% 3.75/1.00  --sat_fm_prep                           false
% 3.75/1.00  --sat_fm_uc_incr                        true
% 3.75/1.00  --sat_out_model                         small
% 3.75/1.00  --sat_out_clauses                       false
% 3.75/1.00  
% 3.75/1.00  ------ QBF Options
% 3.75/1.00  
% 3.75/1.00  --qbf_mode                              false
% 3.75/1.00  --qbf_elim_univ                         false
% 3.75/1.00  --qbf_dom_inst                          none
% 3.75/1.00  --qbf_dom_pre_inst                      false
% 3.75/1.00  --qbf_sk_in                             false
% 3.75/1.00  --qbf_pred_elim                         true
% 3.75/1.00  --qbf_split                             512
% 3.75/1.00  
% 3.75/1.00  ------ BMC1 Options
% 3.75/1.00  
% 3.75/1.00  --bmc1_incremental                      false
% 3.75/1.00  --bmc1_axioms                           reachable_all
% 3.75/1.00  --bmc1_min_bound                        0
% 3.75/1.00  --bmc1_max_bound                        -1
% 3.75/1.00  --bmc1_max_bound_default                -1
% 3.75/1.00  --bmc1_symbol_reachability              true
% 3.75/1.00  --bmc1_property_lemmas                  false
% 3.75/1.00  --bmc1_k_induction                      false
% 3.75/1.00  --bmc1_non_equiv_states                 false
% 3.75/1.00  --bmc1_deadlock                         false
% 3.75/1.00  --bmc1_ucm                              false
% 3.75/1.00  --bmc1_add_unsat_core                   none
% 3.75/1.00  --bmc1_unsat_core_children              false
% 3.75/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.75/1.00  --bmc1_out_stat                         full
% 3.75/1.00  --bmc1_ground_init                      false
% 3.75/1.00  --bmc1_pre_inst_next_state              false
% 3.75/1.00  --bmc1_pre_inst_state                   false
% 3.75/1.00  --bmc1_pre_inst_reach_state             false
% 3.75/1.00  --bmc1_out_unsat_core                   false
% 3.75/1.00  --bmc1_aig_witness_out                  false
% 3.75/1.00  --bmc1_verbose                          false
% 3.75/1.00  --bmc1_dump_clauses_tptp                false
% 3.75/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.75/1.00  --bmc1_dump_file                        -
% 3.75/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.75/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.75/1.00  --bmc1_ucm_extend_mode                  1
% 3.75/1.00  --bmc1_ucm_init_mode                    2
% 3.75/1.00  --bmc1_ucm_cone_mode                    none
% 3.75/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.75/1.00  --bmc1_ucm_relax_model                  4
% 3.75/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.75/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.75/1.00  --bmc1_ucm_layered_model                none
% 3.75/1.00  --bmc1_ucm_max_lemma_size               10
% 3.75/1.00  
% 3.75/1.00  ------ AIG Options
% 3.75/1.00  
% 3.75/1.00  --aig_mode                              false
% 3.75/1.00  
% 3.75/1.00  ------ Instantiation Options
% 3.75/1.00  
% 3.75/1.00  --instantiation_flag                    true
% 3.75/1.00  --inst_sos_flag                         false
% 3.75/1.00  --inst_sos_phase                        true
% 3.75/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.75/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.75/1.00  --inst_lit_sel_side                     num_symb
% 3.75/1.00  --inst_solver_per_active                1400
% 3.75/1.00  --inst_solver_calls_frac                1.
% 3.75/1.00  --inst_passive_queue_type               priority_queues
% 3.75/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.75/1.00  --inst_passive_queues_freq              [25;2]
% 3.75/1.00  --inst_dismatching                      true
% 3.75/1.00  --inst_eager_unprocessed_to_passive     true
% 3.75/1.00  --inst_prop_sim_given                   true
% 3.75/1.00  --inst_prop_sim_new                     false
% 3.75/1.00  --inst_subs_new                         false
% 3.75/1.00  --inst_eq_res_simp                      false
% 3.75/1.00  --inst_subs_given                       false
% 3.75/1.00  --inst_orphan_elimination               true
% 3.75/1.00  --inst_learning_loop_flag               true
% 3.75/1.00  --inst_learning_start                   3000
% 3.75/1.00  --inst_learning_factor                  2
% 3.75/1.00  --inst_start_prop_sim_after_learn       3
% 3.75/1.00  --inst_sel_renew                        solver
% 3.75/1.00  --inst_lit_activity_flag                true
% 3.75/1.00  --inst_restr_to_given                   false
% 3.75/1.00  --inst_activity_threshold               500
% 3.75/1.00  --inst_out_proof                        true
% 3.75/1.00  
% 3.75/1.00  ------ Resolution Options
% 3.75/1.00  
% 3.75/1.00  --resolution_flag                       true
% 3.75/1.00  --res_lit_sel                           adaptive
% 3.75/1.00  --res_lit_sel_side                      none
% 3.75/1.00  --res_ordering                          kbo
% 3.75/1.00  --res_to_prop_solver                    active
% 3.75/1.00  --res_prop_simpl_new                    false
% 3.75/1.00  --res_prop_simpl_given                  true
% 3.75/1.00  --res_passive_queue_type                priority_queues
% 3.75/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.75/1.00  --res_passive_queues_freq               [15;5]
% 3.75/1.00  --res_forward_subs                      full
% 3.75/1.00  --res_backward_subs                     full
% 3.75/1.00  --res_forward_subs_resolution           true
% 3.75/1.00  --res_backward_subs_resolution          true
% 3.75/1.00  --res_orphan_elimination                true
% 3.75/1.00  --res_time_limit                        2.
% 3.75/1.00  --res_out_proof                         true
% 3.75/1.00  
% 3.75/1.00  ------ Superposition Options
% 3.75/1.00  
% 3.75/1.00  --superposition_flag                    true
% 3.75/1.00  --sup_passive_queue_type                priority_queues
% 3.75/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.75/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.75/1.00  --demod_completeness_check              fast
% 3.75/1.00  --demod_use_ground                      true
% 3.75/1.00  --sup_to_prop_solver                    passive
% 3.75/1.00  --sup_prop_simpl_new                    true
% 3.75/1.00  --sup_prop_simpl_given                  true
% 3.75/1.00  --sup_fun_splitting                     false
% 3.75/1.00  --sup_smt_interval                      50000
% 3.75/1.00  
% 3.75/1.00  ------ Superposition Simplification Setup
% 3.75/1.00  
% 3.75/1.00  --sup_indices_passive                   []
% 3.75/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.75/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.75/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.75/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.75/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.75/1.00  --sup_full_bw                           [BwDemod]
% 3.75/1.00  --sup_immed_triv                        [TrivRules]
% 3.75/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.75/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.75/1.00  --sup_immed_bw_main                     []
% 3.75/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.75/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.75/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.75/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.75/1.00  
% 3.75/1.00  ------ Combination Options
% 3.75/1.00  
% 3.75/1.00  --comb_res_mult                         3
% 3.75/1.00  --comb_sup_mult                         2
% 3.75/1.00  --comb_inst_mult                        10
% 3.75/1.00  
% 3.75/1.00  ------ Debug Options
% 3.75/1.00  
% 3.75/1.00  --dbg_backtrace                         false
% 3.75/1.00  --dbg_dump_prop_clauses                 false
% 3.75/1.00  --dbg_dump_prop_clauses_file            -
% 3.75/1.00  --dbg_out_stat                          false
% 3.75/1.00  ------ Parsing...
% 3.75/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.75/1.00  
% 3.75/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.75/1.00  
% 3.75/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.75/1.00  
% 3.75/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.75/1.00  ------ Proving...
% 3.75/1.00  ------ Problem Properties 
% 3.75/1.00  
% 3.75/1.00  
% 3.75/1.00  clauses                                 34
% 3.75/1.00  conjectures                             4
% 3.75/1.00  EPR                                     6
% 3.75/1.00  Horn                                    29
% 3.75/1.00  unary                                   5
% 3.75/1.00  binary                                  11
% 3.75/1.00  lits                                    95
% 3.75/1.00  lits eq                                 35
% 3.75/1.00  fd_pure                                 0
% 3.75/1.00  fd_pseudo                               0
% 3.75/1.00  fd_cond                                 4
% 3.75/1.00  fd_pseudo_cond                          0
% 3.75/1.00  AC symbols                              0
% 3.75/1.00  
% 3.75/1.00  ------ Schedule dynamic 5 is on 
% 3.75/1.00  
% 3.75/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.75/1.00  
% 3.75/1.00  
% 3.75/1.00  ------ 
% 3.75/1.00  Current options:
% 3.75/1.00  ------ 
% 3.75/1.00  
% 3.75/1.00  ------ Input Options
% 3.75/1.00  
% 3.75/1.00  --out_options                           all
% 3.75/1.00  --tptp_safe_out                         true
% 3.75/1.00  --problem_path                          ""
% 3.75/1.00  --include_path                          ""
% 3.75/1.00  --clausifier                            res/vclausify_rel
% 3.75/1.00  --clausifier_options                    --mode clausify
% 3.75/1.00  --stdin                                 false
% 3.75/1.00  --stats_out                             all
% 3.75/1.00  
% 3.75/1.00  ------ General Options
% 3.75/1.00  
% 3.75/1.00  --fof                                   false
% 3.75/1.00  --time_out_real                         305.
% 3.75/1.00  --time_out_virtual                      -1.
% 3.75/1.00  --symbol_type_check                     false
% 3.75/1.00  --clausify_out                          false
% 3.75/1.00  --sig_cnt_out                           false
% 3.75/1.00  --trig_cnt_out                          false
% 3.75/1.00  --trig_cnt_out_tolerance                1.
% 3.75/1.00  --trig_cnt_out_sk_spl                   false
% 3.75/1.00  --abstr_cl_out                          false
% 3.75/1.00  
% 3.75/1.00  ------ Global Options
% 3.75/1.00  
% 3.75/1.00  --schedule                              default
% 3.75/1.00  --add_important_lit                     false
% 3.75/1.00  --prop_solver_per_cl                    1000
% 3.75/1.00  --min_unsat_core                        false
% 3.75/1.00  --soft_assumptions                      false
% 3.75/1.00  --soft_lemma_size                       3
% 3.75/1.00  --prop_impl_unit_size                   0
% 3.75/1.00  --prop_impl_unit                        []
% 3.75/1.00  --share_sel_clauses                     true
% 3.75/1.00  --reset_solvers                         false
% 3.75/1.00  --bc_imp_inh                            [conj_cone]
% 3.75/1.00  --conj_cone_tolerance                   3.
% 3.75/1.00  --extra_neg_conj                        none
% 3.75/1.00  --large_theory_mode                     true
% 3.75/1.00  --prolific_symb_bound                   200
% 3.75/1.00  --lt_threshold                          2000
% 3.75/1.00  --clause_weak_htbl                      true
% 3.75/1.00  --gc_record_bc_elim                     false
% 3.75/1.00  
% 3.75/1.00  ------ Preprocessing Options
% 3.75/1.00  
% 3.75/1.00  --preprocessing_flag                    true
% 3.75/1.00  --time_out_prep_mult                    0.1
% 3.75/1.00  --splitting_mode                        input
% 3.75/1.00  --splitting_grd                         true
% 3.75/1.00  --splitting_cvd                         false
% 3.75/1.00  --splitting_cvd_svl                     false
% 3.75/1.00  --splitting_nvd                         32
% 3.75/1.00  --sub_typing                            true
% 3.75/1.00  --prep_gs_sim                           true
% 3.75/1.00  --prep_unflatten                        true
% 3.75/1.00  --prep_res_sim                          true
% 3.75/1.00  --prep_upred                            true
% 3.75/1.00  --prep_sem_filter                       exhaustive
% 3.75/1.00  --prep_sem_filter_out                   false
% 3.75/1.00  --pred_elim                             true
% 3.75/1.00  --res_sim_input                         true
% 3.75/1.00  --eq_ax_congr_red                       true
% 3.75/1.00  --pure_diseq_elim                       true
% 3.75/1.00  --brand_transform                       false
% 3.75/1.00  --non_eq_to_eq                          false
% 3.75/1.00  --prep_def_merge                        true
% 3.75/1.00  --prep_def_merge_prop_impl              false
% 3.75/1.00  --prep_def_merge_mbd                    true
% 3.75/1.00  --prep_def_merge_tr_red                 false
% 3.75/1.00  --prep_def_merge_tr_cl                  false
% 3.75/1.00  --smt_preprocessing                     true
% 3.75/1.00  --smt_ac_axioms                         fast
% 3.75/1.00  --preprocessed_out                      false
% 3.75/1.00  --preprocessed_stats                    false
% 3.75/1.00  
% 3.75/1.00  ------ Abstraction refinement Options
% 3.75/1.00  
% 3.75/1.00  --abstr_ref                             []
% 3.75/1.00  --abstr_ref_prep                        false
% 3.75/1.00  --abstr_ref_until_sat                   false
% 3.75/1.00  --abstr_ref_sig_restrict                funpre
% 3.75/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.75/1.00  --abstr_ref_under                       []
% 3.75/1.00  
% 3.75/1.00  ------ SAT Options
% 3.75/1.00  
% 3.75/1.00  --sat_mode                              false
% 3.75/1.00  --sat_fm_restart_options                ""
% 3.75/1.00  --sat_gr_def                            false
% 3.75/1.00  --sat_epr_types                         true
% 3.75/1.00  --sat_non_cyclic_types                  false
% 3.75/1.00  --sat_finite_models                     false
% 3.75/1.00  --sat_fm_lemmas                         false
% 3.75/1.00  --sat_fm_prep                           false
% 3.75/1.00  --sat_fm_uc_incr                        true
% 3.75/1.00  --sat_out_model                         small
% 3.75/1.00  --sat_out_clauses                       false
% 3.75/1.00  
% 3.75/1.00  ------ QBF Options
% 3.75/1.00  
% 3.75/1.00  --qbf_mode                              false
% 3.75/1.00  --qbf_elim_univ                         false
% 3.75/1.00  --qbf_dom_inst                          none
% 3.75/1.00  --qbf_dom_pre_inst                      false
% 3.75/1.00  --qbf_sk_in                             false
% 3.75/1.00  --qbf_pred_elim                         true
% 3.75/1.00  --qbf_split                             512
% 3.75/1.00  
% 3.75/1.00  ------ BMC1 Options
% 3.75/1.00  
% 3.75/1.00  --bmc1_incremental                      false
% 3.75/1.00  --bmc1_axioms                           reachable_all
% 3.75/1.00  --bmc1_min_bound                        0
% 3.75/1.00  --bmc1_max_bound                        -1
% 3.75/1.00  --bmc1_max_bound_default                -1
% 3.75/1.00  --bmc1_symbol_reachability              true
% 3.75/1.00  --bmc1_property_lemmas                  false
% 3.75/1.00  --bmc1_k_induction                      false
% 3.75/1.00  --bmc1_non_equiv_states                 false
% 3.75/1.00  --bmc1_deadlock                         false
% 3.75/1.00  --bmc1_ucm                              false
% 3.75/1.00  --bmc1_add_unsat_core                   none
% 3.75/1.00  --bmc1_unsat_core_children              false
% 3.75/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.75/1.00  --bmc1_out_stat                         full
% 3.75/1.00  --bmc1_ground_init                      false
% 3.75/1.00  --bmc1_pre_inst_next_state              false
% 3.75/1.00  --bmc1_pre_inst_state                   false
% 3.75/1.00  --bmc1_pre_inst_reach_state             false
% 3.75/1.00  --bmc1_out_unsat_core                   false
% 3.75/1.00  --bmc1_aig_witness_out                  false
% 3.75/1.00  --bmc1_verbose                          false
% 3.75/1.00  --bmc1_dump_clauses_tptp                false
% 3.75/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.75/1.00  --bmc1_dump_file                        -
% 3.75/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.75/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.75/1.00  --bmc1_ucm_extend_mode                  1
% 3.75/1.00  --bmc1_ucm_init_mode                    2
% 3.75/1.00  --bmc1_ucm_cone_mode                    none
% 3.75/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.75/1.00  --bmc1_ucm_relax_model                  4
% 3.75/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.75/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.75/1.00  --bmc1_ucm_layered_model                none
% 3.75/1.00  --bmc1_ucm_max_lemma_size               10
% 3.75/1.00  
% 3.75/1.00  ------ AIG Options
% 3.75/1.00  
% 3.75/1.00  --aig_mode                              false
% 3.75/1.00  
% 3.75/1.00  ------ Instantiation Options
% 3.75/1.00  
% 3.75/1.00  --instantiation_flag                    true
% 3.75/1.00  --inst_sos_flag                         false
% 3.75/1.00  --inst_sos_phase                        true
% 3.75/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.75/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.75/1.00  --inst_lit_sel_side                     none
% 3.75/1.00  --inst_solver_per_active                1400
% 3.75/1.00  --inst_solver_calls_frac                1.
% 3.75/1.00  --inst_passive_queue_type               priority_queues
% 3.75/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.75/1.00  --inst_passive_queues_freq              [25;2]
% 3.75/1.00  --inst_dismatching                      true
% 3.75/1.00  --inst_eager_unprocessed_to_passive     true
% 3.75/1.00  --inst_prop_sim_given                   true
% 3.75/1.00  --inst_prop_sim_new                     false
% 3.75/1.00  --inst_subs_new                         false
% 3.75/1.00  --inst_eq_res_simp                      false
% 3.75/1.00  --inst_subs_given                       false
% 3.75/1.00  --inst_orphan_elimination               true
% 3.75/1.00  --inst_learning_loop_flag               true
% 3.75/1.00  --inst_learning_start                   3000
% 3.75/1.00  --inst_learning_factor                  2
% 3.75/1.00  --inst_start_prop_sim_after_learn       3
% 3.75/1.00  --inst_sel_renew                        solver
% 3.75/1.00  --inst_lit_activity_flag                true
% 3.75/1.00  --inst_restr_to_given                   false
% 3.75/1.00  --inst_activity_threshold               500
% 3.75/1.00  --inst_out_proof                        true
% 3.75/1.00  
% 3.75/1.00  ------ Resolution Options
% 3.75/1.00  
% 3.75/1.00  --resolution_flag                       false
% 3.75/1.00  --res_lit_sel                           adaptive
% 3.75/1.00  --res_lit_sel_side                      none
% 3.75/1.00  --res_ordering                          kbo
% 3.75/1.00  --res_to_prop_solver                    active
% 3.75/1.00  --res_prop_simpl_new                    false
% 3.75/1.00  --res_prop_simpl_given                  true
% 3.75/1.00  --res_passive_queue_type                priority_queues
% 3.75/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.75/1.00  --res_passive_queues_freq               [15;5]
% 3.75/1.00  --res_forward_subs                      full
% 3.75/1.00  --res_backward_subs                     full
% 3.75/1.00  --res_forward_subs_resolution           true
% 3.75/1.00  --res_backward_subs_resolution          true
% 3.75/1.00  --res_orphan_elimination                true
% 3.75/1.00  --res_time_limit                        2.
% 3.75/1.00  --res_out_proof                         true
% 3.75/1.00  
% 3.75/1.00  ------ Superposition Options
% 3.75/1.00  
% 3.75/1.00  --superposition_flag                    true
% 3.75/1.00  --sup_passive_queue_type                priority_queues
% 3.75/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.75/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.75/1.00  --demod_completeness_check              fast
% 3.75/1.00  --demod_use_ground                      true
% 3.75/1.00  --sup_to_prop_solver                    passive
% 3.75/1.00  --sup_prop_simpl_new                    true
% 3.75/1.00  --sup_prop_simpl_given                  true
% 3.75/1.00  --sup_fun_splitting                     false
% 3.75/1.00  --sup_smt_interval                      50000
% 3.75/1.00  
% 3.75/1.00  ------ Superposition Simplification Setup
% 3.75/1.00  
% 3.75/1.00  --sup_indices_passive                   []
% 3.75/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.75/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.75/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.75/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.75/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.75/1.00  --sup_full_bw                           [BwDemod]
% 3.75/1.00  --sup_immed_triv                        [TrivRules]
% 3.75/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.75/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.75/1.00  --sup_immed_bw_main                     []
% 3.75/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.75/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.75/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.75/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.75/1.00  
% 3.75/1.00  ------ Combination Options
% 3.75/1.00  
% 3.75/1.00  --comb_res_mult                         3
% 3.75/1.00  --comb_sup_mult                         2
% 3.75/1.00  --comb_inst_mult                        10
% 3.75/1.00  
% 3.75/1.00  ------ Debug Options
% 3.75/1.00  
% 3.75/1.00  --dbg_backtrace                         false
% 3.75/1.00  --dbg_dump_prop_clauses                 false
% 3.75/1.00  --dbg_dump_prop_clauses_file            -
% 3.75/1.00  --dbg_out_stat                          false
% 3.75/1.00  
% 3.75/1.00  
% 3.75/1.00  
% 3.75/1.00  
% 3.75/1.00  ------ Proving...
% 3.75/1.00  
% 3.75/1.00  
% 3.75/1.00  % SZS status Theorem for theBenchmark.p
% 3.75/1.00  
% 3.75/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.75/1.00  
% 3.75/1.00  fof(f18,conjecture,(
% 3.75/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.75/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/1.00  
% 3.75/1.00  fof(f19,negated_conjecture,(
% 3.75/1.00    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.75/1.00    inference(negated_conjecture,[],[f18])).
% 3.75/1.00  
% 3.75/1.00  fof(f42,plain,(
% 3.75/1.00    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.75/1.00    inference(ennf_transformation,[],[f19])).
% 3.75/1.00  
% 3.75/1.00  fof(f43,plain,(
% 3.75/1.00    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.75/1.00    inference(flattening,[],[f42])).
% 3.75/1.00  
% 3.75/1.00  fof(f49,plain,(
% 3.75/1.00    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 3.75/1.00    introduced(choice_axiom,[])).
% 3.75/1.00  
% 3.75/1.00  fof(f50,plain,(
% 3.75/1.00    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 3.75/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f43,f49])).
% 3.75/1.00  
% 3.75/1.00  fof(f84,plain,(
% 3.75/1.00    r1_tarski(sK2,sK0)),
% 3.75/1.00    inference(cnf_transformation,[],[f50])).
% 3.75/1.00  
% 3.75/1.00  fof(f14,axiom,(
% 3.75/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.75/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/1.00  
% 3.75/1.00  fof(f34,plain,(
% 3.75/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.75/1.00    inference(ennf_transformation,[],[f14])).
% 3.75/1.00  
% 3.75/1.00  fof(f35,plain,(
% 3.75/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.75/1.00    inference(flattening,[],[f34])).
% 3.75/1.00  
% 3.75/1.00  fof(f48,plain,(
% 3.75/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.75/1.00    inference(nnf_transformation,[],[f35])).
% 3.75/1.00  
% 3.75/1.00  fof(f69,plain,(
% 3.75/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.75/1.00    inference(cnf_transformation,[],[f48])).
% 3.75/1.00  
% 3.75/1.00  fof(f82,plain,(
% 3.75/1.00    v1_funct_2(sK3,sK0,sK1)),
% 3.75/1.00    inference(cnf_transformation,[],[f50])).
% 3.75/1.00  
% 3.75/1.00  fof(f83,plain,(
% 3.75/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.75/1.00    inference(cnf_transformation,[],[f50])).
% 3.75/1.00  
% 3.75/1.00  fof(f13,axiom,(
% 3.75/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.75/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/1.00  
% 3.75/1.00  fof(f33,plain,(
% 3.75/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.75/1.00    inference(ennf_transformation,[],[f13])).
% 3.75/1.00  
% 3.75/1.00  fof(f68,plain,(
% 3.75/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.75/1.00    inference(cnf_transformation,[],[f33])).
% 3.75/1.00  
% 3.75/1.00  fof(f9,axiom,(
% 3.75/1.00    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 3.75/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/1.00  
% 3.75/1.00  fof(f28,plain,(
% 3.75/1.00    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 3.75/1.00    inference(ennf_transformation,[],[f9])).
% 3.75/1.00  
% 3.75/1.00  fof(f29,plain,(
% 3.75/1.00    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.75/1.00    inference(flattening,[],[f28])).
% 3.75/1.00  
% 3.75/1.00  fof(f63,plain,(
% 3.75/1.00    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.75/1.00    inference(cnf_transformation,[],[f29])).
% 3.75/1.00  
% 3.75/1.00  fof(f11,axiom,(
% 3.75/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.75/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/1.00  
% 3.75/1.00  fof(f31,plain,(
% 3.75/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.75/1.00    inference(ennf_transformation,[],[f11])).
% 3.75/1.00  
% 3.75/1.00  fof(f65,plain,(
% 3.75/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.75/1.00    inference(cnf_transformation,[],[f31])).
% 3.75/1.00  
% 3.75/1.00  fof(f17,axiom,(
% 3.75/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 3.75/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/1.00  
% 3.75/1.00  fof(f40,plain,(
% 3.75/1.00    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.75/1.00    inference(ennf_transformation,[],[f17])).
% 3.75/1.00  
% 3.75/1.00  fof(f41,plain,(
% 3.75/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.75/1.00    inference(flattening,[],[f40])).
% 3.75/1.00  
% 3.75/1.00  fof(f80,plain,(
% 3.75/1.00    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.75/1.00    inference(cnf_transformation,[],[f41])).
% 3.75/1.00  
% 3.75/1.00  fof(f16,axiom,(
% 3.75/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 3.75/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/1.00  
% 3.75/1.00  fof(f38,plain,(
% 3.75/1.00    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.75/1.00    inference(ennf_transformation,[],[f16])).
% 3.75/1.00  
% 3.75/1.00  fof(f39,plain,(
% 3.75/1.00    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.75/1.00    inference(flattening,[],[f38])).
% 3.75/1.00  
% 3.75/1.00  fof(f77,plain,(
% 3.75/1.00    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.75/1.00    inference(cnf_transformation,[],[f39])).
% 3.75/1.00  
% 3.75/1.00  fof(f81,plain,(
% 3.75/1.00    v1_funct_1(sK3)),
% 3.75/1.00    inference(cnf_transformation,[],[f50])).
% 3.75/1.00  
% 3.75/1.00  fof(f15,axiom,(
% 3.75/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 3.75/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/1.00  
% 3.75/1.00  fof(f36,plain,(
% 3.75/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.75/1.00    inference(ennf_transformation,[],[f15])).
% 3.75/1.00  
% 3.75/1.00  fof(f37,plain,(
% 3.75/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.75/1.00    inference(flattening,[],[f36])).
% 3.75/1.00  
% 3.75/1.00  fof(f75,plain,(
% 3.75/1.00    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.75/1.00    inference(cnf_transformation,[],[f37])).
% 3.75/1.00  
% 3.75/1.00  fof(f79,plain,(
% 3.75/1.00    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.75/1.00    inference(cnf_transformation,[],[f41])).
% 3.75/1.00  
% 3.75/1.00  fof(f86,plain,(
% 3.75/1.00    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 3.75/1.00    inference(cnf_transformation,[],[f50])).
% 3.75/1.00  
% 3.75/1.00  fof(f12,axiom,(
% 3.75/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.75/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/1.00  
% 3.75/1.00  fof(f32,plain,(
% 3.75/1.00    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.75/1.00    inference(ennf_transformation,[],[f12])).
% 3.75/1.00  
% 3.75/1.00  fof(f67,plain,(
% 3.75/1.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.75/1.00    inference(cnf_transformation,[],[f32])).
% 3.75/1.00  
% 3.75/1.00  fof(f6,axiom,(
% 3.75/1.00    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.75/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/1.00  
% 3.75/1.00  fof(f24,plain,(
% 3.75/1.00    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.75/1.00    inference(ennf_transformation,[],[f6])).
% 3.75/1.00  
% 3.75/1.00  fof(f47,plain,(
% 3.75/1.00    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.75/1.00    inference(nnf_transformation,[],[f24])).
% 3.75/1.00  
% 3.75/1.00  fof(f59,plain,(
% 3.75/1.00    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.75/1.00    inference(cnf_transformation,[],[f47])).
% 3.75/1.00  
% 3.75/1.00  fof(f76,plain,(
% 3.75/1.00    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.75/1.00    inference(cnf_transformation,[],[f37])).
% 3.75/1.00  
% 3.75/1.00  fof(f4,axiom,(
% 3.75/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.75/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/1.00  
% 3.75/1.00  fof(f46,plain,(
% 3.75/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.75/1.00    inference(nnf_transformation,[],[f4])).
% 3.75/1.00  
% 3.75/1.00  fof(f56,plain,(
% 3.75/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.75/1.00    inference(cnf_transformation,[],[f46])).
% 3.75/1.00  
% 3.75/1.00  fof(f8,axiom,(
% 3.75/1.00    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 3.75/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/1.00  
% 3.75/1.00  fof(f27,plain,(
% 3.75/1.00    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 3.75/1.00    inference(ennf_transformation,[],[f8])).
% 3.75/1.00  
% 3.75/1.00  fof(f62,plain,(
% 3.75/1.00    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 3.75/1.00    inference(cnf_transformation,[],[f27])).
% 3.75/1.00  
% 3.75/1.00  fof(f1,axiom,(
% 3.75/1.00    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.75/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/1.00  
% 3.75/1.00  fof(f20,plain,(
% 3.75/1.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.75/1.00    inference(ennf_transformation,[],[f1])).
% 3.75/1.00  
% 3.75/1.00  fof(f21,plain,(
% 3.75/1.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.75/1.00    inference(flattening,[],[f20])).
% 3.75/1.00  
% 3.75/1.00  fof(f51,plain,(
% 3.75/1.00    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 3.75/1.00    inference(cnf_transformation,[],[f21])).
% 3.75/1.00  
% 3.75/1.00  fof(f57,plain,(
% 3.75/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.75/1.00    inference(cnf_transformation,[],[f46])).
% 3.75/1.00  
% 3.75/1.00  fof(f85,plain,(
% 3.75/1.00    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 3.75/1.00    inference(cnf_transformation,[],[f50])).
% 3.75/1.00  
% 3.75/1.00  fof(f70,plain,(
% 3.75/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.75/1.00    inference(cnf_transformation,[],[f48])).
% 3.75/1.00  
% 3.75/1.00  fof(f93,plain,(
% 3.75/1.00    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.75/1.00    inference(equality_resolution,[],[f70])).
% 3.75/1.00  
% 3.75/1.00  fof(f3,axiom,(
% 3.75/1.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.75/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/1.00  
% 3.75/1.00  fof(f44,plain,(
% 3.75/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.75/1.00    inference(nnf_transformation,[],[f3])).
% 3.75/1.00  
% 3.75/1.00  fof(f45,plain,(
% 3.75/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.75/1.00    inference(flattening,[],[f44])).
% 3.75/1.00  
% 3.75/1.00  fof(f54,plain,(
% 3.75/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.75/1.00    inference(cnf_transformation,[],[f45])).
% 3.75/1.00  
% 3.75/1.00  fof(f88,plain,(
% 3.75/1.00    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.75/1.00    inference(equality_resolution,[],[f54])).
% 3.75/1.00  
% 3.75/1.00  fof(f74,plain,(
% 3.75/1.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.75/1.00    inference(cnf_transformation,[],[f48])).
% 3.75/1.00  
% 3.75/1.00  fof(f89,plain,(
% 3.75/1.00    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.75/1.00    inference(equality_resolution,[],[f74])).
% 3.75/1.00  
% 3.75/1.00  fof(f90,plain,(
% 3.75/1.00    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.75/1.00    inference(equality_resolution,[],[f89])).
% 3.75/1.00  
% 3.75/1.00  fof(f55,plain,(
% 3.75/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.75/1.00    inference(cnf_transformation,[],[f45])).
% 3.75/1.00  
% 3.75/1.00  fof(f87,plain,(
% 3.75/1.00    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.75/1.00    inference(equality_resolution,[],[f55])).
% 3.75/1.00  
% 3.75/1.00  fof(f53,plain,(
% 3.75/1.00    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.75/1.00    inference(cnf_transformation,[],[f45])).
% 3.75/1.00  
% 3.75/1.00  fof(f2,axiom,(
% 3.75/1.00    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 3.75/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.75/1.00  
% 3.75/1.00  fof(f22,plain,(
% 3.75/1.00    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 3.75/1.00    inference(ennf_transformation,[],[f2])).
% 3.75/1.00  
% 3.75/1.00  fof(f52,plain,(
% 3.75/1.00    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 3.75/1.00    inference(cnf_transformation,[],[f22])).
% 3.75/1.00  
% 3.75/1.00  fof(f72,plain,(
% 3.75/1.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.75/1.00    inference(cnf_transformation,[],[f48])).
% 3.75/1.00  
% 3.75/1.00  fof(f92,plain,(
% 3.75/1.00    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.75/1.00    inference(equality_resolution,[],[f72])).
% 3.75/1.00  
% 3.75/1.00  cnf(c_32,negated_conjecture,
% 3.75/1.00      ( r1_tarski(sK2,sK0) ),
% 3.75/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_1684,plain,
% 3.75/1.00      ( r1_tarski(sK2,sK0) = iProver_top ),
% 3.75/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_23,plain,
% 3.75/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.75/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.75/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.75/1.00      | k1_xboole_0 = X2 ),
% 3.75/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_34,negated_conjecture,
% 3.75/1.00      ( v1_funct_2(sK3,sK0,sK1) ),
% 3.75/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_645,plain,
% 3.75/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.75/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.75/1.00      | sK3 != X0
% 3.75/1.00      | sK1 != X2
% 3.75/1.00      | sK0 != X1
% 3.75/1.00      | k1_xboole_0 = X2 ),
% 3.75/1.00      inference(resolution_lifted,[status(thm)],[c_23,c_34]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_646,plain,
% 3.75/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.75/1.00      | k1_relset_1(sK0,sK1,sK3) = sK0
% 3.75/1.00      | k1_xboole_0 = sK1 ),
% 3.75/1.00      inference(unflattening,[status(thm)],[c_645]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_33,negated_conjecture,
% 3.75/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.75/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_648,plain,
% 3.75/1.00      ( k1_relset_1(sK0,sK1,sK3) = sK0 | k1_xboole_0 = sK1 ),
% 3.75/1.00      inference(global_propositional_subsumption,
% 3.75/1.00                [status(thm)],
% 3.75/1.00                [c_646,c_33]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_1683,plain,
% 3.75/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.75/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_17,plain,
% 3.75/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.75/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.75/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_1689,plain,
% 3.75/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.75/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.75/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_3497,plain,
% 3.75/1.00      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 3.75/1.00      inference(superposition,[status(thm)],[c_1683,c_1689]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_3627,plain,
% 3.75/1.00      ( k1_relat_1(sK3) = sK0 | sK1 = k1_xboole_0 ),
% 3.75/1.00      inference(superposition,[status(thm)],[c_648,c_3497]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_12,plain,
% 3.75/1.00      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 3.75/1.00      | ~ v1_relat_1(X1)
% 3.75/1.00      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 3.75/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_1692,plain,
% 3.75/1.00      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 3.75/1.00      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 3.75/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.75/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_4239,plain,
% 3.75/1.00      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 3.75/1.00      | sK1 = k1_xboole_0
% 3.75/1.00      | r1_tarski(X0,sK0) != iProver_top
% 3.75/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.75/1.00      inference(superposition,[status(thm)],[c_3627,c_1692]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_38,plain,
% 3.75/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.75/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_14,plain,
% 3.75/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.75/1.00      | v1_relat_1(X0) ),
% 3.75/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_1970,plain,
% 3.75/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.75/1.00      | v1_relat_1(sK3) ),
% 3.75/1.00      inference(instantiation,[status(thm)],[c_14]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_1971,plain,
% 3.75/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.75/1.00      | v1_relat_1(sK3) = iProver_top ),
% 3.75/1.00      inference(predicate_to_equality,[status(thm)],[c_1970]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_4855,plain,
% 3.75/1.00      ( r1_tarski(X0,sK0) != iProver_top
% 3.75/1.00      | sK1 = k1_xboole_0
% 3.75/1.00      | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
% 3.75/1.00      inference(global_propositional_subsumption,
% 3.75/1.00                [status(thm)],
% 3.75/1.00                [c_4239,c_38,c_1971]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_4856,plain,
% 3.75/1.00      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 3.75/1.00      | sK1 = k1_xboole_0
% 3.75/1.00      | r1_tarski(X0,sK0) != iProver_top ),
% 3.75/1.00      inference(renaming,[status(thm)],[c_4855]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_4865,plain,
% 3.75/1.00      ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2 | sK1 = k1_xboole_0 ),
% 3.75/1.00      inference(superposition,[status(thm)],[c_1684,c_4856]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_27,plain,
% 3.75/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.75/1.00      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.75/1.00      | ~ v1_funct_1(X0)
% 3.75/1.00      | ~ v1_relat_1(X0) ),
% 3.75/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_1685,plain,
% 3.75/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
% 3.75/1.00      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 3.75/1.00      | v1_funct_1(X0) != iProver_top
% 3.75/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.75/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_5838,plain,
% 3.75/1.00      ( sK1 = k1_xboole_0
% 3.75/1.00      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 3.75/1.00      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
% 3.75/1.00      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top
% 3.75/1.00      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.75/1.00      inference(superposition,[status(thm)],[c_4865,c_1685]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_26,plain,
% 3.75/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.75/1.00      | ~ v1_funct_1(X0)
% 3.75/1.00      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 3.75/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_1686,plain,
% 3.75/1.00      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 3.75/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.75/1.00      | v1_funct_1(X2) != iProver_top ),
% 3.75/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_5047,plain,
% 3.75/1.00      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
% 3.75/1.00      | v1_funct_1(sK3) != iProver_top ),
% 3.75/1.00      inference(superposition,[status(thm)],[c_1683,c_1686]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_35,negated_conjecture,
% 3.75/1.00      ( v1_funct_1(sK3) ),
% 3.75/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_2042,plain,
% 3.75/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.75/1.00      | ~ v1_funct_1(sK3)
% 3.75/1.00      | k2_partfun1(X0,X1,sK3,X2) = k7_relat_1(sK3,X2) ),
% 3.75/1.00      inference(instantiation,[status(thm)],[c_26]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_2269,plain,
% 3.75/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.75/1.00      | ~ v1_funct_1(sK3)
% 3.75/1.00      | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 3.75/1.00      inference(instantiation,[status(thm)],[c_2042]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_5253,plain,
% 3.75/1.00      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 3.75/1.00      inference(global_propositional_subsumption,
% 3.75/1.00                [status(thm)],
% 3.75/1.00                [c_5047,c_35,c_33,c_2269]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_25,plain,
% 3.75/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.75/1.00      | ~ v1_funct_1(X0)
% 3.75/1.00      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
% 3.75/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_1687,plain,
% 3.75/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.75/1.00      | v1_funct_1(X0) != iProver_top
% 3.75/1.00      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
% 3.75/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_4265,plain,
% 3.75/1.00      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
% 3.75/1.00      | v1_funct_1(sK3) != iProver_top ),
% 3.75/1.00      inference(superposition,[status(thm)],[c_1683,c_1687]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_36,plain,
% 3.75/1.00      ( v1_funct_1(sK3) = iProver_top ),
% 3.75/1.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_2014,plain,
% 3.75/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.75/1.00      | v1_funct_1(k2_partfun1(X0,X1,sK3,X2))
% 3.75/1.00      | ~ v1_funct_1(sK3) ),
% 3.75/1.00      inference(instantiation,[status(thm)],[c_25]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_2517,plain,
% 3.75/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.75/1.00      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
% 3.75/1.00      | ~ v1_funct_1(sK3) ),
% 3.75/1.00      inference(instantiation,[status(thm)],[c_2014]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_2518,plain,
% 3.75/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.75/1.00      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
% 3.75/1.00      | v1_funct_1(sK3) != iProver_top ),
% 3.75/1.00      inference(predicate_to_equality,[status(thm)],[c_2517]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_4634,plain,
% 3.75/1.00      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top ),
% 3.75/1.00      inference(global_propositional_subsumption,
% 3.75/1.00                [status(thm)],
% 3.75/1.00                [c_4265,c_36,c_38,c_2518]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_5262,plain,
% 3.75/1.00      ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 3.75/1.00      inference(demodulation,[status(thm)],[c_5253,c_4634]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_6744,plain,
% 3.75/1.00      ( sK1 = k1_xboole_0
% 3.75/1.00      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 3.75/1.00      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),X0) != iProver_top
% 3.75/1.00      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.75/1.00      inference(forward_subsumption_resolution,
% 3.75/1.00                [status(thm)],
% 3.75/1.00                [c_5838,c_5262]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_28,plain,
% 3.75/1.00      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 3.75/1.00      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.75/1.00      | ~ v1_funct_1(X0)
% 3.75/1.00      | ~ v1_relat_1(X0) ),
% 3.75/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_30,negated_conjecture,
% 3.75/1.00      ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
% 3.75/1.00      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.75/1.00      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
% 3.75/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_656,plain,
% 3.75/1.00      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.75/1.00      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.75/1.00      | ~ v1_funct_1(X0)
% 3.75/1.00      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.75/1.00      | ~ v1_relat_1(X0)
% 3.75/1.00      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 3.75/1.00      | k1_relat_1(X0) != sK2
% 3.75/1.00      | sK1 != X1 ),
% 3.75/1.00      inference(resolution_lifted,[status(thm)],[c_28,c_30]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_657,plain,
% 3.75/1.00      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.75/1.00      | ~ r1_tarski(k2_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)),sK1)
% 3.75/1.00      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.75/1.00      | ~ v1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.75/1.00      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
% 3.75/1.00      inference(unflattening,[status(thm)],[c_656]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_15,plain,
% 3.75/1.00      ( v5_relat_1(X0,X1)
% 3.75/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.75/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_9,plain,
% 3.75/1.00      ( ~ v5_relat_1(X0,X1)
% 3.75/1.00      | r1_tarski(k2_relat_1(X0),X1)
% 3.75/1.00      | ~ v1_relat_1(X0) ),
% 3.75/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_444,plain,
% 3.75/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.75/1.00      | r1_tarski(k2_relat_1(X0),X2)
% 3.75/1.00      | ~ v1_relat_1(X0) ),
% 3.75/1.00      inference(resolution,[status(thm)],[c_15,c_9]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_448,plain,
% 3.75/1.00      ( r1_tarski(k2_relat_1(X0),X2)
% 3.75/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.75/1.00      inference(global_propositional_subsumption,
% 3.75/1.00                [status(thm)],
% 3.75/1.00                [c_444,c_14]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_449,plain,
% 3.75/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.75/1.00      | r1_tarski(k2_relat_1(X0),X2) ),
% 3.75/1.00      inference(renaming,[status(thm)],[c_448]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_669,plain,
% 3.75/1.00      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.75/1.00      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.75/1.00      | k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2 ),
% 3.75/1.00      inference(forward_subsumption_resolution,
% 3.75/1.00                [status(thm)],
% 3.75/1.00                [c_657,c_14,c_449]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_1670,plain,
% 3.75/1.00      ( k1_relat_1(k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 3.75/1.00      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.75/1.00      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.75/1.00      inference(predicate_to_equality,[status(thm)],[c_669]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_5260,plain,
% 3.75/1.00      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 3.75/1.00      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.75/1.00      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.75/1.00      inference(demodulation,[status(thm)],[c_5253,c_1670]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_5276,plain,
% 3.75/1.00      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 3.75/1.00      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.75/1.00      inference(forward_subsumption_resolution,
% 3.75/1.00                [status(thm)],
% 3.75/1.00                [c_5260,c_5262]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_8257,plain,
% 3.75/1.00      ( sK1 = k1_xboole_0
% 3.75/1.00      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.75/1.00      inference(superposition,[status(thm)],[c_4865,c_5276]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_8263,plain,
% 3.75/1.00      ( sK1 = k1_xboole_0
% 3.75/1.00      | r1_tarski(k2_relat_1(k7_relat_1(sK3,sK2)),sK1) != iProver_top
% 3.75/1.00      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 3.75/1.00      inference(superposition,[status(thm)],[c_6744,c_8257]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_24,plain,
% 3.75/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.75/1.00      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.75/1.00      | ~ v1_funct_1(X0) ),
% 3.75/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_1688,plain,
% 3.75/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.75/1.00      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 3.75/1.00      | v1_funct_1(X0) != iProver_top ),
% 3.75/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_6367,plain,
% 3.75/1.00      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 3.75/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.75/1.00      | v1_funct_1(sK3) != iProver_top ),
% 3.75/1.00      inference(superposition,[status(thm)],[c_5253,c_1688]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_6,plain,
% 3.75/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.75/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_1963,plain,
% 3.75/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.75/1.00      | r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
% 3.75/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_1964,plain,
% 3.75/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.75/1.00      | r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 3.75/1.00      inference(predicate_to_equality,[status(thm)],[c_1963]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_11,plain,
% 3.75/1.00      ( r1_tarski(k7_relat_1(X0,X1),X0) | ~ v1_relat_1(X0) ),
% 3.75/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_2065,plain,
% 3.75/1.00      ( r1_tarski(k7_relat_1(sK3,X0),sK3) | ~ v1_relat_1(sK3) ),
% 3.75/1.00      inference(instantiation,[status(thm)],[c_11]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_2066,plain,
% 3.75/1.00      ( r1_tarski(k7_relat_1(sK3,X0),sK3) = iProver_top
% 3.75/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.75/1.00      inference(predicate_to_equality,[status(thm)],[c_2065]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_0,plain,
% 3.75/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 3.75/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_2054,plain,
% 3.75/1.00      ( r1_tarski(X0,k2_zfmisc_1(sK0,sK1))
% 3.75/1.00      | ~ r1_tarski(X0,sK3)
% 3.75/1.00      | ~ r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
% 3.75/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_2400,plain,
% 3.75/1.00      ( r1_tarski(k7_relat_1(sK3,X0),k2_zfmisc_1(sK0,sK1))
% 3.75/1.00      | ~ r1_tarski(k7_relat_1(sK3,X0),sK3)
% 3.75/1.00      | ~ r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
% 3.75/1.00      inference(instantiation,[status(thm)],[c_2054]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_2401,plain,
% 3.75/1.00      ( r1_tarski(k7_relat_1(sK3,X0),k2_zfmisc_1(sK0,sK1)) = iProver_top
% 3.75/1.00      | r1_tarski(k7_relat_1(sK3,X0),sK3) != iProver_top
% 3.75/1.00      | r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) != iProver_top ),
% 3.75/1.00      inference(predicate_to_equality,[status(thm)],[c_2400]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_5,plain,
% 3.75/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.75/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_3333,plain,
% 3.75/1.00      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.75/1.00      | ~ r1_tarski(k7_relat_1(sK3,X0),k2_zfmisc_1(sK0,sK1)) ),
% 3.75/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_3334,plain,
% 3.75/1.00      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 3.75/1.00      | r1_tarski(k7_relat_1(sK3,X0),k2_zfmisc_1(sK0,sK1)) != iProver_top ),
% 3.75/1.00      inference(predicate_to_equality,[status(thm)],[c_3333]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_6504,plain,
% 3.75/1.00      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.75/1.00      inference(global_propositional_subsumption,
% 3.75/1.00                [status(thm)],
% 3.75/1.00                [c_6367,c_38,c_1964,c_1971,c_2066,c_2401,c_3334]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_1690,plain,
% 3.75/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.75/1.00      | v1_relat_1(X0) = iProver_top ),
% 3.75/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_6516,plain,
% 3.75/1.00      ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 3.75/1.00      inference(superposition,[status(thm)],[c_6504,c_1690]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_1679,plain,
% 3.75/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.75/1.00      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 3.75/1.00      inference(predicate_to_equality,[status(thm)],[c_449]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_6514,plain,
% 3.75/1.00      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) = iProver_top ),
% 3.75/1.00      inference(superposition,[status(thm)],[c_6504,c_1679]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_11462,plain,
% 3.75/1.00      ( sK1 = k1_xboole_0 ),
% 3.75/1.00      inference(forward_subsumption_resolution,
% 3.75/1.00                [status(thm)],
% 3.75/1.00                [c_8263,c_6516,c_6514]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_11500,plain,
% 3.75/1.00      ( k1_relset_1(sK0,k1_xboole_0,sK3) = k1_relat_1(sK3) ),
% 3.75/1.00      inference(demodulation,[status(thm)],[c_11462,c_3497]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_31,negated_conjecture,
% 3.75/1.00      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 3.75/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_11506,plain,
% 3.75/1.00      ( sK0 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.75/1.00      inference(demodulation,[status(thm)],[c_11462,c_31]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_11507,plain,
% 3.75/1.00      ( sK0 = k1_xboole_0 ),
% 3.75/1.00      inference(equality_resolution_simp,[status(thm)],[c_11506]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_22,plain,
% 3.75/1.00      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 3.75/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.75/1.00      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 3.75/1.00      inference(cnf_transformation,[],[f93]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_589,plain,
% 3.75/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.75/1.00      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 3.75/1.00      | sK3 != X0
% 3.75/1.00      | sK1 != X1
% 3.75/1.00      | sK0 != k1_xboole_0 ),
% 3.75/1.00      inference(resolution_lifted,[status(thm)],[c_22,c_34]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_590,plain,
% 3.75/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 3.75/1.00      | k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
% 3.75/1.00      | sK0 != k1_xboole_0 ),
% 3.75/1.00      inference(unflattening,[status(thm)],[c_589]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_1673,plain,
% 3.75/1.00      ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
% 3.75/1.00      | sK0 != k1_xboole_0
% 3.75/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
% 3.75/1.00      inference(predicate_to_equality,[status(thm)],[c_590]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_3,plain,
% 3.75/1.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.75/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_1776,plain,
% 3.75/1.00      ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
% 3.75/1.00      | sK0 != k1_xboole_0
% 3.75/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.75/1.00      inference(demodulation,[status(thm)],[c_1673,c_3]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_11503,plain,
% 3.75/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
% 3.75/1.00      | sK0 != k1_xboole_0
% 3.75/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.75/1.00      inference(demodulation,[status(thm)],[c_11462,c_1776]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_11514,plain,
% 3.75/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
% 3.75/1.00      | k1_xboole_0 != k1_xboole_0
% 3.75/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.75/1.00      inference(light_normalisation,[status(thm)],[c_11503,c_11507]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_11515,plain,
% 3.75/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
% 3.75/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.75/1.00      inference(equality_resolution_simp,[status(thm)],[c_11514]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_11505,plain,
% 3.75/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
% 3.75/1.00      inference(demodulation,[status(thm)],[c_11462,c_1683]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_11510,plain,
% 3.75/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.75/1.00      inference(light_normalisation,[status(thm)],[c_11505,c_11507]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_11512,plain,
% 3.75/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.75/1.00      inference(demodulation,[status(thm)],[c_11510,c_3]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_11518,plain,
% 3.75/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0 ),
% 3.75/1.00      inference(forward_subsumption_resolution,
% 3.75/1.00                [status(thm)],
% 3.75/1.00                [c_11515,c_11512]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_11525,plain,
% 3.75/1.00      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 3.75/1.00      inference(light_normalisation,
% 3.75/1.00                [status(thm)],
% 3.75/1.00                [c_11500,c_11507,c_11518]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_12165,plain,
% 3.75/1.00      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 3.75/1.00      | r1_tarski(X0,k1_xboole_0) != iProver_top
% 3.75/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.75/1.00      inference(superposition,[status(thm)],[c_11525,c_1692]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_12185,plain,
% 3.75/1.00      ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0
% 3.75/1.00      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 3.75/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.75/1.00      inference(instantiation,[status(thm)],[c_12165]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_6518,plain,
% 3.75/1.00      ( k1_relset_1(sK0,sK1,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
% 3.75/1.00      inference(superposition,[status(thm)],[c_6504,c_1689]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_11485,plain,
% 3.75/1.00      ( k1_relset_1(sK0,k1_xboole_0,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
% 3.75/1.00      inference(demodulation,[status(thm)],[c_11462,c_6518]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_11578,plain,
% 3.75/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
% 3.75/1.00      inference(light_normalisation,[status(thm)],[c_11485,c_11507]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_11490,plain,
% 3.75/1.00      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
% 3.75/1.00      inference(demodulation,[status(thm)],[c_11462,c_6504]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_11559,plain,
% 3.75/1.00      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.75/1.00      inference(light_normalisation,[status(thm)],[c_11490,c_11507]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_11561,plain,
% 3.75/1.00      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.75/1.00      inference(demodulation,[status(thm)],[c_11559,c_3]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_18,plain,
% 3.75/1.00      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
% 3.75/1.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 3.75/1.00      | k1_xboole_0 = X0 ),
% 3.75/1.00      inference(cnf_transformation,[],[f90]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_473,plain,
% 3.75/1.00      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.75/1.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 3.75/1.00      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.75/1.00      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 3.75/1.00      | sK2 != X0
% 3.75/1.00      | sK1 != k1_xboole_0
% 3.75/1.00      | k1_xboole_0 = X0 ),
% 3.75/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_30]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_474,plain,
% 3.75/1.00      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.75/1.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
% 3.75/1.00      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.75/1.00      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 3.75/1.00      | sK1 != k1_xboole_0
% 3.75/1.00      | k1_xboole_0 = sK2 ),
% 3.75/1.00      inference(unflattening,[status(thm)],[c_473]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_1678,plain,
% 3.75/1.00      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 3.75/1.00      | sK1 != k1_xboole_0
% 3.75/1.00      | k1_xboole_0 = sK2
% 3.75/1.00      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.75/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
% 3.75/1.00      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.75/1.00      inference(predicate_to_equality,[status(thm)],[c_474]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_2,plain,
% 3.75/1.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.75/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_1869,plain,
% 3.75/1.00      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 3.75/1.00      | sK2 = k1_xboole_0
% 3.75/1.00      | sK1 != k1_xboole_0
% 3.75/1.00      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.75/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.75/1.00      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.75/1.00      inference(demodulation,[status(thm)],[c_1678,c_2]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_2163,plain,
% 3.75/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.75/1.00      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.75/1.00      | ~ v1_funct_1(sK3) ),
% 3.75/1.00      inference(instantiation,[status(thm)],[c_2014]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_2164,plain,
% 3.75/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.75/1.00      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) = iProver_top
% 3.75/1.00      | v1_funct_1(sK3) != iProver_top ),
% 3.75/1.00      inference(predicate_to_equality,[status(thm)],[c_2163]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_2339,plain,
% 3.75/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.75/1.00      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.75/1.00      | sK1 != k1_xboole_0
% 3.75/1.00      | sK2 = k1_xboole_0
% 3.75/1.00      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0 ),
% 3.75/1.00      inference(global_propositional_subsumption,
% 3.75/1.00                [status(thm)],
% 3.75/1.00                [c_1869,c_36,c_38,c_2164]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_2340,plain,
% 3.75/1.00      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 3.75/1.00      | sK2 = k1_xboole_0
% 3.75/1.00      | sK1 != k1_xboole_0
% 3.75/1.00      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.75/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.75/1.00      inference(renaming,[status(thm)],[c_2339]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_5258,plain,
% 3.75/1.00      ( k7_relat_1(sK3,sK2) != k1_xboole_0
% 3.75/1.00      | sK2 = k1_xboole_0
% 3.75/1.00      | sK1 != k1_xboole_0
% 3.75/1.00      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.75/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.75/1.00      inference(demodulation,[status(thm)],[c_5253,c_2340]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_4,plain,
% 3.75/1.00      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.75/1.00      | k1_xboole_0 = X0
% 3.75/1.00      | k1_xboole_0 = X1 ),
% 3.75/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_112,plain,
% 3.75/1.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.75/1.00      | k1_xboole_0 = k1_xboole_0 ),
% 3.75/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_113,plain,
% 3.75/1.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.75/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_1,plain,
% 3.75/1.00      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 3.75/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_2229,plain,
% 3.75/1.00      ( ~ r1_tarski(sK2,k1_xboole_0) | k1_xboole_0 = sK2 ),
% 3.75/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_1013,plain,
% 3.75/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.75/1.00      theory(equality) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_2019,plain,
% 3.75/1.00      ( r1_tarski(X0,X1) | ~ r1_tarski(sK2,sK0) | X0 != sK2 | X1 != sK0 ),
% 3.75/1.00      inference(instantiation,[status(thm)],[c_1013]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_2237,plain,
% 3.75/1.00      ( r1_tarski(sK2,X0)
% 3.75/1.00      | ~ r1_tarski(sK2,sK0)
% 3.75/1.00      | X0 != sK0
% 3.75/1.00      | sK2 != sK2 ),
% 3.75/1.00      inference(instantiation,[status(thm)],[c_2019]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_2240,plain,
% 3.75/1.00      ( ~ r1_tarski(sK2,sK0)
% 3.75/1.00      | r1_tarski(sK2,k1_xboole_0)
% 3.75/1.00      | sK2 != sK2
% 3.75/1.00      | k1_xboole_0 != sK0 ),
% 3.75/1.00      inference(instantiation,[status(thm)],[c_2237]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_1011,plain,( X0 = X0 ),theory(equality) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_2238,plain,
% 3.75/1.00      ( sK2 = sK2 ),
% 3.75/1.00      inference(instantiation,[status(thm)],[c_1011]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_1012,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_2002,plain,
% 3.75/1.00      ( sK2 != X0 | sK2 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 3.75/1.00      inference(instantiation,[status(thm)],[c_1012]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_2630,plain,
% 3.75/1.00      ( sK2 != sK2 | sK2 = k1_xboole_0 | k1_xboole_0 != sK2 ),
% 3.75/1.00      inference(instantiation,[status(thm)],[c_2002]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_2775,plain,
% 3.75/1.00      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 3.75/1.00      inference(instantiation,[status(thm)],[c_1012]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_2776,plain,
% 3.75/1.00      ( sK1 != k1_xboole_0
% 3.75/1.00      | k1_xboole_0 = sK1
% 3.75/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.75/1.00      inference(instantiation,[status(thm)],[c_2775]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_5625,plain,
% 3.75/1.00      ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.75/1.00      | sK2 = k1_xboole_0 ),
% 3.75/1.00      inference(global_propositional_subsumption,
% 3.75/1.00                [status(thm)],
% 3.75/1.00                [c_5258,c_32,c_31,c_112,c_113,c_2229,c_2240,c_2238,
% 3.75/1.00                 c_2630,c_2776,c_4865,c_5276]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_5626,plain,
% 3.75/1.00      ( sK2 = k1_xboole_0
% 3.75/1.00      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.75/1.00      inference(renaming,[status(thm)],[c_5625]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_11493,plain,
% 3.75/1.00      ( sK2 = k1_xboole_0
% 3.75/1.00      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top ),
% 3.75/1.00      inference(demodulation,[status(thm)],[c_11462,c_5626]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_11549,plain,
% 3.75/1.00      ( sK2 = k1_xboole_0
% 3.75/1.00      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.75/1.00      inference(demodulation,[status(thm)],[c_11493,c_2]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_11563,plain,
% 3.75/1.00      ( sK2 = k1_xboole_0 ),
% 3.75/1.00      inference(backward_subsumption_resolution,
% 3.75/1.00                [status(thm)],
% 3.75/1.00                [c_11561,c_11549]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_20,plain,
% 3.75/1.00      ( v1_funct_2(X0,k1_xboole_0,X1)
% 3.75/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.75/1.00      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 3.75/1.00      inference(cnf_transformation,[],[f92]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_570,plain,
% 3.75/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.75/1.00      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.75/1.00      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.75/1.00      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 3.75/1.00      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 3.75/1.00      | sK2 != k1_xboole_0
% 3.75/1.00      | sK1 != X1 ),
% 3.75/1.00      inference(resolution_lifted,[status(thm)],[c_20,c_30]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_571,plain,
% 3.75/1.00      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.75/1.00      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 3.75/1.00      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 3.75/1.00      | k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
% 3.75/1.00      | sK2 != k1_xboole_0 ),
% 3.75/1.00      inference(unflattening,[status(thm)],[c_570]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_1674,plain,
% 3.75/1.00      ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
% 3.75/1.00      | sK2 != k1_xboole_0
% 3.75/1.00      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.75/1.00      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
% 3.75/1.00      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.75/1.00      inference(predicate_to_equality,[status(thm)],[c_571]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_1882,plain,
% 3.75/1.00      ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
% 3.75/1.00      | sK2 != k1_xboole_0
% 3.75/1.00      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.75/1.00      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.75/1.00      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 3.75/1.00      inference(demodulation,[status(thm)],[c_1674,c_3]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_2349,plain,
% 3.75/1.00      ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.75/1.00      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.75/1.00      | sK2 != k1_xboole_0
% 3.75/1.00      | k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0 ),
% 3.75/1.00      inference(global_propositional_subsumption,
% 3.75/1.00                [status(thm)],
% 3.75/1.00                [c_1882,c_36,c_38,c_2164]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_2350,plain,
% 3.75/1.00      ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
% 3.75/1.00      | sK2 != k1_xboole_0
% 3.75/1.00      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.75/1.00      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.75/1.00      inference(renaming,[status(thm)],[c_2349]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_5257,plain,
% 3.75/1.00      ( k1_relset_1(k1_xboole_0,sK1,k7_relat_1(sK3,sK2)) != k1_xboole_0
% 3.75/1.00      | sK2 != k1_xboole_0
% 3.75/1.00      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.75/1.00      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.75/1.00      inference(demodulation,[status(thm)],[c_5253,c_2350]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_5634,plain,
% 3.75/1.00      ( k1_relset_1(k1_xboole_0,sK1,k7_relat_1(sK3,sK2)) != k1_xboole_0
% 3.75/1.00      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.75/1.00      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.75/1.00      inference(global_propositional_subsumption,
% 3.75/1.00                [status(thm)],
% 3.75/1.00                [c_5257,c_5626]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_11492,plain,
% 3.75/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,sK2)) != k1_xboole_0
% 3.75/1.00      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
% 3.75/1.00      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.75/1.00      inference(demodulation,[status(thm)],[c_11462,c_5634]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_11555,plain,
% 3.75/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,sK2)) != k1_xboole_0
% 3.75/1.00      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.75/1.00      inference(demodulation,[status(thm)],[c_11492,c_2]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_11564,plain,
% 3.75/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,sK2)) != k1_xboole_0 ),
% 3.75/1.00      inference(backward_subsumption_resolution,
% 3.75/1.00                [status(thm)],
% 3.75/1.00                [c_11561,c_11555]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_11568,plain,
% 3.75/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0 ),
% 3.75/1.00      inference(demodulation,[status(thm)],[c_11563,c_11564]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_11580,plain,
% 3.75/1.00      ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0 ),
% 3.75/1.00      inference(demodulation,[status(thm)],[c_11578,c_11568]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_2470,plain,
% 3.75/1.00      ( k2_relat_1(sK3) = k2_relat_1(sK3) ),
% 3.75/1.00      inference(instantiation,[status(thm)],[c_1011]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_2084,plain,
% 3.75/1.00      ( r1_tarski(X0,X1)
% 3.75/1.00      | ~ r1_tarski(k2_relat_1(sK3),sK1)
% 3.75/1.00      | X0 != k2_relat_1(sK3)
% 3.75/1.00      | X1 != sK1 ),
% 3.75/1.00      inference(instantiation,[status(thm)],[c_1013]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_2469,plain,
% 3.75/1.00      ( r1_tarski(k2_relat_1(sK3),X0)
% 3.75/1.00      | ~ r1_tarski(k2_relat_1(sK3),sK1)
% 3.75/1.00      | X0 != sK1
% 3.75/1.00      | k2_relat_1(sK3) != k2_relat_1(sK3) ),
% 3.75/1.00      inference(instantiation,[status(thm)],[c_2084]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_2472,plain,
% 3.75/1.00      ( ~ r1_tarski(k2_relat_1(sK3),sK1)
% 3.75/1.00      | r1_tarski(k2_relat_1(sK3),k1_xboole_0)
% 3.75/1.00      | k2_relat_1(sK3) != k2_relat_1(sK3)
% 3.75/1.00      | k1_xboole_0 != sK1 ),
% 3.75/1.00      inference(instantiation,[status(thm)],[c_2469]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_2461,plain,
% 3.75/1.00      ( ~ r1_tarski(k2_relat_1(sK3),k1_xboole_0)
% 3.75/1.00      | k1_xboole_0 = k2_relat_1(sK3) ),
% 3.75/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_2093,plain,
% 3.75/1.00      ( X0 != k2_relat_1(sK3)
% 3.75/1.00      | X1 != sK1
% 3.75/1.00      | r1_tarski(X0,X1) = iProver_top
% 3.75/1.00      | r1_tarski(k2_relat_1(sK3),sK1) != iProver_top ),
% 3.75/1.00      inference(predicate_to_equality,[status(thm)],[c_2084]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_2095,plain,
% 3.75/1.00      ( k1_xboole_0 != k2_relat_1(sK3)
% 3.75/1.00      | k1_xboole_0 != sK1
% 3.75/1.00      | r1_tarski(k2_relat_1(sK3),sK1) != iProver_top
% 3.75/1.00      | r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.75/1.00      inference(instantiation,[status(thm)],[c_2093]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_1983,plain,
% 3.75/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.75/1.00      | r1_tarski(k2_relat_1(sK3),sK1) ),
% 3.75/1.00      inference(instantiation,[status(thm)],[c_449]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(c_1984,plain,
% 3.75/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.75/1.00      | r1_tarski(k2_relat_1(sK3),sK1) = iProver_top ),
% 3.75/1.00      inference(predicate_to_equality,[status(thm)],[c_1983]) ).
% 3.75/1.00  
% 3.75/1.00  cnf(contradiction,plain,
% 3.75/1.00      ( $false ),
% 3.75/1.00      inference(minisat,
% 3.75/1.00                [status(thm)],
% 3.75/1.00                [c_12185,c_11580,c_11462,c_2776,c_2470,c_2472,c_2461,
% 3.75/1.00                 c_2095,c_1984,c_1983,c_1971,c_113,c_112,c_38,c_33]) ).
% 3.75/1.00  
% 3.75/1.00  
% 3.75/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.75/1.00  
% 3.75/1.00  ------                               Statistics
% 3.75/1.00  
% 3.75/1.00  ------ General
% 3.75/1.00  
% 3.75/1.00  abstr_ref_over_cycles:                  0
% 3.75/1.00  abstr_ref_under_cycles:                 0
% 3.75/1.00  gc_basic_clause_elim:                   0
% 3.75/1.00  forced_gc_time:                         0
% 3.75/1.00  parsing_time:                           0.012
% 3.75/1.00  unif_index_cands_time:                  0.
% 3.75/1.00  unif_index_add_time:                    0.
% 3.75/1.00  orderings_time:                         0.
% 3.75/1.00  out_proof_time:                         0.014
% 3.75/1.00  total_time:                             0.305
% 3.75/1.00  num_of_symbols:                         50
% 3.75/1.00  num_of_terms:                           10830
% 3.75/1.00  
% 3.75/1.00  ------ Preprocessing
% 3.75/1.00  
% 3.75/1.00  num_of_splits:                          0
% 3.75/1.00  num_of_split_atoms:                     0
% 3.75/1.00  num_of_reused_defs:                     0
% 3.75/1.00  num_eq_ax_congr_red:                    15
% 3.75/1.00  num_of_sem_filtered_clauses:            1
% 3.75/1.00  num_of_subtypes:                        0
% 3.75/1.00  monotx_restored_types:                  0
% 3.75/1.00  sat_num_of_epr_types:                   0
% 3.75/1.00  sat_num_of_non_cyclic_types:            0
% 3.75/1.00  sat_guarded_non_collapsed_types:        0
% 3.75/1.00  num_pure_diseq_elim:                    0
% 3.75/1.00  simp_replaced_by:                       0
% 3.75/1.00  res_preprocessed:                       160
% 3.75/1.00  prep_upred:                             0
% 3.75/1.00  prep_unflattend:                        43
% 3.75/1.00  smt_new_axioms:                         0
% 3.75/1.00  pred_elim_cands:                        4
% 3.75/1.00  pred_elim:                              3
% 3.75/1.00  pred_elim_cl:                           1
% 3.75/1.00  pred_elim_cycles:                       5
% 3.75/1.00  merged_defs:                            8
% 3.75/1.00  merged_defs_ncl:                        0
% 3.75/1.00  bin_hyper_res:                          9
% 3.75/1.00  prep_cycles:                            4
% 3.75/1.00  pred_elim_time:                         0.006
% 3.75/1.00  splitting_time:                         0.
% 3.75/1.00  sem_filter_time:                        0.
% 3.75/1.00  monotx_time:                            0.
% 3.75/1.00  subtype_inf_time:                       0.
% 3.75/1.00  
% 3.75/1.00  ------ Problem properties
% 3.75/1.00  
% 3.75/1.00  clauses:                                34
% 3.75/1.00  conjectures:                            4
% 3.75/1.00  epr:                                    6
% 3.75/1.00  horn:                                   29
% 3.75/1.00  ground:                                 12
% 3.75/1.00  unary:                                  5
% 3.75/1.00  binary:                                 11
% 3.75/1.00  lits:                                   95
% 3.75/1.00  lits_eq:                                35
% 3.75/1.00  fd_pure:                                0
% 3.75/1.00  fd_pseudo:                              0
% 3.75/1.00  fd_cond:                                4
% 3.75/1.00  fd_pseudo_cond:                         0
% 3.75/1.00  ac_symbols:                             0
% 3.75/1.00  
% 3.75/1.00  ------ Propositional Solver
% 3.75/1.00  
% 3.75/1.00  prop_solver_calls:                      29
% 3.75/1.00  prop_fast_solver_calls:                 1359
% 3.75/1.00  smt_solver_calls:                       0
% 3.75/1.00  smt_fast_solver_calls:                  0
% 3.75/1.00  prop_num_of_clauses:                    4490
% 3.75/1.00  prop_preprocess_simplified:             9599
% 3.75/1.00  prop_fo_subsumed:                       29
% 3.75/1.00  prop_solver_time:                       0.
% 3.75/1.00  smt_solver_time:                        0.
% 3.75/1.00  smt_fast_solver_time:                   0.
% 3.75/1.00  prop_fast_solver_time:                  0.
% 3.75/1.00  prop_unsat_core_time:                   0.
% 3.75/1.00  
% 3.75/1.00  ------ QBF
% 3.75/1.00  
% 3.75/1.00  qbf_q_res:                              0
% 3.75/1.00  qbf_num_tautologies:                    0
% 3.75/1.00  qbf_prep_cycles:                        0
% 3.75/1.00  
% 3.75/1.00  ------ BMC1
% 3.75/1.00  
% 3.75/1.00  bmc1_current_bound:                     -1
% 3.75/1.00  bmc1_last_solved_bound:                 -1
% 3.75/1.00  bmc1_unsat_core_size:                   -1
% 3.75/1.00  bmc1_unsat_core_parents_size:           -1
% 3.75/1.00  bmc1_merge_next_fun:                    0
% 3.75/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.75/1.00  
% 3.75/1.00  ------ Instantiation
% 3.75/1.00  
% 3.75/1.00  inst_num_of_clauses:                    1417
% 3.75/1.00  inst_num_in_passive:                    124
% 3.75/1.00  inst_num_in_active:                     662
% 3.75/1.00  inst_num_in_unprocessed:                631
% 3.75/1.00  inst_num_of_loops:                      740
% 3.75/1.00  inst_num_of_learning_restarts:          0
% 3.75/1.00  inst_num_moves_active_passive:          75
% 3.75/1.00  inst_lit_activity:                      0
% 3.75/1.00  inst_lit_activity_moves:                0
% 3.75/1.00  inst_num_tautologies:                   0
% 3.75/1.00  inst_num_prop_implied:                  0
% 3.75/1.00  inst_num_existing_simplified:           0
% 3.75/1.00  inst_num_eq_res_simplified:             0
% 3.75/1.00  inst_num_child_elim:                    0
% 3.75/1.00  inst_num_of_dismatching_blockings:      282
% 3.75/1.00  inst_num_of_non_proper_insts:           1034
% 3.75/1.00  inst_num_of_duplicates:                 0
% 3.75/1.00  inst_inst_num_from_inst_to_res:         0
% 3.75/1.00  inst_dismatching_checking_time:         0.
% 3.75/1.00  
% 3.75/1.00  ------ Resolution
% 3.75/1.00  
% 3.75/1.00  res_num_of_clauses:                     0
% 3.75/1.00  res_num_in_passive:                     0
% 3.75/1.00  res_num_in_active:                      0
% 3.75/1.00  res_num_of_loops:                       164
% 3.75/1.00  res_forward_subset_subsumed:            42
% 3.75/1.00  res_backward_subset_subsumed:           0
% 3.75/1.00  res_forward_subsumed:                   0
% 3.75/1.00  res_backward_subsumed:                  0
% 3.75/1.00  res_forward_subsumption_resolution:     5
% 3.75/1.00  res_backward_subsumption_resolution:    0
% 3.75/1.00  res_clause_to_clause_subsumption:       935
% 3.75/1.00  res_orphan_elimination:                 0
% 3.75/1.00  res_tautology_del:                      90
% 3.75/1.00  res_num_eq_res_simplified:              1
% 3.75/1.00  res_num_sel_changes:                    0
% 3.75/1.00  res_moves_from_active_to_pass:          0
% 3.75/1.00  
% 3.75/1.00  ------ Superposition
% 3.75/1.00  
% 3.75/1.00  sup_time_total:                         0.
% 3.75/1.00  sup_time_generating:                    0.
% 3.75/1.00  sup_time_sim_full:                      0.
% 3.75/1.00  sup_time_sim_immed:                     0.
% 3.75/1.00  
% 3.75/1.00  sup_num_of_clauses:                     266
% 3.75/1.00  sup_num_in_active:                      72
% 3.75/1.00  sup_num_in_passive:                     194
% 3.75/1.00  sup_num_of_loops:                       146
% 3.75/1.00  sup_fw_superposition:                   169
% 3.75/1.00  sup_bw_superposition:                   221
% 3.75/1.00  sup_immediate_simplified:               128
% 3.75/1.00  sup_given_eliminated:                   0
% 3.75/1.00  comparisons_done:                       0
% 3.75/1.00  comparisons_avoided:                    25
% 3.75/1.00  
% 3.75/1.00  ------ Simplifications
% 3.75/1.00  
% 3.75/1.00  
% 3.75/1.00  sim_fw_subset_subsumed:                 26
% 3.75/1.00  sim_bw_subset_subsumed:                 14
% 3.75/1.00  sim_fw_subsumed:                        34
% 3.75/1.00  sim_bw_subsumed:                        4
% 3.75/1.00  sim_fw_subsumption_res:                 9
% 3.75/1.00  sim_bw_subsumption_res:                 3
% 3.75/1.00  sim_tautology_del:                      17
% 3.75/1.00  sim_eq_tautology_del:                   8
% 3.75/1.00  sim_eq_res_simp:                        3
% 3.75/1.00  sim_fw_demodulated:                     26
% 3.75/1.00  sim_bw_demodulated:                     70
% 3.75/1.00  sim_light_normalised:                   39
% 3.75/1.00  sim_joinable_taut:                      0
% 3.75/1.00  sim_joinable_simp:                      0
% 3.75/1.00  sim_ac_normalised:                      0
% 3.75/1.00  sim_smt_subsumption:                    0
% 3.75/1.00  
%------------------------------------------------------------------------------
