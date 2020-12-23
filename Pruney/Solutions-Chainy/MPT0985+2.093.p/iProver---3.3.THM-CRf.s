%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:39 EST 2020

% Result     : Theorem 3.52s
% Output     : CNFRefutation 3.52s
% Verified   : 
% Statistics : Number of formulae       :  192 ( 896 expanded)
%              Number of clauses        :  119 ( 311 expanded)
%              Number of leaves         :   18 ( 166 expanded)
%              Depth                    :   23
%              Number of atoms          :  596 (4499 expanded)
%              Number of equality atoms :  296 ( 984 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f41,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f42,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f49,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
          | ~ v1_funct_1(k2_funct_1(X2)) )
        & k2_relset_1(X0,X1,X2) = X1
        & v2_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
        | ~ v1_funct_1(k2_funct_1(sK2)) )
      & k2_relset_1(sK0,sK1,sK2) = sK1
      & v2_funct_1(sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & k2_relset_1(sK0,sK1,sK2) = sK1
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f42,f49])).

fof(f89,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f50])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f91,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f50])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f31,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f68,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f90,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f87,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f86,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f69,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f67,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f66,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f85,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f92,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f50])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f97,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f58])).

fof(f17,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f79,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f3,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f55,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f9,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f18,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f80,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f94,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f63,f80])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f16])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

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
    inference(nnf_transformation,[],[f36])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f88,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f19,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f38,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f83,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f82,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f101,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f77])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f43])).

fof(f53,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1677,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1681,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3613,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1677,c_1681])).

cnf(c_36,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_3625,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_3613,c_36])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1683,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3142,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1677,c_1683])).

cnf(c_18,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_37,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_448,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_37])).

cnf(c_449,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_448])).

cnf(c_40,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_451,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_449,c_40])).

cnf(c_1674,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_451])).

cnf(c_3165,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_3142,c_1674])).

cnf(c_3756,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
    inference(demodulation,[status(thm)],[c_3625,c_3165])).

cnf(c_32,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1678,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_4917,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3756,c_1678])).

cnf(c_17,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_462,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_37])).

cnf(c_463,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_462])).

cnf(c_465,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_463,c_40])).

cnf(c_1673,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_465])).

cnf(c_3166,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_3142,c_1673])).

cnf(c_4962,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4917,c_3166])).

cnf(c_41,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_43,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_15,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2013,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2014,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2013])).

cnf(c_16,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2016,plain,
    ( ~ v1_funct_1(sK2)
    | v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2017,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2016])).

cnf(c_2041,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_2042,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2041])).

cnf(c_5624,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4962,c_41,c_43,c_2014,c_2017,c_2042])).

cnf(c_33,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_35,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_766,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(X0)
    | k2_funct_1(sK2) != X0
    | k1_relat_1(X0) != sK1
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_35])).

cnf(c_767,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
    inference(unflattening,[status(thm)],[c_766])).

cnf(c_779,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_767,c_19])).

cnf(c_1660,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_779])).

cnf(c_768,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_767])).

cnf(c_2120,plain,
    ( r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1660,c_41,c_43,c_768,c_2014,c_2017,c_2042])).

cnf(c_2121,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2120])).

cnf(c_3261,plain,
    ( k2_relat_1(sK2) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3165,c_2121])).

cnf(c_3407,plain,
    ( k2_relat_1(sK2) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | r1_tarski(k1_relat_1(sK2),sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3261,c_3166])).

cnf(c_3754,plain,
    ( sK1 != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | r1_tarski(k1_relat_1(sK2),sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3625,c_3407])).

cnf(c_3769,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | r1_tarski(k1_relat_1(sK2),sK0) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3754])).

cnf(c_5639,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5624,c_3769])).

cnf(c_5,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_28,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1680,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2623,plain,
    ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_1680])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1687,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2766,plain,
    ( r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2623,c_1687])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1690,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2858,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2766,c_1690])).

cnf(c_13,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_2865,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2858,c_13])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_39,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_736,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK0 != X1
    | sK1 != X2
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_39])).

cnf(c_737,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_736])).

cnf(c_739,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_737,c_38])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1682,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4421,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1677,c_1682])).

cnf(c_4483,plain,
    ( k1_relat_1(sK2) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_739,c_4421])).

cnf(c_29,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1679,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_5822,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3166,c_1679])).

cnf(c_5848,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5822,c_3756])).

cnf(c_8514,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5848,c_41,c_43,c_2014,c_2017,c_2042])).

cnf(c_8519,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4483,c_8514])).

cnf(c_30,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_747,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(X0)
    | k2_funct_1(sK2) != X0
    | k1_relat_1(X0) != sK1
    | k2_relat_1(X0) != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_35])).

cnf(c_748,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
    inference(unflattening,[status(thm)],[c_747])).

cnf(c_760,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_748,c_19])).

cnf(c_1661,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_760])).

cnf(c_749,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_748])).

cnf(c_2317,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | k2_relat_1(k2_funct_1(sK2)) != sK0
    | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1661,c_41,c_43,c_749,c_2014,c_2017,c_2042])).

cnf(c_2318,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2317])).

cnf(c_3260,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != sK0
    | k2_relat_1(sK2) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3165,c_2318])).

cnf(c_3367,plain,
    ( k1_relat_1(sK2) != sK0
    | k2_relat_1(sK2) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3260,c_3166])).

cnf(c_3755,plain,
    ( k1_relat_1(sK2) != sK0
    | sK1 != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3625,c_3367])).

cnf(c_3764,plain,
    ( k1_relat_1(sK2) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3755])).

cnf(c_4542,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4483,c_3764])).

cnf(c_8721,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8519,c_4542])).

cnf(c_8766,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8721,c_1677])).

cnf(c_8771,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8766,c_5])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_516,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | X2 != X0
    | k1_relat_1(X2) != X1
    | k2_relat_1(X2) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_30])).

cnf(c_517,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = k1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_516])).

cnf(c_533,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0)))
    | ~ v1_funct_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = k1_relat_1(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_517,c_19])).

cnf(c_1671,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = k1_relat_1(X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_533])).

cnf(c_1867,plain,
    ( k1_relat_1(X0) = k1_xboole_0
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1671,c_5])).

cnf(c_6806,plain,
    ( k1_relat_1(sK2) = k1_xboole_0
    | sK1 != k1_xboole_0
    | sK2 = k1_xboole_0
    | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3625,c_1867])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2235,plain,
    ( r1_tarski(k1_xboole_0,sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2238,plain,
    ( r1_tarski(k1_xboole_0,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2235])).

cnf(c_2374,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | r1_tarski(sK2,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2375,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(sK2,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2374])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2502,plain,
    ( ~ r1_tarski(X0,sK2)
    | ~ r1_tarski(sK2,X0)
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2503,plain,
    ( sK2 = X0
    | r1_tarski(X0,sK2) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2502])).

cnf(c_2505,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(sK2,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2503])).

cnf(c_7085,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6806,c_2238,c_2375,c_2505])).

cnf(c_7086,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_7085])).

cnf(c_9266,plain,
    ( sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8771,c_7086])).

cnf(c_10490,plain,
    ( r1_tarski(k1_xboole_0,sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5639,c_2865,c_9266])).

cnf(c_1691,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_10492,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_10490,c_1691])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:10:08 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 3.52/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.52/1.01  
% 3.52/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.52/1.01  
% 3.52/1.01  ------  iProver source info
% 3.52/1.01  
% 3.52/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.52/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.52/1.01  git: non_committed_changes: false
% 3.52/1.01  git: last_make_outside_of_git: false
% 3.52/1.01  
% 3.52/1.01  ------ 
% 3.52/1.01  
% 3.52/1.01  ------ Input Options
% 3.52/1.01  
% 3.52/1.01  --out_options                           all
% 3.52/1.01  --tptp_safe_out                         true
% 3.52/1.01  --problem_path                          ""
% 3.52/1.01  --include_path                          ""
% 3.52/1.01  --clausifier                            res/vclausify_rel
% 3.52/1.01  --clausifier_options                    --mode clausify
% 3.52/1.01  --stdin                                 false
% 3.52/1.01  --stats_out                             all
% 3.52/1.01  
% 3.52/1.01  ------ General Options
% 3.52/1.01  
% 3.52/1.01  --fof                                   false
% 3.52/1.01  --time_out_real                         305.
% 3.52/1.01  --time_out_virtual                      -1.
% 3.52/1.01  --symbol_type_check                     false
% 3.52/1.01  --clausify_out                          false
% 3.52/1.01  --sig_cnt_out                           false
% 3.52/1.01  --trig_cnt_out                          false
% 3.52/1.01  --trig_cnt_out_tolerance                1.
% 3.52/1.01  --trig_cnt_out_sk_spl                   false
% 3.52/1.01  --abstr_cl_out                          false
% 3.52/1.01  
% 3.52/1.01  ------ Global Options
% 3.52/1.01  
% 3.52/1.01  --schedule                              default
% 3.52/1.01  --add_important_lit                     false
% 3.52/1.01  --prop_solver_per_cl                    1000
% 3.52/1.01  --min_unsat_core                        false
% 3.52/1.01  --soft_assumptions                      false
% 3.52/1.01  --soft_lemma_size                       3
% 3.52/1.01  --prop_impl_unit_size                   0
% 3.52/1.01  --prop_impl_unit                        []
% 3.52/1.01  --share_sel_clauses                     true
% 3.52/1.01  --reset_solvers                         false
% 3.52/1.01  --bc_imp_inh                            [conj_cone]
% 3.52/1.01  --conj_cone_tolerance                   3.
% 3.52/1.01  --extra_neg_conj                        none
% 3.52/1.01  --large_theory_mode                     true
% 3.52/1.01  --prolific_symb_bound                   200
% 3.52/1.01  --lt_threshold                          2000
% 3.52/1.01  --clause_weak_htbl                      true
% 3.52/1.01  --gc_record_bc_elim                     false
% 3.52/1.01  
% 3.52/1.01  ------ Preprocessing Options
% 3.52/1.01  
% 3.52/1.01  --preprocessing_flag                    true
% 3.52/1.01  --time_out_prep_mult                    0.1
% 3.52/1.01  --splitting_mode                        input
% 3.52/1.01  --splitting_grd                         true
% 3.52/1.01  --splitting_cvd                         false
% 3.52/1.01  --splitting_cvd_svl                     false
% 3.52/1.01  --splitting_nvd                         32
% 3.52/1.01  --sub_typing                            true
% 3.52/1.01  --prep_gs_sim                           true
% 3.52/1.01  --prep_unflatten                        true
% 3.52/1.01  --prep_res_sim                          true
% 3.52/1.01  --prep_upred                            true
% 3.52/1.01  --prep_sem_filter                       exhaustive
% 3.52/1.01  --prep_sem_filter_out                   false
% 3.52/1.01  --pred_elim                             true
% 3.52/1.01  --res_sim_input                         true
% 3.52/1.01  --eq_ax_congr_red                       true
% 3.52/1.01  --pure_diseq_elim                       true
% 3.52/1.01  --brand_transform                       false
% 3.52/1.01  --non_eq_to_eq                          false
% 3.52/1.01  --prep_def_merge                        true
% 3.52/1.01  --prep_def_merge_prop_impl              false
% 3.52/1.01  --prep_def_merge_mbd                    true
% 3.52/1.01  --prep_def_merge_tr_red                 false
% 3.52/1.01  --prep_def_merge_tr_cl                  false
% 3.52/1.01  --smt_preprocessing                     true
% 3.52/1.01  --smt_ac_axioms                         fast
% 3.52/1.01  --preprocessed_out                      false
% 3.52/1.01  --preprocessed_stats                    false
% 3.52/1.01  
% 3.52/1.01  ------ Abstraction refinement Options
% 3.52/1.01  
% 3.52/1.01  --abstr_ref                             []
% 3.52/1.01  --abstr_ref_prep                        false
% 3.52/1.01  --abstr_ref_until_sat                   false
% 3.52/1.01  --abstr_ref_sig_restrict                funpre
% 3.52/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.52/1.01  --abstr_ref_under                       []
% 3.52/1.01  
% 3.52/1.01  ------ SAT Options
% 3.52/1.01  
% 3.52/1.01  --sat_mode                              false
% 3.52/1.01  --sat_fm_restart_options                ""
% 3.52/1.01  --sat_gr_def                            false
% 3.52/1.01  --sat_epr_types                         true
% 3.52/1.01  --sat_non_cyclic_types                  false
% 3.52/1.01  --sat_finite_models                     false
% 3.52/1.01  --sat_fm_lemmas                         false
% 3.52/1.01  --sat_fm_prep                           false
% 3.52/1.01  --sat_fm_uc_incr                        true
% 3.52/1.01  --sat_out_model                         small
% 3.52/1.01  --sat_out_clauses                       false
% 3.52/1.01  
% 3.52/1.01  ------ QBF Options
% 3.52/1.01  
% 3.52/1.01  --qbf_mode                              false
% 3.52/1.01  --qbf_elim_univ                         false
% 3.52/1.01  --qbf_dom_inst                          none
% 3.52/1.01  --qbf_dom_pre_inst                      false
% 3.52/1.01  --qbf_sk_in                             false
% 3.52/1.01  --qbf_pred_elim                         true
% 3.52/1.01  --qbf_split                             512
% 3.52/1.01  
% 3.52/1.01  ------ BMC1 Options
% 3.52/1.01  
% 3.52/1.01  --bmc1_incremental                      false
% 3.52/1.01  --bmc1_axioms                           reachable_all
% 3.52/1.01  --bmc1_min_bound                        0
% 3.52/1.01  --bmc1_max_bound                        -1
% 3.52/1.01  --bmc1_max_bound_default                -1
% 3.52/1.01  --bmc1_symbol_reachability              true
% 3.52/1.01  --bmc1_property_lemmas                  false
% 3.52/1.01  --bmc1_k_induction                      false
% 3.52/1.01  --bmc1_non_equiv_states                 false
% 3.52/1.01  --bmc1_deadlock                         false
% 3.52/1.01  --bmc1_ucm                              false
% 3.52/1.01  --bmc1_add_unsat_core                   none
% 3.52/1.01  --bmc1_unsat_core_children              false
% 3.52/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.52/1.01  --bmc1_out_stat                         full
% 3.52/1.01  --bmc1_ground_init                      false
% 3.52/1.01  --bmc1_pre_inst_next_state              false
% 3.52/1.01  --bmc1_pre_inst_state                   false
% 3.52/1.01  --bmc1_pre_inst_reach_state             false
% 3.52/1.01  --bmc1_out_unsat_core                   false
% 3.52/1.01  --bmc1_aig_witness_out                  false
% 3.52/1.01  --bmc1_verbose                          false
% 3.52/1.01  --bmc1_dump_clauses_tptp                false
% 3.52/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.52/1.01  --bmc1_dump_file                        -
% 3.52/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.52/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.52/1.01  --bmc1_ucm_extend_mode                  1
% 3.52/1.01  --bmc1_ucm_init_mode                    2
% 3.52/1.01  --bmc1_ucm_cone_mode                    none
% 3.52/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.52/1.01  --bmc1_ucm_relax_model                  4
% 3.52/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.52/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.52/1.01  --bmc1_ucm_layered_model                none
% 3.52/1.01  --bmc1_ucm_max_lemma_size               10
% 3.52/1.01  
% 3.52/1.01  ------ AIG Options
% 3.52/1.01  
% 3.52/1.01  --aig_mode                              false
% 3.52/1.01  
% 3.52/1.01  ------ Instantiation Options
% 3.52/1.01  
% 3.52/1.01  --instantiation_flag                    true
% 3.52/1.01  --inst_sos_flag                         false
% 3.52/1.01  --inst_sos_phase                        true
% 3.52/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.52/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.52/1.01  --inst_lit_sel_side                     num_symb
% 3.52/1.01  --inst_solver_per_active                1400
% 3.52/1.01  --inst_solver_calls_frac                1.
% 3.52/1.01  --inst_passive_queue_type               priority_queues
% 3.52/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.52/1.01  --inst_passive_queues_freq              [25;2]
% 3.52/1.01  --inst_dismatching                      true
% 3.52/1.01  --inst_eager_unprocessed_to_passive     true
% 3.52/1.01  --inst_prop_sim_given                   true
% 3.52/1.01  --inst_prop_sim_new                     false
% 3.52/1.01  --inst_subs_new                         false
% 3.52/1.01  --inst_eq_res_simp                      false
% 3.52/1.01  --inst_subs_given                       false
% 3.52/1.01  --inst_orphan_elimination               true
% 3.52/1.01  --inst_learning_loop_flag               true
% 3.52/1.01  --inst_learning_start                   3000
% 3.52/1.01  --inst_learning_factor                  2
% 3.52/1.01  --inst_start_prop_sim_after_learn       3
% 3.52/1.01  --inst_sel_renew                        solver
% 3.52/1.01  --inst_lit_activity_flag                true
% 3.52/1.01  --inst_restr_to_given                   false
% 3.52/1.01  --inst_activity_threshold               500
% 3.52/1.01  --inst_out_proof                        true
% 3.52/1.01  
% 3.52/1.01  ------ Resolution Options
% 3.52/1.01  
% 3.52/1.01  --resolution_flag                       true
% 3.52/1.01  --res_lit_sel                           adaptive
% 3.52/1.01  --res_lit_sel_side                      none
% 3.52/1.01  --res_ordering                          kbo
% 3.52/1.01  --res_to_prop_solver                    active
% 3.52/1.01  --res_prop_simpl_new                    false
% 3.52/1.01  --res_prop_simpl_given                  true
% 3.52/1.01  --res_passive_queue_type                priority_queues
% 3.52/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.52/1.01  --res_passive_queues_freq               [15;5]
% 3.52/1.01  --res_forward_subs                      full
% 3.52/1.01  --res_backward_subs                     full
% 3.52/1.01  --res_forward_subs_resolution           true
% 3.52/1.01  --res_backward_subs_resolution          true
% 3.52/1.01  --res_orphan_elimination                true
% 3.52/1.01  --res_time_limit                        2.
% 3.52/1.01  --res_out_proof                         true
% 3.52/1.01  
% 3.52/1.01  ------ Superposition Options
% 3.52/1.01  
% 3.52/1.01  --superposition_flag                    true
% 3.52/1.01  --sup_passive_queue_type                priority_queues
% 3.52/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.52/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.52/1.01  --demod_completeness_check              fast
% 3.52/1.01  --demod_use_ground                      true
% 3.52/1.01  --sup_to_prop_solver                    passive
% 3.52/1.01  --sup_prop_simpl_new                    true
% 3.52/1.01  --sup_prop_simpl_given                  true
% 3.52/1.01  --sup_fun_splitting                     false
% 3.52/1.01  --sup_smt_interval                      50000
% 3.52/1.01  
% 3.52/1.01  ------ Superposition Simplification Setup
% 3.52/1.01  
% 3.52/1.01  --sup_indices_passive                   []
% 3.52/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.52/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.52/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.52/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.52/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.52/1.01  --sup_full_bw                           [BwDemod]
% 3.52/1.01  --sup_immed_triv                        [TrivRules]
% 3.52/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.52/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.52/1.01  --sup_immed_bw_main                     []
% 3.52/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.52/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.52/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.52/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.52/1.01  
% 3.52/1.01  ------ Combination Options
% 3.52/1.01  
% 3.52/1.01  --comb_res_mult                         3
% 3.52/1.01  --comb_sup_mult                         2
% 3.52/1.01  --comb_inst_mult                        10
% 3.52/1.01  
% 3.52/1.01  ------ Debug Options
% 3.52/1.01  
% 3.52/1.01  --dbg_backtrace                         false
% 3.52/1.01  --dbg_dump_prop_clauses                 false
% 3.52/1.01  --dbg_dump_prop_clauses_file            -
% 3.52/1.01  --dbg_out_stat                          false
% 3.52/1.01  ------ Parsing...
% 3.52/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.52/1.01  
% 3.52/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 3.52/1.01  
% 3.52/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.52/1.01  
% 3.52/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.52/1.01  ------ Proving...
% 3.52/1.01  ------ Problem Properties 
% 3.52/1.01  
% 3.52/1.01  
% 3.52/1.01  clauses                                 42
% 3.52/1.01  conjectures                             3
% 3.52/1.01  EPR                                     6
% 3.52/1.01  Horn                                    35
% 3.52/1.01  unary                                   12
% 3.52/1.01  binary                                  9
% 3.52/1.01  lits                                    114
% 3.52/1.01  lits eq                                 46
% 3.52/1.01  fd_pure                                 0
% 3.52/1.01  fd_pseudo                               0
% 3.52/1.01  fd_cond                                 5
% 3.52/1.01  fd_pseudo_cond                          1
% 3.52/1.01  AC symbols                              0
% 3.52/1.01  
% 3.52/1.01  ------ Schedule dynamic 5 is on 
% 3.52/1.01  
% 3.52/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.52/1.01  
% 3.52/1.01  
% 3.52/1.01  ------ 
% 3.52/1.01  Current options:
% 3.52/1.01  ------ 
% 3.52/1.01  
% 3.52/1.01  ------ Input Options
% 3.52/1.01  
% 3.52/1.01  --out_options                           all
% 3.52/1.01  --tptp_safe_out                         true
% 3.52/1.01  --problem_path                          ""
% 3.52/1.01  --include_path                          ""
% 3.52/1.01  --clausifier                            res/vclausify_rel
% 3.52/1.01  --clausifier_options                    --mode clausify
% 3.52/1.01  --stdin                                 false
% 3.52/1.01  --stats_out                             all
% 3.52/1.01  
% 3.52/1.01  ------ General Options
% 3.52/1.01  
% 3.52/1.01  --fof                                   false
% 3.52/1.01  --time_out_real                         305.
% 3.52/1.01  --time_out_virtual                      -1.
% 3.52/1.01  --symbol_type_check                     false
% 3.52/1.01  --clausify_out                          false
% 3.52/1.01  --sig_cnt_out                           false
% 3.52/1.01  --trig_cnt_out                          false
% 3.52/1.01  --trig_cnt_out_tolerance                1.
% 3.52/1.01  --trig_cnt_out_sk_spl                   false
% 3.52/1.01  --abstr_cl_out                          false
% 3.52/1.01  
% 3.52/1.01  ------ Global Options
% 3.52/1.01  
% 3.52/1.01  --schedule                              default
% 3.52/1.01  --add_important_lit                     false
% 3.52/1.01  --prop_solver_per_cl                    1000
% 3.52/1.01  --min_unsat_core                        false
% 3.52/1.01  --soft_assumptions                      false
% 3.52/1.01  --soft_lemma_size                       3
% 3.52/1.01  --prop_impl_unit_size                   0
% 3.52/1.01  --prop_impl_unit                        []
% 3.52/1.01  --share_sel_clauses                     true
% 3.52/1.01  --reset_solvers                         false
% 3.52/1.01  --bc_imp_inh                            [conj_cone]
% 3.52/1.01  --conj_cone_tolerance                   3.
% 3.52/1.01  --extra_neg_conj                        none
% 3.52/1.01  --large_theory_mode                     true
% 3.52/1.01  --prolific_symb_bound                   200
% 3.52/1.01  --lt_threshold                          2000
% 3.52/1.01  --clause_weak_htbl                      true
% 3.52/1.01  --gc_record_bc_elim                     false
% 3.52/1.01  
% 3.52/1.01  ------ Preprocessing Options
% 3.52/1.01  
% 3.52/1.01  --preprocessing_flag                    true
% 3.52/1.01  --time_out_prep_mult                    0.1
% 3.52/1.01  --splitting_mode                        input
% 3.52/1.01  --splitting_grd                         true
% 3.52/1.01  --splitting_cvd                         false
% 3.52/1.01  --splitting_cvd_svl                     false
% 3.52/1.01  --splitting_nvd                         32
% 3.52/1.01  --sub_typing                            true
% 3.52/1.01  --prep_gs_sim                           true
% 3.52/1.01  --prep_unflatten                        true
% 3.52/1.01  --prep_res_sim                          true
% 3.52/1.01  --prep_upred                            true
% 3.52/1.01  --prep_sem_filter                       exhaustive
% 3.52/1.01  --prep_sem_filter_out                   false
% 3.52/1.01  --pred_elim                             true
% 3.52/1.01  --res_sim_input                         true
% 3.52/1.01  --eq_ax_congr_red                       true
% 3.52/1.01  --pure_diseq_elim                       true
% 3.52/1.01  --brand_transform                       false
% 3.52/1.01  --non_eq_to_eq                          false
% 3.52/1.01  --prep_def_merge                        true
% 3.52/1.01  --prep_def_merge_prop_impl              false
% 3.52/1.01  --prep_def_merge_mbd                    true
% 3.52/1.01  --prep_def_merge_tr_red                 false
% 3.52/1.01  --prep_def_merge_tr_cl                  false
% 3.52/1.01  --smt_preprocessing                     true
% 3.52/1.01  --smt_ac_axioms                         fast
% 3.52/1.01  --preprocessed_out                      false
% 3.52/1.01  --preprocessed_stats                    false
% 3.52/1.01  
% 3.52/1.01  ------ Abstraction refinement Options
% 3.52/1.01  
% 3.52/1.01  --abstr_ref                             []
% 3.52/1.01  --abstr_ref_prep                        false
% 3.52/1.01  --abstr_ref_until_sat                   false
% 3.52/1.01  --abstr_ref_sig_restrict                funpre
% 3.52/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.52/1.01  --abstr_ref_under                       []
% 3.52/1.01  
% 3.52/1.01  ------ SAT Options
% 3.52/1.01  
% 3.52/1.01  --sat_mode                              false
% 3.52/1.01  --sat_fm_restart_options                ""
% 3.52/1.01  --sat_gr_def                            false
% 3.52/1.01  --sat_epr_types                         true
% 3.52/1.01  --sat_non_cyclic_types                  false
% 3.52/1.01  --sat_finite_models                     false
% 3.52/1.01  --sat_fm_lemmas                         false
% 3.52/1.01  --sat_fm_prep                           false
% 3.52/1.01  --sat_fm_uc_incr                        true
% 3.52/1.01  --sat_out_model                         small
% 3.52/1.01  --sat_out_clauses                       false
% 3.52/1.01  
% 3.52/1.01  ------ QBF Options
% 3.52/1.01  
% 3.52/1.01  --qbf_mode                              false
% 3.52/1.01  --qbf_elim_univ                         false
% 3.52/1.01  --qbf_dom_inst                          none
% 3.52/1.01  --qbf_dom_pre_inst                      false
% 3.52/1.01  --qbf_sk_in                             false
% 3.52/1.01  --qbf_pred_elim                         true
% 3.52/1.01  --qbf_split                             512
% 3.52/1.01  
% 3.52/1.01  ------ BMC1 Options
% 3.52/1.01  
% 3.52/1.01  --bmc1_incremental                      false
% 3.52/1.01  --bmc1_axioms                           reachable_all
% 3.52/1.01  --bmc1_min_bound                        0
% 3.52/1.01  --bmc1_max_bound                        -1
% 3.52/1.01  --bmc1_max_bound_default                -1
% 3.52/1.01  --bmc1_symbol_reachability              true
% 3.52/1.01  --bmc1_property_lemmas                  false
% 3.52/1.01  --bmc1_k_induction                      false
% 3.52/1.01  --bmc1_non_equiv_states                 false
% 3.52/1.01  --bmc1_deadlock                         false
% 3.52/1.01  --bmc1_ucm                              false
% 3.52/1.01  --bmc1_add_unsat_core                   none
% 3.52/1.01  --bmc1_unsat_core_children              false
% 3.52/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.52/1.01  --bmc1_out_stat                         full
% 3.52/1.01  --bmc1_ground_init                      false
% 3.52/1.01  --bmc1_pre_inst_next_state              false
% 3.52/1.01  --bmc1_pre_inst_state                   false
% 3.52/1.01  --bmc1_pre_inst_reach_state             false
% 3.52/1.01  --bmc1_out_unsat_core                   false
% 3.52/1.01  --bmc1_aig_witness_out                  false
% 3.52/1.01  --bmc1_verbose                          false
% 3.52/1.01  --bmc1_dump_clauses_tptp                false
% 3.52/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.52/1.01  --bmc1_dump_file                        -
% 3.52/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.52/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.52/1.01  --bmc1_ucm_extend_mode                  1
% 3.52/1.01  --bmc1_ucm_init_mode                    2
% 3.52/1.01  --bmc1_ucm_cone_mode                    none
% 3.52/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.52/1.01  --bmc1_ucm_relax_model                  4
% 3.52/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.52/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.52/1.01  --bmc1_ucm_layered_model                none
% 3.52/1.01  --bmc1_ucm_max_lemma_size               10
% 3.52/1.01  
% 3.52/1.01  ------ AIG Options
% 3.52/1.01  
% 3.52/1.01  --aig_mode                              false
% 3.52/1.01  
% 3.52/1.01  ------ Instantiation Options
% 3.52/1.01  
% 3.52/1.01  --instantiation_flag                    true
% 3.52/1.01  --inst_sos_flag                         false
% 3.52/1.01  --inst_sos_phase                        true
% 3.52/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.52/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.52/1.01  --inst_lit_sel_side                     none
% 3.52/1.01  --inst_solver_per_active                1400
% 3.52/1.01  --inst_solver_calls_frac                1.
% 3.52/1.01  --inst_passive_queue_type               priority_queues
% 3.52/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.52/1.01  --inst_passive_queues_freq              [25;2]
% 3.52/1.01  --inst_dismatching                      true
% 3.52/1.01  --inst_eager_unprocessed_to_passive     true
% 3.52/1.01  --inst_prop_sim_given                   true
% 3.52/1.01  --inst_prop_sim_new                     false
% 3.52/1.01  --inst_subs_new                         false
% 3.52/1.01  --inst_eq_res_simp                      false
% 3.52/1.01  --inst_subs_given                       false
% 3.52/1.01  --inst_orphan_elimination               true
% 3.52/1.01  --inst_learning_loop_flag               true
% 3.52/1.01  --inst_learning_start                   3000
% 3.52/1.01  --inst_learning_factor                  2
% 3.52/1.01  --inst_start_prop_sim_after_learn       3
% 3.52/1.01  --inst_sel_renew                        solver
% 3.52/1.01  --inst_lit_activity_flag                true
% 3.52/1.01  --inst_restr_to_given                   false
% 3.52/1.01  --inst_activity_threshold               500
% 3.52/1.01  --inst_out_proof                        true
% 3.52/1.01  
% 3.52/1.01  ------ Resolution Options
% 3.52/1.01  
% 3.52/1.01  --resolution_flag                       false
% 3.52/1.01  --res_lit_sel                           adaptive
% 3.52/1.01  --res_lit_sel_side                      none
% 3.52/1.01  --res_ordering                          kbo
% 3.52/1.01  --res_to_prop_solver                    active
% 3.52/1.01  --res_prop_simpl_new                    false
% 3.52/1.01  --res_prop_simpl_given                  true
% 3.52/1.01  --res_passive_queue_type                priority_queues
% 3.52/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.52/1.01  --res_passive_queues_freq               [15;5]
% 3.52/1.01  --res_forward_subs                      full
% 3.52/1.01  --res_backward_subs                     full
% 3.52/1.01  --res_forward_subs_resolution           true
% 3.52/1.01  --res_backward_subs_resolution          true
% 3.52/1.01  --res_orphan_elimination                true
% 3.52/1.01  --res_time_limit                        2.
% 3.52/1.01  --res_out_proof                         true
% 3.52/1.01  
% 3.52/1.01  ------ Superposition Options
% 3.52/1.01  
% 3.52/1.01  --superposition_flag                    true
% 3.52/1.01  --sup_passive_queue_type                priority_queues
% 3.52/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.52/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.52/1.01  --demod_completeness_check              fast
% 3.52/1.01  --demod_use_ground                      true
% 3.52/1.01  --sup_to_prop_solver                    passive
% 3.52/1.01  --sup_prop_simpl_new                    true
% 3.52/1.01  --sup_prop_simpl_given                  true
% 3.52/1.01  --sup_fun_splitting                     false
% 3.52/1.01  --sup_smt_interval                      50000
% 3.52/1.01  
% 3.52/1.01  ------ Superposition Simplification Setup
% 3.52/1.01  
% 3.52/1.01  --sup_indices_passive                   []
% 3.52/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.52/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.52/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.52/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.52/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.52/1.01  --sup_full_bw                           [BwDemod]
% 3.52/1.01  --sup_immed_triv                        [TrivRules]
% 3.52/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.52/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.52/1.01  --sup_immed_bw_main                     []
% 3.52/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.52/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.52/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.52/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.52/1.01  
% 3.52/1.01  ------ Combination Options
% 3.52/1.01  
% 3.52/1.01  --comb_res_mult                         3
% 3.52/1.01  --comb_sup_mult                         2
% 3.52/1.01  --comb_inst_mult                        10
% 3.52/1.01  
% 3.52/1.01  ------ Debug Options
% 3.52/1.01  
% 3.52/1.01  --dbg_backtrace                         false
% 3.52/1.01  --dbg_dump_prop_clauses                 false
% 3.52/1.01  --dbg_dump_prop_clauses_file            -
% 3.52/1.01  --dbg_out_stat                          false
% 3.52/1.01  
% 3.52/1.01  
% 3.52/1.01  
% 3.52/1.01  
% 3.52/1.01  ------ Proving...
% 3.52/1.01  
% 3.52/1.01  
% 3.52/1.01  % SZS status Theorem for theBenchmark.p
% 3.52/1.01  
% 3.52/1.01   Resolution empty clause
% 3.52/1.01  
% 3.52/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.52/1.01  
% 3.52/1.01  fof(f21,conjecture,(
% 3.52/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.52/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/1.01  
% 3.52/1.01  fof(f22,negated_conjecture,(
% 3.52/1.01    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.52/1.01    inference(negated_conjecture,[],[f21])).
% 3.52/1.01  
% 3.52/1.01  fof(f41,plain,(
% 3.52/1.01    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.52/1.01    inference(ennf_transformation,[],[f22])).
% 3.52/1.01  
% 3.52/1.01  fof(f42,plain,(
% 3.52/1.01    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.52/1.01    inference(flattening,[],[f41])).
% 3.52/1.01  
% 3.52/1.01  fof(f49,plain,(
% 3.52/1.01    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 3.52/1.01    introduced(choice_axiom,[])).
% 3.52/1.01  
% 3.52/1.01  fof(f50,plain,(
% 3.52/1.01    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 3.52/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f42,f49])).
% 3.52/1.01  
% 3.52/1.01  fof(f89,plain,(
% 3.52/1.01    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.52/1.01    inference(cnf_transformation,[],[f50])).
% 3.52/1.01  
% 3.52/1.01  fof(f15,axiom,(
% 3.52/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.52/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/1.01  
% 3.52/1.01  fof(f34,plain,(
% 3.52/1.01    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.52/1.01    inference(ennf_transformation,[],[f15])).
% 3.52/1.01  
% 3.52/1.01  fof(f72,plain,(
% 3.52/1.01    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.52/1.01    inference(cnf_transformation,[],[f34])).
% 3.52/1.01  
% 3.52/1.01  fof(f91,plain,(
% 3.52/1.01    k2_relset_1(sK0,sK1,sK2) = sK1),
% 3.52/1.01    inference(cnf_transformation,[],[f50])).
% 3.52/1.01  
% 3.52/1.01  fof(f13,axiom,(
% 3.52/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.52/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/1.01  
% 3.52/1.01  fof(f32,plain,(
% 3.52/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.52/1.01    inference(ennf_transformation,[],[f13])).
% 3.52/1.01  
% 3.52/1.01  fof(f70,plain,(
% 3.52/1.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.52/1.01    inference(cnf_transformation,[],[f32])).
% 3.52/1.01  
% 3.52/1.01  fof(f12,axiom,(
% 3.52/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 3.52/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/1.01  
% 3.52/1.01  fof(f30,plain,(
% 3.52/1.01    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.52/1.01    inference(ennf_transformation,[],[f12])).
% 3.52/1.01  
% 3.52/1.01  fof(f31,plain,(
% 3.52/1.01    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.52/1.01    inference(flattening,[],[f30])).
% 3.52/1.01  
% 3.52/1.01  fof(f68,plain,(
% 3.52/1.01    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.52/1.01    inference(cnf_transformation,[],[f31])).
% 3.52/1.01  
% 3.52/1.01  fof(f90,plain,(
% 3.52/1.01    v2_funct_1(sK2)),
% 3.52/1.01    inference(cnf_transformation,[],[f50])).
% 3.52/1.01  
% 3.52/1.01  fof(f87,plain,(
% 3.52/1.01    v1_funct_1(sK2)),
% 3.52/1.01    inference(cnf_transformation,[],[f50])).
% 3.52/1.01  
% 3.52/1.01  fof(f20,axiom,(
% 3.52/1.01    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 3.52/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/1.01  
% 3.52/1.01  fof(f39,plain,(
% 3.52/1.01    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.52/1.01    inference(ennf_transformation,[],[f20])).
% 3.52/1.01  
% 3.52/1.01  fof(f40,plain,(
% 3.52/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.52/1.01    inference(flattening,[],[f39])).
% 3.52/1.01  
% 3.52/1.01  fof(f86,plain,(
% 3.52/1.01    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.52/1.01    inference(cnf_transformation,[],[f40])).
% 3.52/1.01  
% 3.52/1.01  fof(f69,plain,(
% 3.52/1.01    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.52/1.01    inference(cnf_transformation,[],[f31])).
% 3.52/1.01  
% 3.52/1.01  fof(f11,axiom,(
% 3.52/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.52/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/1.01  
% 3.52/1.01  fof(f28,plain,(
% 3.52/1.01    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.52/1.01    inference(ennf_transformation,[],[f11])).
% 3.52/1.01  
% 3.52/1.01  fof(f29,plain,(
% 3.52/1.01    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.52/1.01    inference(flattening,[],[f28])).
% 3.52/1.01  
% 3.52/1.01  fof(f67,plain,(
% 3.52/1.01    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.52/1.01    inference(cnf_transformation,[],[f29])).
% 3.52/1.01  
% 3.52/1.01  fof(f66,plain,(
% 3.52/1.01    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.52/1.01    inference(cnf_transformation,[],[f29])).
% 3.52/1.01  
% 3.52/1.01  fof(f85,plain,(
% 3.52/1.01    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.52/1.01    inference(cnf_transformation,[],[f40])).
% 3.52/1.01  
% 3.52/1.01  fof(f92,plain,(
% 3.52/1.01    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 3.52/1.01    inference(cnf_transformation,[],[f50])).
% 3.52/1.01  
% 3.52/1.01  fof(f4,axiom,(
% 3.52/1.01    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.52/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/1.01  
% 3.52/1.01  fof(f45,plain,(
% 3.52/1.01    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.52/1.01    inference(nnf_transformation,[],[f4])).
% 3.52/1.01  
% 3.52/1.01  fof(f46,plain,(
% 3.52/1.01    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.52/1.01    inference(flattening,[],[f45])).
% 3.52/1.01  
% 3.52/1.01  fof(f58,plain,(
% 3.52/1.01    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.52/1.01    inference(cnf_transformation,[],[f46])).
% 3.52/1.01  
% 3.52/1.01  fof(f97,plain,(
% 3.52/1.01    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.52/1.01    inference(equality_resolution,[],[f58])).
% 3.52/1.01  
% 3.52/1.01  fof(f17,axiom,(
% 3.52/1.01    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 3.52/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/1.01  
% 3.52/1.01  fof(f23,plain,(
% 3.52/1.01    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.52/1.01    inference(pure_predicate_removal,[],[f17])).
% 3.52/1.01  
% 3.52/1.01  fof(f79,plain,(
% 3.52/1.01    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.52/1.01    inference(cnf_transformation,[],[f23])).
% 3.52/1.01  
% 3.52/1.01  fof(f6,axiom,(
% 3.52/1.01    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.52/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/1.01  
% 3.52/1.01  fof(f47,plain,(
% 3.52/1.01    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.52/1.01    inference(nnf_transformation,[],[f6])).
% 3.52/1.01  
% 3.52/1.01  fof(f60,plain,(
% 3.52/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.52/1.01    inference(cnf_transformation,[],[f47])).
% 3.52/1.01  
% 3.52/1.01  fof(f3,axiom,(
% 3.52/1.01    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 3.52/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/1.01  
% 3.52/1.01  fof(f25,plain,(
% 3.52/1.01    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 3.52/1.01    inference(ennf_transformation,[],[f3])).
% 3.52/1.01  
% 3.52/1.01  fof(f55,plain,(
% 3.52/1.01    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 3.52/1.01    inference(cnf_transformation,[],[f25])).
% 3.52/1.01  
% 3.52/1.01  fof(f9,axiom,(
% 3.52/1.01    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.52/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/1.01  
% 3.52/1.01  fof(f63,plain,(
% 3.52/1.01    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 3.52/1.01    inference(cnf_transformation,[],[f9])).
% 3.52/1.01  
% 3.52/1.01  fof(f18,axiom,(
% 3.52/1.01    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.52/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/1.01  
% 3.52/1.01  fof(f80,plain,(
% 3.52/1.01    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.52/1.01    inference(cnf_transformation,[],[f18])).
% 3.52/1.01  
% 3.52/1.01  fof(f94,plain,(
% 3.52/1.01    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 3.52/1.01    inference(definition_unfolding,[],[f63,f80])).
% 3.52/1.01  
% 3.52/1.01  fof(f16,axiom,(
% 3.52/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.52/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/1.01  
% 3.52/1.01  fof(f35,plain,(
% 3.52/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.52/1.01    inference(ennf_transformation,[],[f16])).
% 3.52/1.01  
% 3.52/1.01  fof(f36,plain,(
% 3.52/1.01    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.52/1.01    inference(flattening,[],[f35])).
% 3.52/1.01  
% 3.52/1.01  fof(f48,plain,(
% 3.52/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.52/1.01    inference(nnf_transformation,[],[f36])).
% 3.52/1.01  
% 3.52/1.01  fof(f73,plain,(
% 3.52/1.01    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.52/1.01    inference(cnf_transformation,[],[f48])).
% 3.52/1.01  
% 3.52/1.01  fof(f88,plain,(
% 3.52/1.01    v1_funct_2(sK2,sK0,sK1)),
% 3.52/1.01    inference(cnf_transformation,[],[f50])).
% 3.52/1.01  
% 3.52/1.01  fof(f14,axiom,(
% 3.52/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.52/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/1.01  
% 3.52/1.01  fof(f33,plain,(
% 3.52/1.01    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.52/1.01    inference(ennf_transformation,[],[f14])).
% 3.52/1.01  
% 3.52/1.01  fof(f71,plain,(
% 3.52/1.01    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.52/1.01    inference(cnf_transformation,[],[f33])).
% 3.52/1.01  
% 3.52/1.01  fof(f19,axiom,(
% 3.52/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 3.52/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/1.01  
% 3.52/1.01  fof(f37,plain,(
% 3.52/1.01    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.52/1.01    inference(ennf_transformation,[],[f19])).
% 3.52/1.01  
% 3.52/1.01  fof(f38,plain,(
% 3.52/1.01    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.52/1.01    inference(flattening,[],[f37])).
% 3.52/1.01  
% 3.52/1.01  fof(f83,plain,(
% 3.52/1.01    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.52/1.01    inference(cnf_transformation,[],[f38])).
% 3.52/1.01  
% 3.52/1.01  fof(f82,plain,(
% 3.52/1.01    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.52/1.01    inference(cnf_transformation,[],[f38])).
% 3.52/1.01  
% 3.52/1.01  fof(f77,plain,(
% 3.52/1.01    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.52/1.01    inference(cnf_transformation,[],[f48])).
% 3.52/1.01  
% 3.52/1.01  fof(f101,plain,(
% 3.52/1.01    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.52/1.01    inference(equality_resolution,[],[f77])).
% 3.52/1.01  
% 3.52/1.01  fof(f2,axiom,(
% 3.52/1.01    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.52/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/1.01  
% 3.52/1.01  fof(f54,plain,(
% 3.52/1.01    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.52/1.01    inference(cnf_transformation,[],[f2])).
% 3.52/1.01  
% 3.52/1.01  fof(f1,axiom,(
% 3.52/1.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.52/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.52/1.01  
% 3.52/1.01  fof(f43,plain,(
% 3.52/1.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.52/1.01    inference(nnf_transformation,[],[f1])).
% 3.52/1.01  
% 3.52/1.01  fof(f44,plain,(
% 3.52/1.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.52/1.01    inference(flattening,[],[f43])).
% 3.52/1.01  
% 3.52/1.01  fof(f53,plain,(
% 3.52/1.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.52/1.01    inference(cnf_transformation,[],[f44])).
% 3.52/1.01  
% 3.52/1.01  cnf(c_38,negated_conjecture,
% 3.52/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.52/1.01      inference(cnf_transformation,[],[f89]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_1677,plain,
% 3.52/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.52/1.01      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_21,plain,
% 3.52/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.52/1.01      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.52/1.01      inference(cnf_transformation,[],[f72]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_1681,plain,
% 3.52/1.01      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.52/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.52/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_3613,plain,
% 3.52/1.01      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 3.52/1.01      inference(superposition,[status(thm)],[c_1677,c_1681]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_36,negated_conjecture,
% 3.52/1.01      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 3.52/1.01      inference(cnf_transformation,[],[f91]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_3625,plain,
% 3.52/1.01      ( k2_relat_1(sK2) = sK1 ),
% 3.52/1.01      inference(light_normalisation,[status(thm)],[c_3613,c_36]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_19,plain,
% 3.52/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 3.52/1.01      inference(cnf_transformation,[],[f70]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_1683,plain,
% 3.52/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.52/1.01      | v1_relat_1(X0) = iProver_top ),
% 3.52/1.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_3142,plain,
% 3.52/1.01      ( v1_relat_1(sK2) = iProver_top ),
% 3.52/1.01      inference(superposition,[status(thm)],[c_1677,c_1683]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_18,plain,
% 3.52/1.01      ( ~ v2_funct_1(X0)
% 3.52/1.01      | ~ v1_funct_1(X0)
% 3.52/1.01      | ~ v1_relat_1(X0)
% 3.52/1.01      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 3.52/1.01      inference(cnf_transformation,[],[f68]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_37,negated_conjecture,
% 3.52/1.01      ( v2_funct_1(sK2) ),
% 3.52/1.01      inference(cnf_transformation,[],[f90]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_448,plain,
% 3.52/1.01      ( ~ v1_funct_1(X0)
% 3.52/1.01      | ~ v1_relat_1(X0)
% 3.52/1.01      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 3.52/1.01      | sK2 != X0 ),
% 3.52/1.01      inference(resolution_lifted,[status(thm)],[c_18,c_37]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_449,plain,
% 3.52/1.01      ( ~ v1_funct_1(sK2)
% 3.52/1.01      | ~ v1_relat_1(sK2)
% 3.52/1.01      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 3.52/1.01      inference(unflattening,[status(thm)],[c_448]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_40,negated_conjecture,
% 3.52/1.01      ( v1_funct_1(sK2) ),
% 3.52/1.01      inference(cnf_transformation,[],[f87]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_451,plain,
% 3.52/1.01      ( ~ v1_relat_1(sK2) | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 3.52/1.01      inference(global_propositional_subsumption,[status(thm)],[c_449,c_40]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_1674,plain,
% 3.52/1.01      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 3.52/1.01      | v1_relat_1(sK2) != iProver_top ),
% 3.52/1.01      inference(predicate_to_equality,[status(thm)],[c_451]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_3165,plain,
% 3.52/1.01      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 3.52/1.01      inference(superposition,[status(thm)],[c_3142,c_1674]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_3756,plain,
% 3.52/1.01      ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
% 3.52/1.01      inference(demodulation,[status(thm)],[c_3625,c_3165]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_32,plain,
% 3.52/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.52/1.01      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.52/1.01      | ~ v1_funct_1(X0)
% 3.52/1.01      | ~ v1_relat_1(X0) ),
% 3.52/1.01      inference(cnf_transformation,[],[f86]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_1678,plain,
% 3.52/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
% 3.52/1.01      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 3.52/1.01      | v1_funct_1(X0) != iProver_top
% 3.52/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.52/1.01      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_4917,plain,
% 3.52/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
% 3.52/1.01      | r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0) != iProver_top
% 3.52/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.52/1.01      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.52/1.01      inference(superposition,[status(thm)],[c_3756,c_1678]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_17,plain,
% 3.52/1.01      ( ~ v2_funct_1(X0)
% 3.52/1.01      | ~ v1_funct_1(X0)
% 3.52/1.01      | ~ v1_relat_1(X0)
% 3.52/1.01      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 3.52/1.01      inference(cnf_transformation,[],[f69]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_462,plain,
% 3.52/1.01      ( ~ v1_funct_1(X0)
% 3.52/1.01      | ~ v1_relat_1(X0)
% 3.52/1.01      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 3.52/1.01      | sK2 != X0 ),
% 3.52/1.01      inference(resolution_lifted,[status(thm)],[c_17,c_37]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_463,plain,
% 3.52/1.01      ( ~ v1_funct_1(sK2)
% 3.52/1.01      | ~ v1_relat_1(sK2)
% 3.52/1.01      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.52/1.01      inference(unflattening,[status(thm)],[c_462]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_465,plain,
% 3.52/1.01      ( ~ v1_relat_1(sK2) | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.52/1.01      inference(global_propositional_subsumption,[status(thm)],[c_463,c_40]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_1673,plain,
% 3.52/1.01      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 3.52/1.01      | v1_relat_1(sK2) != iProver_top ),
% 3.52/1.01      inference(predicate_to_equality,[status(thm)],[c_465]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_3166,plain,
% 3.52/1.01      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.52/1.01      inference(superposition,[status(thm)],[c_3142,c_1673]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_4962,plain,
% 3.52/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
% 3.52/1.01      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top
% 3.52/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.52/1.01      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.52/1.01      inference(light_normalisation,[status(thm)],[c_4917,c_3166]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_41,plain,
% 3.52/1.01      ( v1_funct_1(sK2) = iProver_top ),
% 3.52/1.01      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_43,plain,
% 3.52/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.52/1.01      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_15,plain,
% 3.52/1.01      ( ~ v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0)) | ~ v1_relat_1(X0) ),
% 3.52/1.01      inference(cnf_transformation,[],[f67]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_2013,plain,
% 3.52/1.01      ( v1_funct_1(k2_funct_1(sK2)) | ~ v1_funct_1(sK2) | ~ v1_relat_1(sK2) ),
% 3.52/1.01      inference(instantiation,[status(thm)],[c_15]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_2014,plain,
% 3.52/1.01      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 3.52/1.01      | v1_funct_1(sK2) != iProver_top
% 3.52/1.01      | v1_relat_1(sK2) != iProver_top ),
% 3.52/1.01      inference(predicate_to_equality,[status(thm)],[c_2013]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_16,plain,
% 3.52/1.01      ( ~ v1_funct_1(X0) | ~ v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0)) ),
% 3.52/1.01      inference(cnf_transformation,[],[f66]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_2016,plain,
% 3.52/1.01      ( ~ v1_funct_1(sK2) | v1_relat_1(k2_funct_1(sK2)) | ~ v1_relat_1(sK2) ),
% 3.52/1.01      inference(instantiation,[status(thm)],[c_16]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_2017,plain,
% 3.52/1.01      ( v1_funct_1(sK2) != iProver_top
% 3.52/1.01      | v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 3.52/1.01      | v1_relat_1(sK2) != iProver_top ),
% 3.52/1.01      inference(predicate_to_equality,[status(thm)],[c_2016]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_2041,plain,
% 3.52/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.52/1.01      | v1_relat_1(sK2) ),
% 3.52/1.01      inference(instantiation,[status(thm)],[c_19]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_2042,plain,
% 3.52/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.52/1.01      | v1_relat_1(sK2) = iProver_top ),
% 3.52/1.01      inference(predicate_to_equality,[status(thm)],[c_2041]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_5624,plain,
% 3.52/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
% 3.52/1.01      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
% 3.52/1.01      inference(global_propositional_subsumption,
% 3.52/1.01                [status(thm)],
% 3.52/1.01                [c_4962,c_41,c_43,c_2014,c_2017,c_2042]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_33,plain,
% 3.52/1.01      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 3.52/1.01      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.52/1.01      | ~ v1_funct_1(X0)
% 3.52/1.01      | ~ v1_relat_1(X0) ),
% 3.52/1.01      inference(cnf_transformation,[],[f85]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_35,negated_conjecture,
% 3.52/1.01      ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
% 3.52/1.01      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.52/1.01      | ~ v1_funct_1(k2_funct_1(sK2)) ),
% 3.52/1.01      inference(cnf_transformation,[],[f92]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_766,plain,
% 3.52/1.01      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.52/1.01      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.52/1.01      | ~ v1_funct_1(X0)
% 3.52/1.01      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.52/1.01      | ~ v1_relat_1(X0)
% 3.52/1.01      | k2_funct_1(sK2) != X0
% 3.52/1.01      | k1_relat_1(X0) != sK1
% 3.52/1.01      | sK0 != X1 ),
% 3.52/1.01      inference(resolution_lifted,[status(thm)],[c_33,c_35]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_767,plain,
% 3.52/1.01      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.52/1.01      | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)
% 3.52/1.01      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.52/1.01      | ~ v1_relat_1(k2_funct_1(sK2))
% 3.52/1.01      | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
% 3.52/1.01      inference(unflattening,[status(thm)],[c_766]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_779,plain,
% 3.52/1.01      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.52/1.01      | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)
% 3.52/1.01      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.52/1.01      | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
% 3.52/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_767,c_19]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_1660,plain,
% 3.52/1.01      ( k1_relat_1(k2_funct_1(sK2)) != sK1
% 3.52/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.52/1.01      | r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) != iProver_top
% 3.52/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.52/1.01      inference(predicate_to_equality,[status(thm)],[c_779]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_768,plain,
% 3.52/1.01      ( k1_relat_1(k2_funct_1(sK2)) != sK1
% 3.52/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.52/1.01      | r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) != iProver_top
% 3.52/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.52/1.01      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.52/1.01      inference(predicate_to_equality,[status(thm)],[c_767]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_2120,plain,
% 3.52/1.01      ( r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) != iProver_top
% 3.52/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.52/1.01      | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
% 3.52/1.01      inference(global_propositional_subsumption,
% 3.52/1.01                [status(thm)],
% 3.52/1.01                [c_1660,c_41,c_43,c_768,c_2014,c_2017,c_2042]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_2121,plain,
% 3.52/1.01      ( k1_relat_1(k2_funct_1(sK2)) != sK1
% 3.52/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.52/1.01      | r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) != iProver_top ),
% 3.52/1.01      inference(renaming,[status(thm)],[c_2120]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_3261,plain,
% 3.52/1.01      ( k2_relat_1(sK2) != sK1
% 3.52/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.52/1.01      | r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) != iProver_top ),
% 3.52/1.01      inference(demodulation,[status(thm)],[c_3165,c_2121]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_3407,plain,
% 3.52/1.01      ( k2_relat_1(sK2) != sK1
% 3.52/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.52/1.01      | r1_tarski(k1_relat_1(sK2),sK0) != iProver_top ),
% 3.52/1.01      inference(light_normalisation,[status(thm)],[c_3261,c_3166]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_3754,plain,
% 3.52/1.01      ( sK1 != sK1
% 3.52/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.52/1.01      | r1_tarski(k1_relat_1(sK2),sK0) != iProver_top ),
% 3.52/1.01      inference(demodulation,[status(thm)],[c_3625,c_3407]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_3769,plain,
% 3.52/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.52/1.01      | r1_tarski(k1_relat_1(sK2),sK0) != iProver_top ),
% 3.52/1.01      inference(equality_resolution_simp,[status(thm)],[c_3754]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_5639,plain,
% 3.52/1.01      ( r1_tarski(k1_relat_1(sK2),sK0) != iProver_top ),
% 3.52/1.01      inference(superposition,[status(thm)],[c_5624,c_3769]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_5,plain,
% 3.52/1.01      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.52/1.01      inference(cnf_transformation,[],[f97]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_28,plain,
% 3.52/1.01      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.52/1.01      inference(cnf_transformation,[],[f79]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_1680,plain,
% 3.52/1.01      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 3.52/1.01      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_2623,plain,
% 3.52/1.01      ( m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.52/1.01      inference(superposition,[status(thm)],[c_5,c_1680]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_10,plain,
% 3.52/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.52/1.01      inference(cnf_transformation,[],[f60]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_1687,plain,
% 3.52/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.52/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 3.52/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_2766,plain,
% 3.52/1.01      ( r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0) = iProver_top ),
% 3.52/1.01      inference(superposition,[status(thm)],[c_2623,c_1687]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_4,plain,
% 3.52/1.01      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 3.52/1.01      inference(cnf_transformation,[],[f55]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_1690,plain,
% 3.52/1.01      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.52/1.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_2858,plain,
% 3.52/1.01      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 3.52/1.01      inference(superposition,[status(thm)],[c_2766,c_1690]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_13,plain,
% 3.52/1.01      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 3.52/1.01      inference(cnf_transformation,[],[f94]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_2865,plain,
% 3.52/1.01      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.52/1.01      inference(superposition,[status(thm)],[c_2858,c_13]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_27,plain,
% 3.52/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 3.52/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.52/1.01      | k1_relset_1(X1,X2,X0) = X1
% 3.52/1.01      | k1_xboole_0 = X2 ),
% 3.52/1.01      inference(cnf_transformation,[],[f73]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_39,negated_conjecture,
% 3.52/1.01      ( v1_funct_2(sK2,sK0,sK1) ),
% 3.52/1.01      inference(cnf_transformation,[],[f88]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_736,plain,
% 3.52/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.52/1.01      | k1_relset_1(X1,X2,X0) = X1
% 3.52/1.01      | sK0 != X1
% 3.52/1.01      | sK1 != X2
% 3.52/1.01      | sK2 != X0
% 3.52/1.01      | k1_xboole_0 = X2 ),
% 3.52/1.01      inference(resolution_lifted,[status(thm)],[c_27,c_39]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_737,plain,
% 3.52/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.52/1.01      | k1_relset_1(sK0,sK1,sK2) = sK0
% 3.52/1.01      | k1_xboole_0 = sK1 ),
% 3.52/1.01      inference(unflattening,[status(thm)],[c_736]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_739,plain,
% 3.52/1.01      ( k1_relset_1(sK0,sK1,sK2) = sK0 | k1_xboole_0 = sK1 ),
% 3.52/1.01      inference(global_propositional_subsumption,[status(thm)],[c_737,c_38]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_20,plain,
% 3.52/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.52/1.01      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.52/1.01      inference(cnf_transformation,[],[f71]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_1682,plain,
% 3.52/1.01      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.52/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.52/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_4421,plain,
% 3.52/1.01      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 3.52/1.01      inference(superposition,[status(thm)],[c_1677,c_1682]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_4483,plain,
% 3.52/1.01      ( k1_relat_1(sK2) = sK0 | sK1 = k1_xboole_0 ),
% 3.52/1.01      inference(superposition,[status(thm)],[c_739,c_4421]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_29,plain,
% 3.52/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 3.52/1.01      | ~ v1_funct_1(X0)
% 3.52/1.01      | ~ v1_relat_1(X0) ),
% 3.52/1.01      inference(cnf_transformation,[],[f83]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_1679,plain,
% 3.52/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 3.52/1.01      | v1_funct_1(X0) != iProver_top
% 3.52/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.52/1.01      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_5822,plain,
% 3.52/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) = iProver_top
% 3.52/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.52/1.01      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.52/1.01      inference(superposition,[status(thm)],[c_3166,c_1679]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_5848,plain,
% 3.52/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top
% 3.52/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.52/1.01      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.52/1.01      inference(light_normalisation,[status(thm)],[c_5822,c_3756]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_8514,plain,
% 3.52/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top ),
% 3.52/1.01      inference(global_propositional_subsumption,
% 3.52/1.01                [status(thm)],
% 3.52/1.01                [c_5848,c_41,c_43,c_2014,c_2017,c_2042]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_8519,plain,
% 3.52/1.01      ( sK1 = k1_xboole_0
% 3.52/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.52/1.01      inference(superposition,[status(thm)],[c_4483,c_8514]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_30,plain,
% 3.52/1.01      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 3.52/1.01      | ~ v1_funct_1(X0)
% 3.52/1.01      | ~ v1_relat_1(X0) ),
% 3.52/1.01      inference(cnf_transformation,[],[f82]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_747,plain,
% 3.52/1.01      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.52/1.01      | ~ v1_funct_1(X0)
% 3.52/1.01      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.52/1.01      | ~ v1_relat_1(X0)
% 3.52/1.01      | k2_funct_1(sK2) != X0
% 3.52/1.01      | k1_relat_1(X0) != sK1
% 3.52/1.01      | k2_relat_1(X0) != sK0 ),
% 3.52/1.01      inference(resolution_lifted,[status(thm)],[c_30,c_35]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_748,plain,
% 3.52/1.01      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.52/1.01      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.52/1.01      | ~ v1_relat_1(k2_funct_1(sK2))
% 3.52/1.01      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 3.52/1.01      | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
% 3.52/1.01      inference(unflattening,[status(thm)],[c_747]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_760,plain,
% 3.52/1.01      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.52/1.01      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.52/1.01      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 3.52/1.01      | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
% 3.52/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_748,c_19]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_1661,plain,
% 3.52/1.01      ( k1_relat_1(k2_funct_1(sK2)) != sK1
% 3.52/1.01      | k2_relat_1(k2_funct_1(sK2)) != sK0
% 3.52/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.52/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.52/1.01      inference(predicate_to_equality,[status(thm)],[c_760]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_749,plain,
% 3.52/1.01      ( k1_relat_1(k2_funct_1(sK2)) != sK1
% 3.52/1.01      | k2_relat_1(k2_funct_1(sK2)) != sK0
% 3.52/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.52/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.52/1.01      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.52/1.01      inference(predicate_to_equality,[status(thm)],[c_748]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_2317,plain,
% 3.52/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.52/1.01      | k2_relat_1(k2_funct_1(sK2)) != sK0
% 3.52/1.01      | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
% 3.52/1.01      inference(global_propositional_subsumption,
% 3.52/1.01                [status(thm)],
% 3.52/1.01                [c_1661,c_41,c_43,c_749,c_2014,c_2017,c_2042]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_2318,plain,
% 3.52/1.01      ( k1_relat_1(k2_funct_1(sK2)) != sK1
% 3.52/1.01      | k2_relat_1(k2_funct_1(sK2)) != sK0
% 3.52/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 3.52/1.01      inference(renaming,[status(thm)],[c_2317]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_3260,plain,
% 3.52/1.01      ( k2_relat_1(k2_funct_1(sK2)) != sK0
% 3.52/1.01      | k2_relat_1(sK2) != sK1
% 3.52/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 3.52/1.01      inference(demodulation,[status(thm)],[c_3165,c_2318]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_3367,plain,
% 3.52/1.01      ( k1_relat_1(sK2) != sK0
% 3.52/1.01      | k2_relat_1(sK2) != sK1
% 3.52/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 3.52/1.01      inference(light_normalisation,[status(thm)],[c_3260,c_3166]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_3755,plain,
% 3.52/1.01      ( k1_relat_1(sK2) != sK0
% 3.52/1.01      | sK1 != sK1
% 3.52/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 3.52/1.01      inference(demodulation,[status(thm)],[c_3625,c_3367]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_3764,plain,
% 3.52/1.01      ( k1_relat_1(sK2) != sK0
% 3.52/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 3.52/1.01      inference(equality_resolution_simp,[status(thm)],[c_3755]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_4542,plain,
% 3.52/1.01      ( sK1 = k1_xboole_0
% 3.52/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 3.52/1.01      inference(superposition,[status(thm)],[c_4483,c_3764]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_8721,plain,
% 3.52/1.01      ( sK1 = k1_xboole_0 ),
% 3.52/1.01      inference(global_propositional_subsumption,[status(thm)],[c_8519,c_4542]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_8766,plain,
% 3.52/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
% 3.52/1.01      inference(demodulation,[status(thm)],[c_8721,c_1677]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_8771,plain,
% 3.52/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.52/1.01      inference(demodulation,[status(thm)],[c_8766,c_5]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_23,plain,
% 3.52/1.01      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 3.52/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.52/1.01      | k1_xboole_0 = X1
% 3.52/1.01      | k1_xboole_0 = X0 ),
% 3.52/1.01      inference(cnf_transformation,[],[f101]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_516,plain,
% 3.52/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.52/1.01      | ~ v1_funct_1(X2)
% 3.52/1.01      | ~ v1_relat_1(X2)
% 3.52/1.01      | X2 != X0
% 3.52/1.01      | k1_relat_1(X2) != X1
% 3.52/1.01      | k2_relat_1(X2) != k1_xboole_0
% 3.52/1.01      | k1_xboole_0 = X0
% 3.52/1.01      | k1_xboole_0 = X1 ),
% 3.52/1.01      inference(resolution_lifted,[status(thm)],[c_23,c_30]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_517,plain,
% 3.52/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0)))
% 3.52/1.01      | ~ v1_funct_1(X0)
% 3.52/1.01      | ~ v1_relat_1(X0)
% 3.52/1.01      | k2_relat_1(X0) != k1_xboole_0
% 3.52/1.01      | k1_xboole_0 = X0
% 3.52/1.01      | k1_xboole_0 = k1_relat_1(X0) ),
% 3.52/1.01      inference(unflattening,[status(thm)],[c_516]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_533,plain,
% 3.52/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0)))
% 3.52/1.01      | ~ v1_funct_1(X0)
% 3.52/1.01      | k2_relat_1(X0) != k1_xboole_0
% 3.52/1.01      | k1_xboole_0 = X0
% 3.52/1.01      | k1_xboole_0 = k1_relat_1(X0) ),
% 3.52/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_517,c_19]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_1671,plain,
% 3.52/1.01      ( k2_relat_1(X0) != k1_xboole_0
% 3.52/1.01      | k1_xboole_0 = X0
% 3.52/1.01      | k1_xboole_0 = k1_relat_1(X0)
% 3.52/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0))) != iProver_top
% 3.52/1.01      | v1_funct_1(X0) != iProver_top ),
% 3.52/1.01      inference(predicate_to_equality,[status(thm)],[c_533]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_1867,plain,
% 3.52/1.01      ( k1_relat_1(X0) = k1_xboole_0
% 3.52/1.01      | k2_relat_1(X0) != k1_xboole_0
% 3.52/1.01      | k1_xboole_0 = X0
% 3.52/1.01      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.52/1.01      | v1_funct_1(X0) != iProver_top ),
% 3.52/1.01      inference(demodulation,[status(thm)],[c_1671,c_5]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_6806,plain,
% 3.52/1.01      ( k1_relat_1(sK2) = k1_xboole_0
% 3.52/1.01      | sK1 != k1_xboole_0
% 3.52/1.01      | sK2 = k1_xboole_0
% 3.52/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.52/1.01      | v1_funct_1(sK2) != iProver_top ),
% 3.52/1.01      inference(superposition,[status(thm)],[c_3625,c_1867]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_3,plain,
% 3.52/1.01      ( r1_tarski(k1_xboole_0,X0) ),
% 3.52/1.01      inference(cnf_transformation,[],[f54]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_2235,plain,
% 3.52/1.01      ( r1_tarski(k1_xboole_0,sK2) ),
% 3.52/1.01      inference(instantiation,[status(thm)],[c_3]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_2238,plain,
% 3.52/1.01      ( r1_tarski(k1_xboole_0,sK2) = iProver_top ),
% 3.52/1.01      inference(predicate_to_equality,[status(thm)],[c_2235]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_2374,plain,
% 3.52/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
% 3.52/1.01      | r1_tarski(sK2,k1_xboole_0) ),
% 3.52/1.01      inference(instantiation,[status(thm)],[c_10]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_2375,plain,
% 3.52/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.52/1.01      | r1_tarski(sK2,k1_xboole_0) = iProver_top ),
% 3.52/1.01      inference(predicate_to_equality,[status(thm)],[c_2374]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_0,plain,
% 3.52/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.52/1.01      inference(cnf_transformation,[],[f53]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_2502,plain,
% 3.52/1.01      ( ~ r1_tarski(X0,sK2) | ~ r1_tarski(sK2,X0) | sK2 = X0 ),
% 3.52/1.01      inference(instantiation,[status(thm)],[c_0]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_2503,plain,
% 3.52/1.01      ( sK2 = X0
% 3.52/1.01      | r1_tarski(X0,sK2) != iProver_top
% 3.52/1.01      | r1_tarski(sK2,X0) != iProver_top ),
% 3.52/1.01      inference(predicate_to_equality,[status(thm)],[c_2502]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_2505,plain,
% 3.52/1.01      ( sK2 = k1_xboole_0
% 3.52/1.01      | r1_tarski(sK2,k1_xboole_0) != iProver_top
% 3.52/1.01      | r1_tarski(k1_xboole_0,sK2) != iProver_top ),
% 3.52/1.01      inference(instantiation,[status(thm)],[c_2503]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_7085,plain,
% 3.52/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.52/1.01      | sK2 = k1_xboole_0 ),
% 3.52/1.01      inference(global_propositional_subsumption,
% 3.52/1.01                [status(thm)],
% 3.52/1.01                [c_6806,c_2238,c_2375,c_2505]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_7086,plain,
% 3.52/1.01      ( sK2 = k1_xboole_0
% 3.52/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.52/1.01      inference(renaming,[status(thm)],[c_7085]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_9266,plain,
% 3.52/1.01      ( sK2 = k1_xboole_0 ),
% 3.52/1.01      inference(superposition,[status(thm)],[c_8771,c_7086]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_10490,plain,
% 3.52/1.01      ( r1_tarski(k1_xboole_0,sK0) != iProver_top ),
% 3.52/1.01      inference(light_normalisation,[status(thm)],[c_5639,c_2865,c_9266]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_1691,plain,
% 3.52/1.01      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.52/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.52/1.01  
% 3.52/1.01  cnf(c_10492,plain,
% 3.52/1.01      ( $false ),
% 3.52/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_10490,c_1691]) ).
% 3.52/1.01  
% 3.52/1.01  
% 3.52/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.52/1.01  
% 3.52/1.01  ------                               Statistics
% 3.52/1.01  
% 3.52/1.01  ------ General
% 3.52/1.01  
% 3.52/1.01  abstr_ref_over_cycles:                  0
% 3.52/1.01  abstr_ref_under_cycles:                 0
% 3.52/1.01  gc_basic_clause_elim:                   0
% 3.52/1.01  forced_gc_time:                         0
% 3.52/1.01  parsing_time:                           0.012
% 3.52/1.01  unif_index_cands_time:                  0.
% 3.52/1.01  unif_index_add_time:                    0.
% 3.52/1.01  orderings_time:                         0.
% 3.52/1.01  out_proof_time:                         0.012
% 3.52/1.01  total_time:                             0.338
% 3.52/1.01  num_of_symbols:                         49
% 3.52/1.01  num_of_terms:                           7102
% 3.52/1.01  
% 3.52/1.01  ------ Preprocessing
% 3.52/1.01  
% 3.52/1.01  num_of_splits:                          0
% 3.52/1.01  num_of_split_atoms:                     0
% 3.52/1.01  num_of_reused_defs:                     0
% 3.52/1.01  num_eq_ax_congr_red:                    4
% 3.52/1.01  num_of_sem_filtered_clauses:            1
% 3.52/1.01  num_of_subtypes:                        0
% 3.52/1.01  monotx_restored_types:                  0
% 3.52/1.01  sat_num_of_epr_types:                   0
% 3.52/1.01  sat_num_of_non_cyclic_types:            0
% 3.52/1.01  sat_guarded_non_collapsed_types:        0
% 3.52/1.01  num_pure_diseq_elim:                    0
% 3.52/1.01  simp_replaced_by:                       0
% 3.52/1.01  res_preprocessed:                       149
% 3.52/1.01  prep_upred:                             0
% 3.52/1.01  prep_unflattend:                        53
% 3.52/1.01  smt_new_axioms:                         0
% 3.52/1.01  pred_elim_cands:                        6
% 3.52/1.01  pred_elim:                              2
% 3.52/1.01  pred_elim_cl:                           -4
% 3.52/1.01  pred_elim_cycles:                       3
% 3.52/1.01  merged_defs:                            6
% 3.52/1.01  merged_defs_ncl:                        0
% 3.52/1.01  bin_hyper_res:                          7
% 3.52/1.01  prep_cycles:                            3
% 3.52/1.01  pred_elim_time:                         0.013
% 3.52/1.01  splitting_time:                         0.
% 3.52/1.01  sem_filter_time:                        0.
% 3.52/1.01  monotx_time:                            0.
% 3.52/1.01  subtype_inf_time:                       0.
% 3.52/1.01  
% 3.52/1.01  ------ Problem properties
% 3.52/1.01  
% 3.52/1.01  clauses:                                42
% 3.52/1.01  conjectures:                            3
% 3.52/1.01  epr:                                    6
% 3.52/1.01  horn:                                   35
% 3.52/1.01  ground:                                 14
% 3.52/1.01  unary:                                  12
% 3.52/1.01  binary:                                 9
% 3.52/1.01  lits:                                   114
% 3.52/1.01  lits_eq:                                46
% 3.52/1.01  fd_pure:                                0
% 3.52/1.01  fd_pseudo:                              0
% 3.52/1.01  fd_cond:                                5
% 3.52/1.01  fd_pseudo_cond:                         1
% 3.52/1.01  ac_symbols:                             0
% 3.52/1.01  
% 3.52/1.01  ------ Propositional Solver
% 3.52/1.01  
% 3.52/1.01  prop_solver_calls:                      25
% 3.52/1.01  prop_fast_solver_calls:                 1320
% 3.52/1.01  smt_solver_calls:                       0
% 3.52/1.01  smt_fast_solver_calls:                  0
% 3.52/1.01  prop_num_of_clauses:                    3851
% 3.52/1.01  prop_preprocess_simplified:             8533
% 3.52/1.01  prop_fo_subsumed:                       56
% 3.52/1.01  prop_solver_time:                       0.
% 3.52/1.01  smt_solver_time:                        0.
% 3.52/1.01  smt_fast_solver_time:                   0.
% 3.52/1.01  prop_fast_solver_time:                  0.
% 3.52/1.01  prop_unsat_core_time:                   0.
% 3.52/1.01  
% 3.52/1.01  ------ QBF
% 3.52/1.01  
% 3.52/1.01  qbf_q_res:                              0
% 3.52/1.01  qbf_num_tautologies:                    0
% 3.52/1.01  qbf_prep_cycles:                        0
% 3.52/1.01  
% 3.52/1.01  ------ BMC1
% 3.52/1.01  
% 3.52/1.01  bmc1_current_bound:                     -1
% 3.52/1.01  bmc1_last_solved_bound:                 -1
% 3.52/1.01  bmc1_unsat_core_size:                   -1
% 3.52/1.01  bmc1_unsat_core_parents_size:           -1
% 3.52/1.01  bmc1_merge_next_fun:                    0
% 3.52/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.52/1.01  
% 3.52/1.01  ------ Instantiation
% 3.52/1.01  
% 3.52/1.01  inst_num_of_clauses:                    1270
% 3.52/1.01  inst_num_in_passive:                    343
% 3.52/1.01  inst_num_in_active:                     579
% 3.52/1.01  inst_num_in_unprocessed:                348
% 3.52/1.01  inst_num_of_loops:                      700
% 3.52/1.01  inst_num_of_learning_restarts:          0
% 3.52/1.01  inst_num_moves_active_passive:          117
% 3.52/1.01  inst_lit_activity:                      0
% 3.52/1.01  inst_lit_activity_moves:                0
% 3.52/1.01  inst_num_tautologies:                   0
% 3.52/1.01  inst_num_prop_implied:                  0
% 3.52/1.01  inst_num_existing_simplified:           0
% 3.52/1.01  inst_num_eq_res_simplified:             0
% 3.52/1.01  inst_num_child_elim:                    0
% 3.52/1.01  inst_num_of_dismatching_blockings:      409
% 3.52/1.01  inst_num_of_non_proper_insts:           1405
% 3.52/1.01  inst_num_of_duplicates:                 0
% 3.52/1.01  inst_inst_num_from_inst_to_res:         0
% 3.52/1.01  inst_dismatching_checking_time:         0.
% 3.52/1.01  
% 3.52/1.01  ------ Resolution
% 3.52/1.01  
% 3.52/1.01  res_num_of_clauses:                     0
% 3.52/1.01  res_num_in_passive:                     0
% 3.52/1.01  res_num_in_active:                      0
% 3.52/1.01  res_num_of_loops:                       152
% 3.52/1.01  res_forward_subset_subsumed:            80
% 3.52/1.01  res_backward_subset_subsumed:           0
% 3.52/1.01  res_forward_subsumed:                   0
% 3.52/1.01  res_backward_subsumed:                  0
% 3.52/1.01  res_forward_subsumption_resolution:     7
% 3.52/1.01  res_backward_subsumption_resolution:    0
% 3.52/1.01  res_clause_to_clause_subsumption:       741
% 3.52/1.01  res_orphan_elimination:                 0
% 3.52/1.01  res_tautology_del:                      76
% 3.52/1.01  res_num_eq_res_simplified:              0
% 3.52/1.01  res_num_sel_changes:                    0
% 3.52/1.01  res_moves_from_active_to_pass:          0
% 3.52/1.01  
% 3.52/1.01  ------ Superposition
% 3.52/1.01  
% 3.52/1.01  sup_time_total:                         0.
% 3.52/1.01  sup_time_generating:                    0.
% 3.52/1.01  sup_time_sim_full:                      0.
% 3.52/1.01  sup_time_sim_immed:                     0.
% 3.52/1.01  
% 3.52/1.01  sup_num_of_clauses:                     135
% 3.52/1.01  sup_num_in_active:                      62
% 3.52/1.01  sup_num_in_passive:                     73
% 3.52/1.01  sup_num_of_loops:                       139
% 3.52/1.01  sup_fw_superposition:                   131
% 3.52/1.01  sup_bw_superposition:                   114
% 3.52/1.01  sup_immediate_simplified:               164
% 3.52/1.01  sup_given_eliminated:                   1
% 3.52/1.01  comparisons_done:                       0
% 3.52/1.01  comparisons_avoided:                    30
% 3.52/1.01  
% 3.52/1.01  ------ Simplifications
% 3.52/1.01  
% 3.52/1.01  
% 3.52/1.01  sim_fw_subset_subsumed:                 45
% 3.52/1.01  sim_bw_subset_subsumed:                 29
% 3.52/1.01  sim_fw_subsumed:                        16
% 3.52/1.01  sim_bw_subsumed:                        3
% 3.52/1.01  sim_fw_subsumption_res:                 2
% 3.52/1.01  sim_bw_subsumption_res:                 4
% 3.52/1.01  sim_tautology_del:                      4
% 3.52/1.01  sim_eq_tautology_del:                   12
% 3.52/1.01  sim_eq_res_simp:                        4
% 3.52/1.01  sim_fw_demodulated:                     35
% 3.52/1.01  sim_bw_demodulated:                     78
% 3.52/1.01  sim_light_normalised:                   82
% 3.52/1.01  sim_joinable_taut:                      0
% 3.52/1.01  sim_joinable_simp:                      0
% 3.52/1.01  sim_ac_normalised:                      0
% 3.52/1.01  sim_smt_subsumption:                    0
% 3.52/1.01  
%------------------------------------------------------------------------------
