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
% DateTime   : Thu Dec  3 12:03:59 EST 2020

% Result     : Theorem 19.42s
% Output     : CNFRefutation 19.42s
% Verified   : 
% Statistics : Number of formulae       :  288 (12360 expanded)
%              Number of clauses        :  201 (4657 expanded)
%              Number of leaves         :   22 (2257 expanded)
%              Depth                    :   34
%              Number of atoms          :  862 (63358 expanded)
%              Number of equality atoms :  513 (22042 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    inference(ennf_transformation,[],[f16])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f52,plain,(
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
    inference(nnf_transformation,[],[f42])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f19,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

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
    inference(ennf_transformation,[],[f20])).

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
    inference(flattening,[],[f47])).

fof(f53,plain,
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

fof(f54,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f48,f53])).

fof(f85,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f86,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f54])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( r1_tarski(X0,X3)
       => m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(flattening,[],[f39])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f37])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f49])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f91,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f58])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f90,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f59])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f94,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f79])).

fof(f88,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f54])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f2,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f56,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(X2,X1)
        & v1_relat_1(X2) )
     => ( v4_relat_1(k7_relat_1(X2,X0),X1)
        & v4_relat_1(k7_relat_1(X2,X0),X0)
        & v1_relat_1(k7_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(k7_relat_1(X2,X0),X1)
        & v4_relat_1(k7_relat_1(X2,X0),X0)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(k7_relat_1(X2,X0),X1)
        & v4_relat_1(k7_relat_1(X2,X0),X0)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(k7_relat_1(X2,X0),X0)
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f87,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f45])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f84,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f43])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f92,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f80])).

fof(f93,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f92])).

fof(f89,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f54])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f95,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f78])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_33,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_448,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X0
    | sK1 != X2
    | sK0 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_33])).

cnf(c_449,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_448])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_451,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_449,c_32])).

cnf(c_1218,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1225,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2561,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1218,c_1225])).

cnf(c_2579,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_451,c_2561])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X3,X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1223,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(X3,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3294,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1218,c_1223])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X3) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1224,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) = iProver_top
    | r1_tarski(k1_relat_1(X0),X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4417,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3294,c_1224])).

cnf(c_6050,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X2,sK3) != iProver_top
    | r1_tarski(k1_relat_1(X2),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4417,c_1223])).

cnf(c_22024,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(sK3,sK3) != iProver_top
    | r1_tarski(sK0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2579,c_6050])).

cnf(c_7,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_97,plain,
    ( v4_relat_1(X0,X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1237,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3857,plain,
    ( r1_tarski(X0,sK3) != iProver_top
    | v1_relat_1(X0) = iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3294,c_1237])).

cnf(c_12,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2125,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2126,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2125])).

cnf(c_4318,plain,
    ( v1_relat_1(X0) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3857,c_2126])).

cnf(c_4319,plain,
    ( r1_tarski(X0,sK3) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_4318])).

cnf(c_4416,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) = iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1218,c_1224])).

cnf(c_4742,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(k1_relat_1(sK3),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4416,c_1223])).

cnf(c_16,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1226,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_6572,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(k1_relat_1(sK3),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4742,c_1226])).

cnf(c_12001,plain,
    ( sK1 = k1_xboole_0
    | v4_relat_1(X0,X1) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(sK0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2579,c_6572])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_104,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_105,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1230,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1836,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_1230])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_380,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK3 != X0
    | sK1 != k1_xboole_0
    | sK0 != X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_33])).

cnf(c_381,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0 ),
    inference(unflattening,[status(thm)],[c_380])).

cnf(c_1215,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_381])).

cnf(c_1341,plain,
    ( sK3 = k1_xboole_0
    | sK1 != k1_xboole_0
    | sK0 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1215,c_2])).

cnf(c_30,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_707,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1552,plain,
    ( sK0 != X0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_707])).

cnf(c_1815,plain,
    ( sK0 != sK0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1552])).

cnf(c_706,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1816,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_706])).

cnf(c_1894,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_707])).

cnf(c_1895,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1894])).

cnf(c_2059,plain,
    ( sK0 = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1341,c_30,c_104,c_105,c_1815,c_1816,c_1895])).

cnf(c_2060,plain,
    ( sK1 != k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_2059])).

cnf(c_2300,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_1226])).

cnf(c_14,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1228,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1238,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2211,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1228,c_1238])).

cnf(c_2399,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2211,c_1836])).

cnf(c_2403,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2399,c_1228])).

cnf(c_708,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_4922,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK0,k1_xboole_0)
    | sK0 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_708])).

cnf(c_4923,plain,
    ( sK0 != X0
    | k1_xboole_0 != X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(sK0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4922])).

cnf(c_4925,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4923])).

cnf(c_4739,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_4416])).

cnf(c_4945,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2579,c_4739])).

cnf(c_37,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_1525,plain,
    ( v4_relat_1(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1526,plain,
    ( v4_relat_1(sK3,sK0) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1525])).

cnf(c_1486,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1769,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1486])).

cnf(c_1770,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1769])).

cnf(c_3080,plain,
    ( ~ v4_relat_1(sK3,sK0)
    | r1_tarski(k1_relat_1(sK3),sK0)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_3081,plain,
    ( v4_relat_1(sK3,sK0) != iProver_top
    | r1_tarski(k1_relat_1(sK3),sK0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3080])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2318,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(k1_relat_1(X2),X0)
    | r1_tarski(k1_relat_1(X2),X1) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_4103,plain,
    ( r1_tarski(k1_relat_1(sK3),X0)
    | ~ r1_tarski(k1_relat_1(sK3),sK0)
    | ~ r1_tarski(sK0,X0) ),
    inference(instantiation,[status(thm)],[c_2318])).

cnf(c_4104,plain,
    ( r1_tarski(k1_relat_1(sK3),X0) = iProver_top
    | r1_tarski(k1_relat_1(sK3),sK0) != iProver_top
    | r1_tarski(sK0,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4103])).

cnf(c_4106,plain,
    ( r1_tarski(k1_relat_1(sK3),sK0) != iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_xboole_0) = iProver_top
    | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4104])).

cnf(c_6894,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4945,c_37,c_1526,c_1770,c_2126,c_3081,c_4106,c_4739])).

cnf(c_3297,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_1223])).

cnf(c_3301,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3297,c_3])).

cnf(c_6901,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6894,c_3301])).

cnf(c_12040,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(sK0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12001,c_104,c_105,c_1836,c_2060,c_2300,c_2403,c_4925,c_6901])).

cnf(c_22174,plain,
    ( r1_tarski(X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
    | r1_tarski(sK0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_22024,c_97,c_4319,c_4417,c_12040])).

cnf(c_22175,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
    | r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(sK0,X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_22174])).

cnf(c_2299,plain,
    ( v4_relat_1(sK3,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1218,c_1226])).

cnf(c_10,plain,
    ( ~ v4_relat_1(X0,X1)
    | v4_relat_1(k7_relat_1(X0,X2),X2)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1232,plain,
    ( v4_relat_1(X0,X1) != iProver_top
    | v4_relat_1(k7_relat_1(X0,X2),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4466,plain,
    ( v4_relat_1(k7_relat_1(sK3,X0),X0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2299,c_1232])).

cnf(c_3719,plain,
    ( v4_relat_1(k7_relat_1(sK3,X0),X0)
    | ~ v4_relat_1(sK3,sK0)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_3720,plain,
    ( v4_relat_1(k7_relat_1(sK3,X0),X0) = iProver_top
    | v4_relat_1(sK3,sK0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3719])).

cnf(c_4855,plain,
    ( v4_relat_1(k7_relat_1(sK3,X0),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4466,c_37,c_1526,c_1770,c_2126,c_3720])).

cnf(c_31,negated_conjecture,
    ( r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1219,plain,
    ( r1_tarski(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_15,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1227,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3633,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2579,c_1227])).

cnf(c_7464,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | sK1 = k1_xboole_0
    | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3633,c_37,c_1770,c_2126])).

cnf(c_7465,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
    | sK1 = k1_xboole_0
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_7464])).

cnf(c_7475,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1219,c_7465])).

cnf(c_1235,plain,
    ( v4_relat_1(X0,X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_7532,plain,
    ( sK1 = k1_xboole_0
    | v4_relat_1(k7_relat_1(sK3,sK2),X0) != iProver_top
    | r1_tarski(sK2,X0) = iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7475,c_1235])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1220,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_1629,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1218,c_1220])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_35,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_1840,plain,
    ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1629,c_35])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1222,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2622,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1840,c_1222])).

cnf(c_3004,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2622,c_35,c_37])).

cnf(c_3012,plain,
    ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3004,c_1237])).

cnf(c_3281,plain,
    ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3012,c_2126])).

cnf(c_8282,plain,
    ( sK1 = k1_xboole_0
    | v4_relat_1(k7_relat_1(sK3,sK2),X0) != iProver_top
    | r1_tarski(sK2,X0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7532,c_3281])).

cnf(c_8288,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(sK2,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4855,c_8282])).

cnf(c_38,plain,
    ( r1_tarski(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_1553,plain,
    ( sK2 != X0
    | sK2 = sK0
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_707])).

cnf(c_1554,plain,
    ( sK2 = sK0
    | sK2 != k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1553])).

cnf(c_1684,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_706])).

cnf(c_20,plain,
    ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_29,negated_conjecture,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_354,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK2 != X0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_29])).

cnf(c_355,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_354])).

cnf(c_1216,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK2
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_355])).

cnf(c_1396,plain,
    ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1216,c_2])).

cnf(c_1678,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1568,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(sK2,sK0)
    | X0 != sK2
    | X1 != sK0 ),
    inference(instantiation,[status(thm)],[c_708])).

cnf(c_1683,plain,
    ( r1_tarski(sK2,X0)
    | ~ r1_tarski(sK2,sK0)
    | X0 != sK0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1568])).

cnf(c_1686,plain,
    ( ~ r1_tarski(sK2,sK0)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != sK2
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1683])).

cnf(c_1551,plain,
    ( sK2 != X0
    | sK2 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_707])).

cnf(c_1814,plain,
    ( sK2 != sK2
    | sK2 = k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_1551])).

cnf(c_1970,plain,
    ( sK1 != k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1396,c_31,c_30,c_104,c_105,c_1678,c_1686,c_1684,c_1814,c_1895])).

cnf(c_1971,plain,
    ( sK2 = k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_1970])).

cnf(c_4313,plain,
    ( r1_tarski(sK2,sK2)
    | ~ r1_tarski(sK2,sK0)
    | sK2 != sK2
    | sK2 != sK0 ),
    inference(instantiation,[status(thm)],[c_1683])).

cnf(c_4314,plain,
    ( sK2 != sK2
    | sK2 != sK0
    | r1_tarski(sK2,sK2) = iProver_top
    | r1_tarski(sK2,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4313])).

cnf(c_79273,plain,
    ( r1_tarski(sK2,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8288,c_38,c_1554,c_1684,c_1971,c_2060,c_4314])).

cnf(c_4418,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3004,c_1224])).

cnf(c_11842,plain,
    ( k1_relset_1(X0,sK1,k7_relat_1(sK3,X1)) = k1_relat_1(k7_relat_1(sK3,X1))
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,X1)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4418,c_1225])).

cnf(c_24422,plain,
    ( k1_relset_1(X0,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
    | sK1 = k1_xboole_0
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7475,c_11842])).

cnf(c_79299,plain,
    ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_79273,c_24422])).

cnf(c_23,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_432,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_relset_1(X1,X2,X0) != X1
    | sK2 != X1
    | sK1 != X2
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_29])).

cnf(c_433,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_432])).

cnf(c_1212,plain,
    ( k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
    | k1_xboole_0 = sK1
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_433])).

cnf(c_1845,plain,
    ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) != sK2
    | sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1840,c_1212])).

cnf(c_88118,plain,
    ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
    | sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_79299,c_1845])).

cnf(c_89307,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_88118,c_7475])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1221,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2098,plain,
    ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1218,c_1221])).

cnf(c_2115,plain,
    ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2098,c_1840])).

cnf(c_2391,plain,
    ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2115,c_35])).

cnf(c_89314,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_89307,c_2391])).

cnf(c_89324,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top
    | r1_tarski(sK0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_22175,c_89314])).

cnf(c_4513,plain,
    ( ~ v4_relat_1(k7_relat_1(sK3,X0),X0)
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X0)
    | ~ v1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_10467,plain,
    ( ~ v4_relat_1(k7_relat_1(sK3,sK2),sK2)
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)
    | ~ v1_relat_1(k7_relat_1(sK3,sK2)) ),
    inference(instantiation,[status(thm)],[c_4513])).

cnf(c_10473,plain,
    ( v4_relat_1(k7_relat_1(sK3,sK2),sK2) != iProver_top
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) = iProver_top
    | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10467])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_15511,plain,
    ( v1_relat_1(k7_relat_1(sK3,sK2))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_15512,plain,
    ( v1_relat_1(k7_relat_1(sK3,sK2)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15511])).

cnf(c_17065,plain,
    ( v4_relat_1(k7_relat_1(sK3,sK2),sK2)
    | ~ v4_relat_1(sK3,sK0)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_3719])).

cnf(c_17066,plain,
    ( v4_relat_1(k7_relat_1(sK3,sK2),sK2) = iProver_top
    | v4_relat_1(sK3,sK0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17065])).

cnf(c_89328,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4418,c_89314])).

cnf(c_89465,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_89324,c_37,c_1526,c_1770,c_2126,c_10473,c_15512,c_17066,c_89328])).

cnf(c_3015,plain,
    ( k1_relset_1(sK0,sK1,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(superposition,[status(thm)],[c_3004,c_1225])).

cnf(c_89764,plain,
    ( k1_relset_1(sK0,k1_xboole_0,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(demodulation,[status(thm)],[c_89465,c_3015])).

cnf(c_89776,plain,
    ( sK0 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_89465,c_30])).

cnf(c_89777,plain,
    ( sK0 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_89776])).

cnf(c_89842,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
    inference(light_normalisation,[status(thm)],[c_89764,c_89777])).

cnf(c_89765,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_89465,c_3004])).

cnf(c_89828,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_89765,c_89777])).

cnf(c_89830,plain,
    ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_89828,c_3])).

cnf(c_22,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_400,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k2_partfun1(sK0,sK1,sK3,sK2) != X0
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | sK2 != k1_xboole_0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_29])).

cnf(c_401,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_400])).

cnf(c_1214,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_401])).

cnf(c_1409,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1214,c_3])).

cnf(c_1975,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k7_relat_1(sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1409,c_1840])).

cnf(c_89768,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,sK2)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_89465,c_1975])).

cnf(c_89769,plain,
    ( sK2 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_89465,c_1971])).

cnf(c_89803,plain,
    ( sK2 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_89769])).

cnf(c_89814,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_89768,c_89803])).

cnf(c_89815,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_89814])).

cnf(c_89820,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0
    | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_89815,c_3])).

cnf(c_89833,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0
    | v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
    inference(backward_subsumption_resolution,[status(thm)],[c_89830,c_89820])).

cnf(c_89844,plain,
    ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0
    | v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_89842,c_89833])).

cnf(c_3480,plain,
    ( k1_relat_1(X0) = k1_xboole_0
    | v4_relat_1(X0,k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1235,c_1238])).

cnf(c_8137,plain,
    ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4855,c_3480])).

cnf(c_3034,plain,
    ( v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3012])).

cnf(c_8662,plain,
    ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8137,c_2126,c_3034])).

cnf(c_89848,plain,
    ( k1_xboole_0 != k1_xboole_0
    | v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_89844,c_8662])).

cnf(c_89849,plain,
    ( v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_89848])).

cnf(c_2123,plain,
    ( v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2115])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_89849,c_2123,c_35])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:32:32 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 19.42/3.05  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.42/3.05  
% 19.42/3.05  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.42/3.05  
% 19.42/3.05  ------  iProver source info
% 19.42/3.05  
% 19.42/3.05  git: date: 2020-06-30 10:37:57 +0100
% 19.42/3.05  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.42/3.05  git: non_committed_changes: false
% 19.42/3.05  git: last_make_outside_of_git: false
% 19.42/3.05  
% 19.42/3.05  ------ 
% 19.42/3.05  
% 19.42/3.05  ------ Input Options
% 19.42/3.05  
% 19.42/3.05  --out_options                           all
% 19.42/3.05  --tptp_safe_out                         true
% 19.42/3.05  --problem_path                          ""
% 19.42/3.05  --include_path                          ""
% 19.42/3.05  --clausifier                            res/vclausify_rel
% 19.42/3.05  --clausifier_options                    --mode clausify
% 19.42/3.05  --stdin                                 false
% 19.42/3.05  --stats_out                             all
% 19.42/3.05  
% 19.42/3.05  ------ General Options
% 19.42/3.05  
% 19.42/3.05  --fof                                   false
% 19.42/3.05  --time_out_real                         305.
% 19.42/3.05  --time_out_virtual                      -1.
% 19.42/3.05  --symbol_type_check                     false
% 19.42/3.05  --clausify_out                          false
% 19.42/3.05  --sig_cnt_out                           false
% 19.42/3.05  --trig_cnt_out                          false
% 19.42/3.05  --trig_cnt_out_tolerance                1.
% 19.42/3.05  --trig_cnt_out_sk_spl                   false
% 19.42/3.05  --abstr_cl_out                          false
% 19.42/3.05  
% 19.42/3.05  ------ Global Options
% 19.42/3.05  
% 19.42/3.05  --schedule                              default
% 19.42/3.05  --add_important_lit                     false
% 19.42/3.05  --prop_solver_per_cl                    1000
% 19.42/3.05  --min_unsat_core                        false
% 19.42/3.05  --soft_assumptions                      false
% 19.42/3.05  --soft_lemma_size                       3
% 19.42/3.05  --prop_impl_unit_size                   0
% 19.42/3.05  --prop_impl_unit                        []
% 19.42/3.05  --share_sel_clauses                     true
% 19.42/3.05  --reset_solvers                         false
% 19.42/3.05  --bc_imp_inh                            [conj_cone]
% 19.42/3.05  --conj_cone_tolerance                   3.
% 19.42/3.05  --extra_neg_conj                        none
% 19.42/3.05  --large_theory_mode                     true
% 19.42/3.05  --prolific_symb_bound                   200
% 19.42/3.05  --lt_threshold                          2000
% 19.42/3.05  --clause_weak_htbl                      true
% 19.42/3.05  --gc_record_bc_elim                     false
% 19.42/3.05  
% 19.42/3.05  ------ Preprocessing Options
% 19.42/3.05  
% 19.42/3.05  --preprocessing_flag                    true
% 19.42/3.05  --time_out_prep_mult                    0.1
% 19.42/3.05  --splitting_mode                        input
% 19.42/3.05  --splitting_grd                         true
% 19.42/3.05  --splitting_cvd                         false
% 19.42/3.05  --splitting_cvd_svl                     false
% 19.42/3.05  --splitting_nvd                         32
% 19.42/3.05  --sub_typing                            true
% 19.42/3.05  --prep_gs_sim                           true
% 19.42/3.05  --prep_unflatten                        true
% 19.42/3.05  --prep_res_sim                          true
% 19.42/3.05  --prep_upred                            true
% 19.42/3.05  --prep_sem_filter                       exhaustive
% 19.42/3.05  --prep_sem_filter_out                   false
% 19.42/3.05  --pred_elim                             true
% 19.42/3.05  --res_sim_input                         true
% 19.42/3.05  --eq_ax_congr_red                       true
% 19.42/3.05  --pure_diseq_elim                       true
% 19.42/3.05  --brand_transform                       false
% 19.42/3.05  --non_eq_to_eq                          false
% 19.42/3.05  --prep_def_merge                        true
% 19.42/3.05  --prep_def_merge_prop_impl              false
% 19.42/3.05  --prep_def_merge_mbd                    true
% 19.42/3.05  --prep_def_merge_tr_red                 false
% 19.42/3.05  --prep_def_merge_tr_cl                  false
% 19.42/3.05  --smt_preprocessing                     true
% 19.42/3.05  --smt_ac_axioms                         fast
% 19.42/3.05  --preprocessed_out                      false
% 19.42/3.05  --preprocessed_stats                    false
% 19.42/3.05  
% 19.42/3.05  ------ Abstraction refinement Options
% 19.42/3.05  
% 19.42/3.05  --abstr_ref                             []
% 19.42/3.05  --abstr_ref_prep                        false
% 19.42/3.05  --abstr_ref_until_sat                   false
% 19.42/3.05  --abstr_ref_sig_restrict                funpre
% 19.42/3.05  --abstr_ref_af_restrict_to_split_sk     false
% 19.42/3.05  --abstr_ref_under                       []
% 19.42/3.05  
% 19.42/3.05  ------ SAT Options
% 19.42/3.05  
% 19.42/3.05  --sat_mode                              false
% 19.42/3.05  --sat_fm_restart_options                ""
% 19.42/3.05  --sat_gr_def                            false
% 19.42/3.05  --sat_epr_types                         true
% 19.42/3.05  --sat_non_cyclic_types                  false
% 19.42/3.05  --sat_finite_models                     false
% 19.42/3.05  --sat_fm_lemmas                         false
% 19.42/3.05  --sat_fm_prep                           false
% 19.42/3.05  --sat_fm_uc_incr                        true
% 19.42/3.05  --sat_out_model                         small
% 19.42/3.05  --sat_out_clauses                       false
% 19.42/3.05  
% 19.42/3.05  ------ QBF Options
% 19.42/3.05  
% 19.42/3.05  --qbf_mode                              false
% 19.42/3.05  --qbf_elim_univ                         false
% 19.42/3.05  --qbf_dom_inst                          none
% 19.42/3.05  --qbf_dom_pre_inst                      false
% 19.42/3.05  --qbf_sk_in                             false
% 19.42/3.05  --qbf_pred_elim                         true
% 19.42/3.05  --qbf_split                             512
% 19.42/3.05  
% 19.42/3.05  ------ BMC1 Options
% 19.42/3.05  
% 19.42/3.05  --bmc1_incremental                      false
% 19.42/3.05  --bmc1_axioms                           reachable_all
% 19.42/3.05  --bmc1_min_bound                        0
% 19.42/3.05  --bmc1_max_bound                        -1
% 19.42/3.05  --bmc1_max_bound_default                -1
% 19.42/3.05  --bmc1_symbol_reachability              true
% 19.42/3.05  --bmc1_property_lemmas                  false
% 19.42/3.05  --bmc1_k_induction                      false
% 19.42/3.05  --bmc1_non_equiv_states                 false
% 19.42/3.05  --bmc1_deadlock                         false
% 19.42/3.05  --bmc1_ucm                              false
% 19.42/3.05  --bmc1_add_unsat_core                   none
% 19.42/3.05  --bmc1_unsat_core_children              false
% 19.42/3.05  --bmc1_unsat_core_extrapolate_axioms    false
% 19.42/3.05  --bmc1_out_stat                         full
% 19.42/3.05  --bmc1_ground_init                      false
% 19.42/3.05  --bmc1_pre_inst_next_state              false
% 19.42/3.05  --bmc1_pre_inst_state                   false
% 19.42/3.05  --bmc1_pre_inst_reach_state             false
% 19.42/3.05  --bmc1_out_unsat_core                   false
% 19.42/3.05  --bmc1_aig_witness_out                  false
% 19.42/3.05  --bmc1_verbose                          false
% 19.42/3.05  --bmc1_dump_clauses_tptp                false
% 19.42/3.05  --bmc1_dump_unsat_core_tptp             false
% 19.42/3.05  --bmc1_dump_file                        -
% 19.42/3.05  --bmc1_ucm_expand_uc_limit              128
% 19.42/3.05  --bmc1_ucm_n_expand_iterations          6
% 19.42/3.05  --bmc1_ucm_extend_mode                  1
% 19.42/3.05  --bmc1_ucm_init_mode                    2
% 19.42/3.05  --bmc1_ucm_cone_mode                    none
% 19.42/3.05  --bmc1_ucm_reduced_relation_type        0
% 19.42/3.05  --bmc1_ucm_relax_model                  4
% 19.42/3.05  --bmc1_ucm_full_tr_after_sat            true
% 19.42/3.05  --bmc1_ucm_expand_neg_assumptions       false
% 19.42/3.05  --bmc1_ucm_layered_model                none
% 19.42/3.06  --bmc1_ucm_max_lemma_size               10
% 19.42/3.06  
% 19.42/3.06  ------ AIG Options
% 19.42/3.06  
% 19.42/3.06  --aig_mode                              false
% 19.42/3.06  
% 19.42/3.06  ------ Instantiation Options
% 19.42/3.06  
% 19.42/3.06  --instantiation_flag                    true
% 19.42/3.06  --inst_sos_flag                         false
% 19.42/3.06  --inst_sos_phase                        true
% 19.42/3.06  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.42/3.06  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.42/3.06  --inst_lit_sel_side                     num_symb
% 19.42/3.06  --inst_solver_per_active                1400
% 19.42/3.06  --inst_solver_calls_frac                1.
% 19.42/3.06  --inst_passive_queue_type               priority_queues
% 19.42/3.06  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.42/3.06  --inst_passive_queues_freq              [25;2]
% 19.42/3.06  --inst_dismatching                      true
% 19.42/3.06  --inst_eager_unprocessed_to_passive     true
% 19.42/3.06  --inst_prop_sim_given                   true
% 19.42/3.06  --inst_prop_sim_new                     false
% 19.42/3.06  --inst_subs_new                         false
% 19.42/3.06  --inst_eq_res_simp                      false
% 19.42/3.06  --inst_subs_given                       false
% 19.42/3.06  --inst_orphan_elimination               true
% 19.42/3.06  --inst_learning_loop_flag               true
% 19.42/3.06  --inst_learning_start                   3000
% 19.42/3.06  --inst_learning_factor                  2
% 19.42/3.06  --inst_start_prop_sim_after_learn       3
% 19.42/3.06  --inst_sel_renew                        solver
% 19.42/3.06  --inst_lit_activity_flag                true
% 19.42/3.06  --inst_restr_to_given                   false
% 19.42/3.06  --inst_activity_threshold               500
% 19.42/3.06  --inst_out_proof                        true
% 19.42/3.06  
% 19.42/3.06  ------ Resolution Options
% 19.42/3.06  
% 19.42/3.06  --resolution_flag                       true
% 19.42/3.06  --res_lit_sel                           adaptive
% 19.42/3.06  --res_lit_sel_side                      none
% 19.42/3.06  --res_ordering                          kbo
% 19.42/3.06  --res_to_prop_solver                    active
% 19.42/3.06  --res_prop_simpl_new                    false
% 19.42/3.06  --res_prop_simpl_given                  true
% 19.42/3.06  --res_passive_queue_type                priority_queues
% 19.42/3.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.42/3.06  --res_passive_queues_freq               [15;5]
% 19.42/3.06  --res_forward_subs                      full
% 19.42/3.06  --res_backward_subs                     full
% 19.42/3.06  --res_forward_subs_resolution           true
% 19.42/3.06  --res_backward_subs_resolution          true
% 19.42/3.06  --res_orphan_elimination                true
% 19.42/3.06  --res_time_limit                        2.
% 19.42/3.06  --res_out_proof                         true
% 19.42/3.06  
% 19.42/3.06  ------ Superposition Options
% 19.42/3.06  
% 19.42/3.06  --superposition_flag                    true
% 19.42/3.06  --sup_passive_queue_type                priority_queues
% 19.42/3.06  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.42/3.06  --sup_passive_queues_freq               [8;1;4]
% 19.42/3.06  --demod_completeness_check              fast
% 19.42/3.06  --demod_use_ground                      true
% 19.42/3.06  --sup_to_prop_solver                    passive
% 19.42/3.06  --sup_prop_simpl_new                    true
% 19.42/3.06  --sup_prop_simpl_given                  true
% 19.42/3.06  --sup_fun_splitting                     false
% 19.42/3.06  --sup_smt_interval                      50000
% 19.42/3.06  
% 19.42/3.06  ------ Superposition Simplification Setup
% 19.42/3.06  
% 19.42/3.06  --sup_indices_passive                   []
% 19.42/3.06  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.42/3.06  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.42/3.06  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.42/3.06  --sup_full_triv                         [TrivRules;PropSubs]
% 19.42/3.06  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.42/3.06  --sup_full_bw                           [BwDemod]
% 19.42/3.06  --sup_immed_triv                        [TrivRules]
% 19.42/3.06  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.42/3.06  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.42/3.06  --sup_immed_bw_main                     []
% 19.42/3.06  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.42/3.06  --sup_input_triv                        [Unflattening;TrivRules]
% 19.42/3.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.42/3.06  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.42/3.06  
% 19.42/3.06  ------ Combination Options
% 19.42/3.06  
% 19.42/3.06  --comb_res_mult                         3
% 19.42/3.06  --comb_sup_mult                         2
% 19.42/3.06  --comb_inst_mult                        10
% 19.42/3.06  
% 19.42/3.06  ------ Debug Options
% 19.42/3.06  
% 19.42/3.06  --dbg_backtrace                         false
% 19.42/3.06  --dbg_dump_prop_clauses                 false
% 19.42/3.06  --dbg_dump_prop_clauses_file            -
% 19.42/3.06  --dbg_out_stat                          false
% 19.42/3.06  ------ Parsing...
% 19.42/3.06  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.42/3.06  
% 19.42/3.06  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 19.42/3.06  
% 19.42/3.06  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.42/3.06  
% 19.42/3.06  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.42/3.06  ------ Proving...
% 19.42/3.06  ------ Problem Properties 
% 19.42/3.06  
% 19.42/3.06  
% 19.42/3.06  clauses                                 34
% 19.42/3.06  conjectures                             4
% 19.42/3.06  EPR                                     5
% 19.42/3.06  Horn                                    31
% 19.42/3.06  unary                                   6
% 19.42/3.06  binary                                  7
% 19.42/3.06  lits                                    91
% 19.42/3.06  lits eq                                 28
% 19.42/3.06  fd_pure                                 0
% 19.42/3.06  fd_pseudo                               0
% 19.42/3.06  fd_cond                                 2
% 19.42/3.06  fd_pseudo_cond                          0
% 19.42/3.06  AC symbols                              0
% 19.42/3.06  
% 19.42/3.06  ------ Schedule dynamic 5 is on 
% 19.42/3.06  
% 19.42/3.06  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 19.42/3.06  
% 19.42/3.06  
% 19.42/3.06  ------ 
% 19.42/3.06  Current options:
% 19.42/3.06  ------ 
% 19.42/3.06  
% 19.42/3.06  ------ Input Options
% 19.42/3.06  
% 19.42/3.06  --out_options                           all
% 19.42/3.06  --tptp_safe_out                         true
% 19.42/3.06  --problem_path                          ""
% 19.42/3.06  --include_path                          ""
% 19.42/3.06  --clausifier                            res/vclausify_rel
% 19.42/3.06  --clausifier_options                    --mode clausify
% 19.42/3.06  --stdin                                 false
% 19.42/3.06  --stats_out                             all
% 19.42/3.06  
% 19.42/3.06  ------ General Options
% 19.42/3.06  
% 19.42/3.06  --fof                                   false
% 19.42/3.06  --time_out_real                         305.
% 19.42/3.06  --time_out_virtual                      -1.
% 19.42/3.06  --symbol_type_check                     false
% 19.42/3.06  --clausify_out                          false
% 19.42/3.06  --sig_cnt_out                           false
% 19.42/3.06  --trig_cnt_out                          false
% 19.42/3.06  --trig_cnt_out_tolerance                1.
% 19.42/3.06  --trig_cnt_out_sk_spl                   false
% 19.42/3.06  --abstr_cl_out                          false
% 19.42/3.06  
% 19.42/3.06  ------ Global Options
% 19.42/3.06  
% 19.42/3.06  --schedule                              default
% 19.42/3.06  --add_important_lit                     false
% 19.42/3.06  --prop_solver_per_cl                    1000
% 19.42/3.06  --min_unsat_core                        false
% 19.42/3.06  --soft_assumptions                      false
% 19.42/3.06  --soft_lemma_size                       3
% 19.42/3.06  --prop_impl_unit_size                   0
% 19.42/3.06  --prop_impl_unit                        []
% 19.42/3.06  --share_sel_clauses                     true
% 19.42/3.06  --reset_solvers                         false
% 19.42/3.06  --bc_imp_inh                            [conj_cone]
% 19.42/3.06  --conj_cone_tolerance                   3.
% 19.42/3.06  --extra_neg_conj                        none
% 19.42/3.06  --large_theory_mode                     true
% 19.42/3.06  --prolific_symb_bound                   200
% 19.42/3.06  --lt_threshold                          2000
% 19.42/3.06  --clause_weak_htbl                      true
% 19.42/3.06  --gc_record_bc_elim                     false
% 19.42/3.06  
% 19.42/3.06  ------ Preprocessing Options
% 19.42/3.06  
% 19.42/3.06  --preprocessing_flag                    true
% 19.42/3.06  --time_out_prep_mult                    0.1
% 19.42/3.06  --splitting_mode                        input
% 19.42/3.06  --splitting_grd                         true
% 19.42/3.06  --splitting_cvd                         false
% 19.42/3.06  --splitting_cvd_svl                     false
% 19.42/3.06  --splitting_nvd                         32
% 19.42/3.06  --sub_typing                            true
% 19.42/3.06  --prep_gs_sim                           true
% 19.42/3.06  --prep_unflatten                        true
% 19.42/3.06  --prep_res_sim                          true
% 19.42/3.06  --prep_upred                            true
% 19.42/3.06  --prep_sem_filter                       exhaustive
% 19.42/3.06  --prep_sem_filter_out                   false
% 19.42/3.06  --pred_elim                             true
% 19.42/3.06  --res_sim_input                         true
% 19.42/3.06  --eq_ax_congr_red                       true
% 19.42/3.06  --pure_diseq_elim                       true
% 19.42/3.06  --brand_transform                       false
% 19.42/3.06  --non_eq_to_eq                          false
% 19.42/3.06  --prep_def_merge                        true
% 19.42/3.06  --prep_def_merge_prop_impl              false
% 19.42/3.06  --prep_def_merge_mbd                    true
% 19.42/3.06  --prep_def_merge_tr_red                 false
% 19.42/3.06  --prep_def_merge_tr_cl                  false
% 19.42/3.06  --smt_preprocessing                     true
% 19.42/3.06  --smt_ac_axioms                         fast
% 19.42/3.06  --preprocessed_out                      false
% 19.42/3.06  --preprocessed_stats                    false
% 19.42/3.06  
% 19.42/3.06  ------ Abstraction refinement Options
% 19.42/3.06  
% 19.42/3.06  --abstr_ref                             []
% 19.42/3.06  --abstr_ref_prep                        false
% 19.42/3.06  --abstr_ref_until_sat                   false
% 19.42/3.06  --abstr_ref_sig_restrict                funpre
% 19.42/3.06  --abstr_ref_af_restrict_to_split_sk     false
% 19.42/3.06  --abstr_ref_under                       []
% 19.42/3.06  
% 19.42/3.06  ------ SAT Options
% 19.42/3.06  
% 19.42/3.06  --sat_mode                              false
% 19.42/3.06  --sat_fm_restart_options                ""
% 19.42/3.06  --sat_gr_def                            false
% 19.42/3.06  --sat_epr_types                         true
% 19.42/3.06  --sat_non_cyclic_types                  false
% 19.42/3.06  --sat_finite_models                     false
% 19.42/3.06  --sat_fm_lemmas                         false
% 19.42/3.06  --sat_fm_prep                           false
% 19.42/3.06  --sat_fm_uc_incr                        true
% 19.42/3.06  --sat_out_model                         small
% 19.42/3.06  --sat_out_clauses                       false
% 19.42/3.06  
% 19.42/3.06  ------ QBF Options
% 19.42/3.06  
% 19.42/3.06  --qbf_mode                              false
% 19.42/3.06  --qbf_elim_univ                         false
% 19.42/3.06  --qbf_dom_inst                          none
% 19.42/3.06  --qbf_dom_pre_inst                      false
% 19.42/3.06  --qbf_sk_in                             false
% 19.42/3.06  --qbf_pred_elim                         true
% 19.42/3.06  --qbf_split                             512
% 19.42/3.06  
% 19.42/3.06  ------ BMC1 Options
% 19.42/3.06  
% 19.42/3.06  --bmc1_incremental                      false
% 19.42/3.06  --bmc1_axioms                           reachable_all
% 19.42/3.06  --bmc1_min_bound                        0
% 19.42/3.06  --bmc1_max_bound                        -1
% 19.42/3.06  --bmc1_max_bound_default                -1
% 19.42/3.06  --bmc1_symbol_reachability              true
% 19.42/3.06  --bmc1_property_lemmas                  false
% 19.42/3.06  --bmc1_k_induction                      false
% 19.42/3.06  --bmc1_non_equiv_states                 false
% 19.42/3.06  --bmc1_deadlock                         false
% 19.42/3.06  --bmc1_ucm                              false
% 19.42/3.06  --bmc1_add_unsat_core                   none
% 19.42/3.06  --bmc1_unsat_core_children              false
% 19.42/3.06  --bmc1_unsat_core_extrapolate_axioms    false
% 19.42/3.06  --bmc1_out_stat                         full
% 19.42/3.06  --bmc1_ground_init                      false
% 19.42/3.06  --bmc1_pre_inst_next_state              false
% 19.42/3.06  --bmc1_pre_inst_state                   false
% 19.42/3.06  --bmc1_pre_inst_reach_state             false
% 19.42/3.06  --bmc1_out_unsat_core                   false
% 19.42/3.06  --bmc1_aig_witness_out                  false
% 19.42/3.06  --bmc1_verbose                          false
% 19.42/3.06  --bmc1_dump_clauses_tptp                false
% 19.42/3.06  --bmc1_dump_unsat_core_tptp             false
% 19.42/3.06  --bmc1_dump_file                        -
% 19.42/3.06  --bmc1_ucm_expand_uc_limit              128
% 19.42/3.06  --bmc1_ucm_n_expand_iterations          6
% 19.42/3.06  --bmc1_ucm_extend_mode                  1
% 19.42/3.06  --bmc1_ucm_init_mode                    2
% 19.42/3.06  --bmc1_ucm_cone_mode                    none
% 19.42/3.06  --bmc1_ucm_reduced_relation_type        0
% 19.42/3.06  --bmc1_ucm_relax_model                  4
% 19.42/3.06  --bmc1_ucm_full_tr_after_sat            true
% 19.42/3.06  --bmc1_ucm_expand_neg_assumptions       false
% 19.42/3.06  --bmc1_ucm_layered_model                none
% 19.42/3.06  --bmc1_ucm_max_lemma_size               10
% 19.42/3.06  
% 19.42/3.06  ------ AIG Options
% 19.42/3.06  
% 19.42/3.06  --aig_mode                              false
% 19.42/3.06  
% 19.42/3.06  ------ Instantiation Options
% 19.42/3.06  
% 19.42/3.06  --instantiation_flag                    true
% 19.42/3.06  --inst_sos_flag                         false
% 19.42/3.06  --inst_sos_phase                        true
% 19.42/3.06  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.42/3.06  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.42/3.06  --inst_lit_sel_side                     none
% 19.42/3.06  --inst_solver_per_active                1400
% 19.42/3.06  --inst_solver_calls_frac                1.
% 19.42/3.06  --inst_passive_queue_type               priority_queues
% 19.42/3.06  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.42/3.06  --inst_passive_queues_freq              [25;2]
% 19.42/3.06  --inst_dismatching                      true
% 19.42/3.06  --inst_eager_unprocessed_to_passive     true
% 19.42/3.06  --inst_prop_sim_given                   true
% 19.42/3.06  --inst_prop_sim_new                     false
% 19.42/3.06  --inst_subs_new                         false
% 19.42/3.06  --inst_eq_res_simp                      false
% 19.42/3.06  --inst_subs_given                       false
% 19.42/3.06  --inst_orphan_elimination               true
% 19.42/3.06  --inst_learning_loop_flag               true
% 19.42/3.06  --inst_learning_start                   3000
% 19.42/3.06  --inst_learning_factor                  2
% 19.42/3.06  --inst_start_prop_sim_after_learn       3
% 19.42/3.06  --inst_sel_renew                        solver
% 19.42/3.06  --inst_lit_activity_flag                true
% 19.42/3.06  --inst_restr_to_given                   false
% 19.42/3.06  --inst_activity_threshold               500
% 19.42/3.06  --inst_out_proof                        true
% 19.42/3.06  
% 19.42/3.06  ------ Resolution Options
% 19.42/3.06  
% 19.42/3.06  --resolution_flag                       false
% 19.42/3.06  --res_lit_sel                           adaptive
% 19.42/3.06  --res_lit_sel_side                      none
% 19.42/3.06  --res_ordering                          kbo
% 19.42/3.06  --res_to_prop_solver                    active
% 19.42/3.06  --res_prop_simpl_new                    false
% 19.42/3.06  --res_prop_simpl_given                  true
% 19.42/3.06  --res_passive_queue_type                priority_queues
% 19.42/3.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.42/3.06  --res_passive_queues_freq               [15;5]
% 19.42/3.06  --res_forward_subs                      full
% 19.42/3.06  --res_backward_subs                     full
% 19.42/3.06  --res_forward_subs_resolution           true
% 19.42/3.06  --res_backward_subs_resolution          true
% 19.42/3.06  --res_orphan_elimination                true
% 19.42/3.06  --res_time_limit                        2.
% 19.42/3.06  --res_out_proof                         true
% 19.42/3.06  
% 19.42/3.06  ------ Superposition Options
% 19.42/3.06  
% 19.42/3.06  --superposition_flag                    true
% 19.42/3.06  --sup_passive_queue_type                priority_queues
% 19.42/3.06  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.42/3.06  --sup_passive_queues_freq               [8;1;4]
% 19.42/3.06  --demod_completeness_check              fast
% 19.42/3.06  --demod_use_ground                      true
% 19.42/3.06  --sup_to_prop_solver                    passive
% 19.42/3.06  --sup_prop_simpl_new                    true
% 19.42/3.06  --sup_prop_simpl_given                  true
% 19.42/3.06  --sup_fun_splitting                     false
% 19.42/3.06  --sup_smt_interval                      50000
% 19.42/3.06  
% 19.42/3.06  ------ Superposition Simplification Setup
% 19.42/3.06  
% 19.42/3.06  --sup_indices_passive                   []
% 19.42/3.06  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.42/3.06  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.42/3.06  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.42/3.06  --sup_full_triv                         [TrivRules;PropSubs]
% 19.42/3.06  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.42/3.06  --sup_full_bw                           [BwDemod]
% 19.42/3.06  --sup_immed_triv                        [TrivRules]
% 19.42/3.06  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.42/3.06  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.42/3.06  --sup_immed_bw_main                     []
% 19.42/3.06  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.42/3.06  --sup_input_triv                        [Unflattening;TrivRules]
% 19.42/3.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.42/3.06  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.42/3.06  
% 19.42/3.06  ------ Combination Options
% 19.42/3.06  
% 19.42/3.06  --comb_res_mult                         3
% 19.42/3.06  --comb_sup_mult                         2
% 19.42/3.06  --comb_inst_mult                        10
% 19.42/3.06  
% 19.42/3.06  ------ Debug Options
% 19.42/3.06  
% 19.42/3.06  --dbg_backtrace                         false
% 19.42/3.06  --dbg_dump_prop_clauses                 false
% 19.42/3.06  --dbg_dump_prop_clauses_file            -
% 19.42/3.06  --dbg_out_stat                          false
% 19.42/3.06  
% 19.42/3.06  
% 19.42/3.06  
% 19.42/3.06  
% 19.42/3.06  ------ Proving...
% 19.42/3.06  
% 19.42/3.06  
% 19.42/3.06  % SZS status Theorem for theBenchmark.p
% 19.42/3.06  
% 19.42/3.06  % SZS output start CNFRefutation for theBenchmark.p
% 19.42/3.06  
% 19.42/3.06  fof(f16,axiom,(
% 19.42/3.06    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 19.42/3.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.42/3.06  
% 19.42/3.06  fof(f41,plain,(
% 19.42/3.06    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 19.42/3.06    inference(ennf_transformation,[],[f16])).
% 19.42/3.06  
% 19.42/3.06  fof(f42,plain,(
% 19.42/3.06    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 19.42/3.06    inference(flattening,[],[f41])).
% 19.42/3.06  
% 19.42/3.06  fof(f52,plain,(
% 19.42/3.06    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 19.42/3.06    inference(nnf_transformation,[],[f42])).
% 19.42/3.06  
% 19.42/3.06  fof(f75,plain,(
% 19.42/3.06    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 19.42/3.06    inference(cnf_transformation,[],[f52])).
% 19.42/3.06  
% 19.42/3.06  fof(f19,conjecture,(
% 19.42/3.06    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 19.42/3.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.42/3.06  
% 19.42/3.06  fof(f20,negated_conjecture,(
% 19.42/3.06    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 19.42/3.06    inference(negated_conjecture,[],[f19])).
% 19.42/3.06  
% 19.42/3.06  fof(f47,plain,(
% 19.42/3.06    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 19.42/3.06    inference(ennf_transformation,[],[f20])).
% 19.42/3.06  
% 19.42/3.06  fof(f48,plain,(
% 19.42/3.06    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 19.42/3.06    inference(flattening,[],[f47])).
% 19.42/3.06  
% 19.42/3.06  fof(f53,plain,(
% 19.42/3.06    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 19.42/3.06    introduced(choice_axiom,[])).
% 19.42/3.06  
% 19.42/3.06  fof(f54,plain,(
% 19.42/3.06    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 19.42/3.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f48,f53])).
% 19.42/3.06  
% 19.42/3.06  fof(f85,plain,(
% 19.42/3.06    v1_funct_2(sK3,sK0,sK1)),
% 19.42/3.06    inference(cnf_transformation,[],[f54])).
% 19.42/3.06  
% 19.42/3.06  fof(f86,plain,(
% 19.42/3.06    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 19.42/3.06    inference(cnf_transformation,[],[f54])).
% 19.42/3.06  
% 19.42/3.06  fof(f13,axiom,(
% 19.42/3.06    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 19.42/3.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.42/3.06  
% 19.42/3.06  fof(f36,plain,(
% 19.42/3.06    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 19.42/3.06    inference(ennf_transformation,[],[f13])).
% 19.42/3.06  
% 19.42/3.06  fof(f72,plain,(
% 19.42/3.06    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 19.42/3.06    inference(cnf_transformation,[],[f36])).
% 19.42/3.06  
% 19.42/3.06  fof(f15,axiom,(
% 19.42/3.06    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => (r1_tarski(X0,X3) => m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 19.42/3.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.42/3.06  
% 19.42/3.06  fof(f39,plain,(
% 19.42/3.06    ! [X0,X1,X2,X3] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 19.42/3.06    inference(ennf_transformation,[],[f15])).
% 19.42/3.06  
% 19.42/3.06  fof(f40,plain,(
% 19.42/3.06    ! [X0,X1,X2,X3] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 19.42/3.06    inference(flattening,[],[f39])).
% 19.42/3.06  
% 19.42/3.06  fof(f74,plain,(
% 19.42/3.06    ( ! [X2,X0,X3,X1] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 19.42/3.06    inference(cnf_transformation,[],[f40])).
% 19.42/3.06  
% 19.42/3.06  fof(f14,axiom,(
% 19.42/3.06    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 19.42/3.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.42/3.06  
% 19.42/3.06  fof(f37,plain,(
% 19.42/3.06    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 19.42/3.06    inference(ennf_transformation,[],[f14])).
% 19.42/3.06  
% 19.42/3.06  fof(f38,plain,(
% 19.42/3.06    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 19.42/3.06    inference(flattening,[],[f37])).
% 19.42/3.06  
% 19.42/3.06  fof(f73,plain,(
% 19.42/3.06    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 19.42/3.06    inference(cnf_transformation,[],[f38])).
% 19.42/3.06  
% 19.42/3.06  fof(f5,axiom,(
% 19.42/3.06    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 19.42/3.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.42/3.06  
% 19.42/3.06  fof(f26,plain,(
% 19.42/3.06    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 19.42/3.06    inference(ennf_transformation,[],[f5])).
% 19.42/3.06  
% 19.42/3.06  fof(f51,plain,(
% 19.42/3.06    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 19.42/3.06    inference(nnf_transformation,[],[f26])).
% 19.42/3.06  
% 19.42/3.06  fof(f61,plain,(
% 19.42/3.06    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 19.42/3.06    inference(cnf_transformation,[],[f51])).
% 19.42/3.06  
% 19.42/3.06  fof(f4,axiom,(
% 19.42/3.06    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 19.42/3.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.42/3.06  
% 19.42/3.06  fof(f25,plain,(
% 19.42/3.06    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 19.42/3.06    inference(ennf_transformation,[],[f4])).
% 19.42/3.06  
% 19.42/3.06  fof(f60,plain,(
% 19.42/3.06    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 19.42/3.06    inference(cnf_transformation,[],[f25])).
% 19.42/3.06  
% 19.42/3.06  fof(f8,axiom,(
% 19.42/3.06    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 19.42/3.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.42/3.06  
% 19.42/3.06  fof(f67,plain,(
% 19.42/3.06    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 19.42/3.06    inference(cnf_transformation,[],[f8])).
% 19.42/3.06  
% 19.42/3.06  fof(f12,axiom,(
% 19.42/3.06    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 19.42/3.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.42/3.06  
% 19.42/3.06  fof(f21,plain,(
% 19.42/3.06    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 19.42/3.06    inference(pure_predicate_removal,[],[f12])).
% 19.42/3.06  
% 19.42/3.06  fof(f35,plain,(
% 19.42/3.06    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 19.42/3.06    inference(ennf_transformation,[],[f21])).
% 19.42/3.06  
% 19.42/3.06  fof(f71,plain,(
% 19.42/3.06    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 19.42/3.06    inference(cnf_transformation,[],[f35])).
% 19.42/3.06  
% 19.42/3.06  fof(f3,axiom,(
% 19.42/3.06    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 19.42/3.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.42/3.06  
% 19.42/3.06  fof(f49,plain,(
% 19.42/3.06    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 19.42/3.06    inference(nnf_transformation,[],[f3])).
% 19.42/3.06  
% 19.42/3.06  fof(f50,plain,(
% 19.42/3.06    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 19.42/3.06    inference(flattening,[],[f49])).
% 19.42/3.06  
% 19.42/3.06  fof(f57,plain,(
% 19.42/3.06    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 19.42/3.06    inference(cnf_transformation,[],[f50])).
% 19.42/3.06  
% 19.42/3.06  fof(f58,plain,(
% 19.42/3.06    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 19.42/3.06    inference(cnf_transformation,[],[f50])).
% 19.42/3.06  
% 19.42/3.06  fof(f91,plain,(
% 19.42/3.06    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 19.42/3.06    inference(equality_resolution,[],[f58])).
% 19.42/3.06  
% 19.42/3.06  fof(f59,plain,(
% 19.42/3.06    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 19.42/3.06    inference(cnf_transformation,[],[f50])).
% 19.42/3.06  
% 19.42/3.06  fof(f90,plain,(
% 19.42/3.06    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 19.42/3.06    inference(equality_resolution,[],[f59])).
% 19.42/3.06  
% 19.42/3.06  fof(f79,plain,(
% 19.42/3.06    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 19.42/3.06    inference(cnf_transformation,[],[f52])).
% 19.42/3.06  
% 19.42/3.06  fof(f94,plain,(
% 19.42/3.06    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 19.42/3.06    inference(equality_resolution,[],[f79])).
% 19.42/3.06  
% 19.42/3.06  fof(f88,plain,(
% 19.42/3.06    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 19.42/3.06    inference(cnf_transformation,[],[f54])).
% 19.42/3.06  
% 19.42/3.06  fof(f10,axiom,(
% 19.42/3.06    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 19.42/3.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.42/3.06  
% 19.42/3.06  fof(f32,plain,(
% 19.42/3.06    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 19.42/3.06    inference(ennf_transformation,[],[f10])).
% 19.42/3.06  
% 19.42/3.06  fof(f69,plain,(
% 19.42/3.06    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 19.42/3.06    inference(cnf_transformation,[],[f32])).
% 19.42/3.06  
% 19.42/3.06  fof(f2,axiom,(
% 19.42/3.06    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 19.42/3.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.42/3.06  
% 19.42/3.06  fof(f24,plain,(
% 19.42/3.06    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 19.42/3.06    inference(ennf_transformation,[],[f2])).
% 19.42/3.06  
% 19.42/3.06  fof(f56,plain,(
% 19.42/3.06    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 19.42/3.06    inference(cnf_transformation,[],[f24])).
% 19.42/3.06  
% 19.42/3.06  fof(f1,axiom,(
% 19.42/3.06    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 19.42/3.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.42/3.06  
% 19.42/3.06  fof(f22,plain,(
% 19.42/3.06    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 19.42/3.06    inference(ennf_transformation,[],[f1])).
% 19.42/3.06  
% 19.42/3.06  fof(f23,plain,(
% 19.42/3.06    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 19.42/3.06    inference(flattening,[],[f22])).
% 19.42/3.06  
% 19.42/3.06  fof(f55,plain,(
% 19.42/3.06    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 19.42/3.06    inference(cnf_transformation,[],[f23])).
% 19.42/3.06  
% 19.42/3.06  fof(f7,axiom,(
% 19.42/3.06    ! [X0,X1,X2] : ((v4_relat_1(X2,X1) & v1_relat_1(X2)) => (v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))))),
% 19.42/3.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.42/3.06  
% 19.42/3.06  fof(f28,plain,(
% 19.42/3.06    ! [X0,X1,X2] : ((v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))) | (~v4_relat_1(X2,X1) | ~v1_relat_1(X2)))),
% 19.42/3.06    inference(ennf_transformation,[],[f7])).
% 19.42/3.06  
% 19.42/3.06  fof(f29,plain,(
% 19.42/3.06    ! [X0,X1,X2] : ((v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))) | ~v4_relat_1(X2,X1) | ~v1_relat_1(X2))),
% 19.42/3.06    inference(flattening,[],[f28])).
% 19.42/3.06  
% 19.42/3.06  fof(f65,plain,(
% 19.42/3.06    ( ! [X2,X0,X1] : (v4_relat_1(k7_relat_1(X2,X0),X0) | ~v4_relat_1(X2,X1) | ~v1_relat_1(X2)) )),
% 19.42/3.06    inference(cnf_transformation,[],[f29])).
% 19.42/3.06  
% 19.42/3.06  fof(f87,plain,(
% 19.42/3.06    r1_tarski(sK2,sK0)),
% 19.42/3.06    inference(cnf_transformation,[],[f54])).
% 19.42/3.06  
% 19.42/3.06  fof(f11,axiom,(
% 19.42/3.06    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 19.42/3.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.42/3.06  
% 19.42/3.06  fof(f33,plain,(
% 19.42/3.06    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 19.42/3.06    inference(ennf_transformation,[],[f11])).
% 19.42/3.06  
% 19.42/3.06  fof(f34,plain,(
% 19.42/3.06    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 19.42/3.06    inference(flattening,[],[f33])).
% 19.42/3.06  
% 19.42/3.06  fof(f70,plain,(
% 19.42/3.06    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 19.42/3.06    inference(cnf_transformation,[],[f34])).
% 19.42/3.06  
% 19.42/3.06  fof(f18,axiom,(
% 19.42/3.06    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 19.42/3.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.42/3.06  
% 19.42/3.06  fof(f45,plain,(
% 19.42/3.06    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 19.42/3.06    inference(ennf_transformation,[],[f18])).
% 19.42/3.06  
% 19.42/3.06  fof(f46,plain,(
% 19.42/3.06    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 19.42/3.06    inference(flattening,[],[f45])).
% 19.42/3.06  
% 19.42/3.06  fof(f83,plain,(
% 19.42/3.06    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 19.42/3.06    inference(cnf_transformation,[],[f46])).
% 19.42/3.06  
% 19.42/3.06  fof(f84,plain,(
% 19.42/3.06    v1_funct_1(sK3)),
% 19.42/3.06    inference(cnf_transformation,[],[f54])).
% 19.42/3.06  
% 19.42/3.06  fof(f17,axiom,(
% 19.42/3.06    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 19.42/3.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.42/3.06  
% 19.42/3.06  fof(f43,plain,(
% 19.42/3.06    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 19.42/3.06    inference(ennf_transformation,[],[f17])).
% 19.42/3.06  
% 19.42/3.06  fof(f44,plain,(
% 19.42/3.06    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 19.42/3.06    inference(flattening,[],[f43])).
% 19.42/3.06  
% 19.42/3.06  fof(f82,plain,(
% 19.42/3.06    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 19.42/3.06    inference(cnf_transformation,[],[f44])).
% 19.42/3.06  
% 19.42/3.06  fof(f80,plain,(
% 19.42/3.06    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 19.42/3.06    inference(cnf_transformation,[],[f52])).
% 19.42/3.06  
% 19.42/3.06  fof(f92,plain,(
% 19.42/3.06    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 19.42/3.06    inference(equality_resolution,[],[f80])).
% 19.42/3.06  
% 19.42/3.06  fof(f93,plain,(
% 19.42/3.06    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 19.42/3.06    inference(equality_resolution,[],[f92])).
% 19.42/3.06  
% 19.42/3.06  fof(f89,plain,(
% 19.42/3.06    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 19.42/3.06    inference(cnf_transformation,[],[f54])).
% 19.42/3.06  
% 19.42/3.06  fof(f77,plain,(
% 19.42/3.06    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 19.42/3.06    inference(cnf_transformation,[],[f52])).
% 19.42/3.06  
% 19.42/3.06  fof(f81,plain,(
% 19.42/3.06    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 19.42/3.06    inference(cnf_transformation,[],[f44])).
% 19.42/3.06  
% 19.42/3.06  fof(f6,axiom,(
% 19.42/3.06    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 19.42/3.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.42/3.06  
% 19.42/3.06  fof(f27,plain,(
% 19.42/3.06    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 19.42/3.06    inference(ennf_transformation,[],[f6])).
% 19.42/3.06  
% 19.42/3.06  fof(f63,plain,(
% 19.42/3.06    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 19.42/3.06    inference(cnf_transformation,[],[f27])).
% 19.42/3.06  
% 19.42/3.06  fof(f78,plain,(
% 19.42/3.06    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 19.42/3.06    inference(cnf_transformation,[],[f52])).
% 19.42/3.06  
% 19.42/3.06  fof(f95,plain,(
% 19.42/3.06    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 19.42/3.06    inference(equality_resolution,[],[f78])).
% 19.42/3.06  
% 19.42/3.06  cnf(c_25,plain,
% 19.42/3.06      ( ~ v1_funct_2(X0,X1,X2)
% 19.42/3.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.42/3.06      | k1_relset_1(X1,X2,X0) = X1
% 19.42/3.06      | k1_xboole_0 = X2 ),
% 19.42/3.06      inference(cnf_transformation,[],[f75]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_33,negated_conjecture,
% 19.42/3.06      ( v1_funct_2(sK3,sK0,sK1) ),
% 19.42/3.06      inference(cnf_transformation,[],[f85]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_448,plain,
% 19.42/3.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.42/3.06      | k1_relset_1(X1,X2,X0) = X1
% 19.42/3.06      | sK3 != X0
% 19.42/3.06      | sK1 != X2
% 19.42/3.06      | sK0 != X1
% 19.42/3.06      | k1_xboole_0 = X2 ),
% 19.42/3.06      inference(resolution_lifted,[status(thm)],[c_25,c_33]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_449,plain,
% 19.42/3.06      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 19.42/3.06      | k1_relset_1(sK0,sK1,sK3) = sK0
% 19.42/3.06      | k1_xboole_0 = sK1 ),
% 19.42/3.06      inference(unflattening,[status(thm)],[c_448]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_32,negated_conjecture,
% 19.42/3.06      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 19.42/3.06      inference(cnf_transformation,[],[f86]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_451,plain,
% 19.42/3.06      ( k1_relset_1(sK0,sK1,sK3) = sK0 | k1_xboole_0 = sK1 ),
% 19.42/3.06      inference(global_propositional_subsumption,
% 19.42/3.06                [status(thm)],
% 19.42/3.06                [c_449,c_32]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_1218,plain,
% 19.42/3.06      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 19.42/3.06      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_17,plain,
% 19.42/3.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.42/3.06      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 19.42/3.06      inference(cnf_transformation,[],[f72]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_1225,plain,
% 19.42/3.06      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 19.42/3.06      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 19.42/3.06      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_2561,plain,
% 19.42/3.06      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 19.42/3.06      inference(superposition,[status(thm)],[c_1218,c_1225]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_2579,plain,
% 19.42/3.06      ( k1_relat_1(sK3) = sK0 | sK1 = k1_xboole_0 ),
% 19.42/3.06      inference(superposition,[status(thm)],[c_451,c_2561]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_19,plain,
% 19.42/3.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.42/3.06      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.42/3.06      | ~ r1_tarski(X3,X0) ),
% 19.42/3.06      inference(cnf_transformation,[],[f74]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_1223,plain,
% 19.42/3.06      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 19.42/3.06      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 19.42/3.06      | r1_tarski(X3,X0) != iProver_top ),
% 19.42/3.06      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_3294,plain,
% 19.42/3.06      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 19.42/3.06      | r1_tarski(X0,sK3) != iProver_top ),
% 19.42/3.06      inference(superposition,[status(thm)],[c_1218,c_1223]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_18,plain,
% 19.42/3.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.42/3.06      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 19.42/3.06      | ~ r1_tarski(k1_relat_1(X0),X3) ),
% 19.42/3.06      inference(cnf_transformation,[],[f73]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_1224,plain,
% 19.42/3.06      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 19.42/3.06      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) = iProver_top
% 19.42/3.06      | r1_tarski(k1_relat_1(X0),X3) != iProver_top ),
% 19.42/3.06      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_4417,plain,
% 19.42/3.06      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
% 19.42/3.06      | r1_tarski(X0,sK3) != iProver_top
% 19.42/3.06      | r1_tarski(k1_relat_1(X0),X1) != iProver_top ),
% 19.42/3.06      inference(superposition,[status(thm)],[c_3294,c_1224]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_6050,plain,
% 19.42/3.06      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
% 19.42/3.06      | r1_tarski(X0,X2) != iProver_top
% 19.42/3.06      | r1_tarski(X2,sK3) != iProver_top
% 19.42/3.06      | r1_tarski(k1_relat_1(X2),X1) != iProver_top ),
% 19.42/3.06      inference(superposition,[status(thm)],[c_4417,c_1223]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_22024,plain,
% 19.42/3.06      ( sK1 = k1_xboole_0
% 19.42/3.06      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
% 19.42/3.06      | r1_tarski(X0,sK3) != iProver_top
% 19.42/3.06      | r1_tarski(sK3,sK3) != iProver_top
% 19.42/3.06      | r1_tarski(sK0,X1) != iProver_top ),
% 19.42/3.06      inference(superposition,[status(thm)],[c_2579,c_6050]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_7,plain,
% 19.42/3.06      ( ~ v4_relat_1(X0,X1)
% 19.42/3.06      | r1_tarski(k1_relat_1(X0),X1)
% 19.42/3.06      | ~ v1_relat_1(X0) ),
% 19.42/3.06      inference(cnf_transformation,[],[f61]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_97,plain,
% 19.42/3.06      ( v4_relat_1(X0,X1) != iProver_top
% 19.42/3.06      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 19.42/3.06      | v1_relat_1(X0) != iProver_top ),
% 19.42/3.06      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_5,plain,
% 19.42/3.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 19.42/3.06      | ~ v1_relat_1(X1)
% 19.42/3.06      | v1_relat_1(X0) ),
% 19.42/3.06      inference(cnf_transformation,[],[f60]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_1237,plain,
% 19.42/3.06      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 19.42/3.06      | v1_relat_1(X1) != iProver_top
% 19.42/3.06      | v1_relat_1(X0) = iProver_top ),
% 19.42/3.06      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_3857,plain,
% 19.42/3.06      ( r1_tarski(X0,sK3) != iProver_top
% 19.42/3.06      | v1_relat_1(X0) = iProver_top
% 19.42/3.06      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top ),
% 19.42/3.06      inference(superposition,[status(thm)],[c_3294,c_1237]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_12,plain,
% 19.42/3.06      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 19.42/3.06      inference(cnf_transformation,[],[f67]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_2125,plain,
% 19.42/3.06      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 19.42/3.06      inference(instantiation,[status(thm)],[c_12]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_2126,plain,
% 19.42/3.06      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 19.42/3.06      inference(predicate_to_equality,[status(thm)],[c_2125]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_4318,plain,
% 19.42/3.06      ( v1_relat_1(X0) = iProver_top | r1_tarski(X0,sK3) != iProver_top ),
% 19.42/3.06      inference(global_propositional_subsumption,
% 19.42/3.06                [status(thm)],
% 19.42/3.06                [c_3857,c_2126]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_4319,plain,
% 19.42/3.06      ( r1_tarski(X0,sK3) != iProver_top | v1_relat_1(X0) = iProver_top ),
% 19.42/3.06      inference(renaming,[status(thm)],[c_4318]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_4416,plain,
% 19.42/3.06      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) = iProver_top
% 19.42/3.06      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
% 19.42/3.06      inference(superposition,[status(thm)],[c_1218,c_1224]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_4742,plain,
% 19.42/3.06      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
% 19.42/3.06      | r1_tarski(X0,sK3) != iProver_top
% 19.42/3.06      | r1_tarski(k1_relat_1(sK3),X1) != iProver_top ),
% 19.42/3.06      inference(superposition,[status(thm)],[c_4416,c_1223]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_16,plain,
% 19.42/3.06      ( v4_relat_1(X0,X1)
% 19.42/3.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 19.42/3.06      inference(cnf_transformation,[],[f71]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_1226,plain,
% 19.42/3.06      ( v4_relat_1(X0,X1) = iProver_top
% 19.42/3.06      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 19.42/3.06      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_6572,plain,
% 19.42/3.06      ( v4_relat_1(X0,X1) = iProver_top
% 19.42/3.06      | r1_tarski(X0,sK3) != iProver_top
% 19.42/3.06      | r1_tarski(k1_relat_1(sK3),X1) != iProver_top ),
% 19.42/3.06      inference(superposition,[status(thm)],[c_4742,c_1226]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_12001,plain,
% 19.42/3.06      ( sK1 = k1_xboole_0
% 19.42/3.06      | v4_relat_1(X0,X1) = iProver_top
% 19.42/3.06      | r1_tarski(X0,sK3) != iProver_top
% 19.42/3.06      | r1_tarski(sK0,X1) != iProver_top ),
% 19.42/3.06      inference(superposition,[status(thm)],[c_2579,c_6572]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_4,plain,
% 19.42/3.06      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 19.42/3.06      | k1_xboole_0 = X0
% 19.42/3.06      | k1_xboole_0 = X1 ),
% 19.42/3.06      inference(cnf_transformation,[],[f57]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_104,plain,
% 19.42/3.06      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 19.42/3.06      | k1_xboole_0 = k1_xboole_0 ),
% 19.42/3.06      inference(instantiation,[status(thm)],[c_4]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_3,plain,
% 19.42/3.06      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 19.42/3.06      inference(cnf_transformation,[],[f91]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_105,plain,
% 19.42/3.06      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 19.42/3.06      inference(instantiation,[status(thm)],[c_3]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_2,plain,
% 19.42/3.06      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 19.42/3.06      inference(cnf_transformation,[],[f90]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_1230,plain,
% 19.42/3.06      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 19.42/3.06      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_1836,plain,
% 19.42/3.06      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 19.42/3.06      inference(superposition,[status(thm)],[c_2,c_1230]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_21,plain,
% 19.42/3.06      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 19.42/3.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 19.42/3.06      | k1_xboole_0 = X1
% 19.42/3.06      | k1_xboole_0 = X0 ),
% 19.42/3.06      inference(cnf_transformation,[],[f94]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_380,plain,
% 19.42/3.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 19.42/3.06      | sK3 != X0
% 19.42/3.06      | sK1 != k1_xboole_0
% 19.42/3.06      | sK0 != X1
% 19.42/3.06      | k1_xboole_0 = X0
% 19.42/3.06      | k1_xboole_0 = X1 ),
% 19.42/3.06      inference(resolution_lifted,[status(thm)],[c_21,c_33]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_381,plain,
% 19.42/3.06      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
% 19.42/3.06      | sK1 != k1_xboole_0
% 19.42/3.06      | k1_xboole_0 = sK3
% 19.42/3.06      | k1_xboole_0 = sK0 ),
% 19.42/3.06      inference(unflattening,[status(thm)],[c_380]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_1215,plain,
% 19.42/3.06      ( sK1 != k1_xboole_0
% 19.42/3.06      | k1_xboole_0 = sK3
% 19.42/3.06      | k1_xboole_0 = sK0
% 19.42/3.06      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
% 19.42/3.06      inference(predicate_to_equality,[status(thm)],[c_381]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_1341,plain,
% 19.42/3.06      ( sK3 = k1_xboole_0
% 19.42/3.06      | sK1 != k1_xboole_0
% 19.42/3.06      | sK0 = k1_xboole_0
% 19.42/3.06      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 19.42/3.06      inference(demodulation,[status(thm)],[c_1215,c_2]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_30,negated_conjecture,
% 19.42/3.06      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 19.42/3.06      inference(cnf_transformation,[],[f88]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_707,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_1552,plain,
% 19.42/3.06      ( sK0 != X0 | sK0 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 19.42/3.06      inference(instantiation,[status(thm)],[c_707]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_1815,plain,
% 19.42/3.06      ( sK0 != sK0 | sK0 = k1_xboole_0 | k1_xboole_0 != sK0 ),
% 19.42/3.06      inference(instantiation,[status(thm)],[c_1552]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_706,plain,( X0 = X0 ),theory(equality) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_1816,plain,
% 19.42/3.06      ( sK0 = sK0 ),
% 19.42/3.06      inference(instantiation,[status(thm)],[c_706]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_1894,plain,
% 19.42/3.06      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 19.42/3.06      inference(instantiation,[status(thm)],[c_707]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_1895,plain,
% 19.42/3.06      ( sK1 != k1_xboole_0
% 19.42/3.06      | k1_xboole_0 = sK1
% 19.42/3.06      | k1_xboole_0 != k1_xboole_0 ),
% 19.42/3.06      inference(instantiation,[status(thm)],[c_1894]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_2059,plain,
% 19.42/3.06      ( sK0 = k1_xboole_0 | sK1 != k1_xboole_0 ),
% 19.42/3.06      inference(global_propositional_subsumption,
% 19.42/3.06                [status(thm)],
% 19.42/3.06                [c_1341,c_30,c_104,c_105,c_1815,c_1816,c_1895]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_2060,plain,
% 19.42/3.06      ( sK1 != k1_xboole_0 | sK0 = k1_xboole_0 ),
% 19.42/3.06      inference(renaming,[status(thm)],[c_2059]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_2300,plain,
% 19.42/3.06      ( v4_relat_1(X0,X1) = iProver_top
% 19.42/3.06      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 19.42/3.06      inference(superposition,[status(thm)],[c_2,c_1226]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_14,plain,
% 19.42/3.06      ( r1_tarski(k7_relat_1(X0,X1),X0) | ~ v1_relat_1(X0) ),
% 19.42/3.06      inference(cnf_transformation,[],[f69]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_1228,plain,
% 19.42/3.06      ( r1_tarski(k7_relat_1(X0,X1),X0) = iProver_top
% 19.42/3.06      | v1_relat_1(X0) != iProver_top ),
% 19.42/3.06      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_1,plain,
% 19.42/3.06      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 19.42/3.06      inference(cnf_transformation,[],[f56]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_1238,plain,
% 19.42/3.06      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 19.42/3.06      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_2211,plain,
% 19.42/3.06      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0
% 19.42/3.06      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 19.42/3.06      inference(superposition,[status(thm)],[c_1228,c_1238]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_2399,plain,
% 19.42/3.06      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 19.42/3.06      inference(global_propositional_subsumption,
% 19.42/3.06                [status(thm)],
% 19.42/3.06                [c_2211,c_1836]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_2403,plain,
% 19.42/3.06      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top
% 19.42/3.06      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 19.42/3.06      inference(superposition,[status(thm)],[c_2399,c_1228]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_708,plain,
% 19.42/3.06      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 19.42/3.06      theory(equality) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_4922,plain,
% 19.42/3.06      ( ~ r1_tarski(X0,X1)
% 19.42/3.06      | r1_tarski(sK0,k1_xboole_0)
% 19.42/3.06      | sK0 != X0
% 19.42/3.06      | k1_xboole_0 != X1 ),
% 19.42/3.06      inference(instantiation,[status(thm)],[c_708]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_4923,plain,
% 19.42/3.06      ( sK0 != X0
% 19.42/3.06      | k1_xboole_0 != X1
% 19.42/3.06      | r1_tarski(X0,X1) != iProver_top
% 19.42/3.06      | r1_tarski(sK0,k1_xboole_0) = iProver_top ),
% 19.42/3.06      inference(predicate_to_equality,[status(thm)],[c_4922]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_4925,plain,
% 19.42/3.06      ( sK0 != k1_xboole_0
% 19.42/3.06      | k1_xboole_0 != k1_xboole_0
% 19.42/3.06      | r1_tarski(sK0,k1_xboole_0) = iProver_top
% 19.42/3.06      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 19.42/3.06      inference(instantiation,[status(thm)],[c_4923]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_4739,plain,
% 19.42/3.06      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 19.42/3.06      | r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top ),
% 19.42/3.06      inference(superposition,[status(thm)],[c_3,c_4416]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_4945,plain,
% 19.42/3.06      ( sK1 = k1_xboole_0
% 19.42/3.06      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 19.42/3.06      | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
% 19.42/3.06      inference(superposition,[status(thm)],[c_2579,c_4739]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_37,plain,
% 19.42/3.06      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 19.42/3.06      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_1525,plain,
% 19.42/3.06      ( v4_relat_1(sK3,sK0)
% 19.42/3.06      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 19.42/3.06      inference(instantiation,[status(thm)],[c_16]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_1526,plain,
% 19.42/3.06      ( v4_relat_1(sK3,sK0) = iProver_top
% 19.42/3.06      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 19.42/3.06      inference(predicate_to_equality,[status(thm)],[c_1525]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_1486,plain,
% 19.42/3.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.42/3.06      | v1_relat_1(X0)
% 19.42/3.06      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 19.42/3.06      inference(instantiation,[status(thm)],[c_5]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_1769,plain,
% 19.42/3.06      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 19.42/3.06      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
% 19.42/3.06      | v1_relat_1(sK3) ),
% 19.42/3.06      inference(instantiation,[status(thm)],[c_1486]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_1770,plain,
% 19.42/3.06      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 19.42/3.06      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 19.42/3.06      | v1_relat_1(sK3) = iProver_top ),
% 19.42/3.06      inference(predicate_to_equality,[status(thm)],[c_1769]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_3080,plain,
% 19.42/3.06      ( ~ v4_relat_1(sK3,sK0)
% 19.42/3.06      | r1_tarski(k1_relat_1(sK3),sK0)
% 19.42/3.06      | ~ v1_relat_1(sK3) ),
% 19.42/3.06      inference(instantiation,[status(thm)],[c_7]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_3081,plain,
% 19.42/3.06      ( v4_relat_1(sK3,sK0) != iProver_top
% 19.42/3.06      | r1_tarski(k1_relat_1(sK3),sK0) = iProver_top
% 19.42/3.06      | v1_relat_1(sK3) != iProver_top ),
% 19.42/3.06      inference(predicate_to_equality,[status(thm)],[c_3080]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_0,plain,
% 19.42/3.06      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 19.42/3.06      inference(cnf_transformation,[],[f55]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_2318,plain,
% 19.42/3.06      ( ~ r1_tarski(X0,X1)
% 19.42/3.06      | ~ r1_tarski(k1_relat_1(X2),X0)
% 19.42/3.06      | r1_tarski(k1_relat_1(X2),X1) ),
% 19.42/3.06      inference(instantiation,[status(thm)],[c_0]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_4103,plain,
% 19.42/3.06      ( r1_tarski(k1_relat_1(sK3),X0)
% 19.42/3.06      | ~ r1_tarski(k1_relat_1(sK3),sK0)
% 19.42/3.06      | ~ r1_tarski(sK0,X0) ),
% 19.42/3.06      inference(instantiation,[status(thm)],[c_2318]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_4104,plain,
% 19.42/3.06      ( r1_tarski(k1_relat_1(sK3),X0) = iProver_top
% 19.42/3.06      | r1_tarski(k1_relat_1(sK3),sK0) != iProver_top
% 19.42/3.06      | r1_tarski(sK0,X0) != iProver_top ),
% 19.42/3.06      inference(predicate_to_equality,[status(thm)],[c_4103]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_4106,plain,
% 19.42/3.06      ( r1_tarski(k1_relat_1(sK3),sK0) != iProver_top
% 19.42/3.06      | r1_tarski(k1_relat_1(sK3),k1_xboole_0) = iProver_top
% 19.42/3.06      | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
% 19.42/3.06      inference(instantiation,[status(thm)],[c_4104]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_6894,plain,
% 19.42/3.06      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 19.42/3.06      | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
% 19.42/3.06      inference(global_propositional_subsumption,
% 19.42/3.06                [status(thm)],
% 19.42/3.06                [c_4945,c_37,c_1526,c_1770,c_2126,c_3081,c_4106,c_4739]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_3297,plain,
% 19.42/3.06      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) = iProver_top
% 19.42/3.06      | m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 19.42/3.06      | r1_tarski(X0,X2) != iProver_top ),
% 19.42/3.06      inference(superposition,[status(thm)],[c_3,c_1223]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_3301,plain,
% 19.42/3.06      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 19.42/3.06      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 19.42/3.06      | r1_tarski(X1,X0) != iProver_top ),
% 19.42/3.06      inference(demodulation,[status(thm)],[c_3297,c_3]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_6901,plain,
% 19.42/3.06      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 19.42/3.06      | r1_tarski(X0,sK3) != iProver_top
% 19.42/3.06      | r1_tarski(sK0,k1_xboole_0) != iProver_top ),
% 19.42/3.06      inference(superposition,[status(thm)],[c_6894,c_3301]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_12040,plain,
% 19.42/3.06      ( v4_relat_1(X0,X1) = iProver_top
% 19.42/3.06      | r1_tarski(X0,sK3) != iProver_top
% 19.42/3.06      | r1_tarski(sK0,X1) != iProver_top ),
% 19.42/3.06      inference(global_propositional_subsumption,
% 19.42/3.06                [status(thm)],
% 19.42/3.06                [c_12001,c_104,c_105,c_1836,c_2060,c_2300,c_2403,c_4925,
% 19.42/3.06                 c_6901]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_22174,plain,
% 19.42/3.06      ( r1_tarski(X0,sK3) != iProver_top
% 19.42/3.06      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
% 19.42/3.06      | r1_tarski(sK0,X1) != iProver_top ),
% 19.42/3.06      inference(global_propositional_subsumption,
% 19.42/3.06                [status(thm)],
% 19.42/3.06                [c_22024,c_97,c_4319,c_4417,c_12040]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_22175,plain,
% 19.42/3.06      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
% 19.42/3.06      | r1_tarski(X0,sK3) != iProver_top
% 19.42/3.06      | r1_tarski(sK0,X1) != iProver_top ),
% 19.42/3.06      inference(renaming,[status(thm)],[c_22174]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_2299,plain,
% 19.42/3.06      ( v4_relat_1(sK3,sK0) = iProver_top ),
% 19.42/3.06      inference(superposition,[status(thm)],[c_1218,c_1226]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_10,plain,
% 19.42/3.06      ( ~ v4_relat_1(X0,X1)
% 19.42/3.06      | v4_relat_1(k7_relat_1(X0,X2),X2)
% 19.42/3.06      | ~ v1_relat_1(X0) ),
% 19.42/3.06      inference(cnf_transformation,[],[f65]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_1232,plain,
% 19.42/3.06      ( v4_relat_1(X0,X1) != iProver_top
% 19.42/3.06      | v4_relat_1(k7_relat_1(X0,X2),X2) = iProver_top
% 19.42/3.06      | v1_relat_1(X0) != iProver_top ),
% 19.42/3.06      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_4466,plain,
% 19.42/3.06      ( v4_relat_1(k7_relat_1(sK3,X0),X0) = iProver_top
% 19.42/3.06      | v1_relat_1(sK3) != iProver_top ),
% 19.42/3.06      inference(superposition,[status(thm)],[c_2299,c_1232]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_3719,plain,
% 19.42/3.06      ( v4_relat_1(k7_relat_1(sK3,X0),X0)
% 19.42/3.06      | ~ v4_relat_1(sK3,sK0)
% 19.42/3.06      | ~ v1_relat_1(sK3) ),
% 19.42/3.06      inference(instantiation,[status(thm)],[c_10]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_3720,plain,
% 19.42/3.06      ( v4_relat_1(k7_relat_1(sK3,X0),X0) = iProver_top
% 19.42/3.06      | v4_relat_1(sK3,sK0) != iProver_top
% 19.42/3.06      | v1_relat_1(sK3) != iProver_top ),
% 19.42/3.06      inference(predicate_to_equality,[status(thm)],[c_3719]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_4855,plain,
% 19.42/3.06      ( v4_relat_1(k7_relat_1(sK3,X0),X0) = iProver_top ),
% 19.42/3.06      inference(global_propositional_subsumption,
% 19.42/3.06                [status(thm)],
% 19.42/3.06                [c_4466,c_37,c_1526,c_1770,c_2126,c_3720]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_31,negated_conjecture,
% 19.42/3.06      ( r1_tarski(sK2,sK0) ),
% 19.42/3.06      inference(cnf_transformation,[],[f87]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_1219,plain,
% 19.42/3.06      ( r1_tarski(sK2,sK0) = iProver_top ),
% 19.42/3.06      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_15,plain,
% 19.42/3.06      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 19.42/3.06      | ~ v1_relat_1(X1)
% 19.42/3.06      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 19.42/3.06      inference(cnf_transformation,[],[f70]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_1227,plain,
% 19.42/3.06      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 19.42/3.06      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 19.42/3.06      | v1_relat_1(X0) != iProver_top ),
% 19.42/3.06      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_3633,plain,
% 19.42/3.06      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 19.42/3.06      | sK1 = k1_xboole_0
% 19.42/3.06      | r1_tarski(X0,sK0) != iProver_top
% 19.42/3.06      | v1_relat_1(sK3) != iProver_top ),
% 19.42/3.06      inference(superposition,[status(thm)],[c_2579,c_1227]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_7464,plain,
% 19.42/3.06      ( r1_tarski(X0,sK0) != iProver_top
% 19.42/3.06      | sK1 = k1_xboole_0
% 19.42/3.06      | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
% 19.42/3.06      inference(global_propositional_subsumption,
% 19.42/3.06                [status(thm)],
% 19.42/3.06                [c_3633,c_37,c_1770,c_2126]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_7465,plain,
% 19.42/3.06      ( k1_relat_1(k7_relat_1(sK3,X0)) = X0
% 19.42/3.06      | sK1 = k1_xboole_0
% 19.42/3.06      | r1_tarski(X0,sK0) != iProver_top ),
% 19.42/3.06      inference(renaming,[status(thm)],[c_7464]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_7475,plain,
% 19.42/3.06      ( k1_relat_1(k7_relat_1(sK3,sK2)) = sK2 | sK1 = k1_xboole_0 ),
% 19.42/3.06      inference(superposition,[status(thm)],[c_1219,c_7465]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_1235,plain,
% 19.42/3.06      ( v4_relat_1(X0,X1) != iProver_top
% 19.42/3.06      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 19.42/3.06      | v1_relat_1(X0) != iProver_top ),
% 19.42/3.06      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_7532,plain,
% 19.42/3.06      ( sK1 = k1_xboole_0
% 19.42/3.06      | v4_relat_1(k7_relat_1(sK3,sK2),X0) != iProver_top
% 19.42/3.06      | r1_tarski(sK2,X0) = iProver_top
% 19.42/3.06      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 19.42/3.06      inference(superposition,[status(thm)],[c_7475,c_1235]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_28,plain,
% 19.42/3.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.42/3.06      | ~ v1_funct_1(X0)
% 19.42/3.06      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 19.42/3.06      inference(cnf_transformation,[],[f83]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_1220,plain,
% 19.42/3.06      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 19.42/3.06      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 19.42/3.06      | v1_funct_1(X2) != iProver_top ),
% 19.42/3.06      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_1629,plain,
% 19.42/3.06      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
% 19.42/3.06      | v1_funct_1(sK3) != iProver_top ),
% 19.42/3.06      inference(superposition,[status(thm)],[c_1218,c_1220]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_34,negated_conjecture,
% 19.42/3.06      ( v1_funct_1(sK3) ),
% 19.42/3.06      inference(cnf_transformation,[],[f84]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_35,plain,
% 19.42/3.06      ( v1_funct_1(sK3) = iProver_top ),
% 19.42/3.06      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_1840,plain,
% 19.42/3.06      ( k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) ),
% 19.42/3.06      inference(global_propositional_subsumption,
% 19.42/3.06                [status(thm)],
% 19.42/3.06                [c_1629,c_35]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_26,plain,
% 19.42/3.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.42/3.06      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.42/3.06      | ~ v1_funct_1(X0) ),
% 19.42/3.06      inference(cnf_transformation,[],[f82]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_1222,plain,
% 19.42/3.06      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 19.42/3.06      | m1_subset_1(k2_partfun1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 19.42/3.06      | v1_funct_1(X0) != iProver_top ),
% 19.42/3.06      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_2622,plain,
% 19.42/3.06      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 19.42/3.06      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 19.42/3.06      | v1_funct_1(sK3) != iProver_top ),
% 19.42/3.06      inference(superposition,[status(thm)],[c_1840,c_1222]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_3004,plain,
% 19.42/3.06      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 19.42/3.06      inference(global_propositional_subsumption,
% 19.42/3.06                [status(thm)],
% 19.42/3.06                [c_2622,c_35,c_37]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_3012,plain,
% 19.42/3.06      ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top
% 19.42/3.06      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top ),
% 19.42/3.06      inference(superposition,[status(thm)],[c_3004,c_1237]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_3281,plain,
% 19.42/3.06      ( v1_relat_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 19.42/3.06      inference(global_propositional_subsumption,
% 19.42/3.06                [status(thm)],
% 19.42/3.06                [c_3012,c_2126]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_8282,plain,
% 19.42/3.06      ( sK1 = k1_xboole_0
% 19.42/3.06      | v4_relat_1(k7_relat_1(sK3,sK2),X0) != iProver_top
% 19.42/3.06      | r1_tarski(sK2,X0) = iProver_top ),
% 19.42/3.06      inference(forward_subsumption_resolution,
% 19.42/3.06                [status(thm)],
% 19.42/3.06                [c_7532,c_3281]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_8288,plain,
% 19.42/3.06      ( sK1 = k1_xboole_0 | r1_tarski(sK2,sK2) = iProver_top ),
% 19.42/3.06      inference(superposition,[status(thm)],[c_4855,c_8282]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_38,plain,
% 19.42/3.06      ( r1_tarski(sK2,sK0) = iProver_top ),
% 19.42/3.06      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_1553,plain,
% 19.42/3.06      ( sK2 != X0 | sK2 = sK0 | sK0 != X0 ),
% 19.42/3.06      inference(instantiation,[status(thm)],[c_707]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_1554,plain,
% 19.42/3.06      ( sK2 = sK0 | sK2 != k1_xboole_0 | sK0 != k1_xboole_0 ),
% 19.42/3.06      inference(instantiation,[status(thm)],[c_1553]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_1684,plain,
% 19.42/3.06      ( sK2 = sK2 ),
% 19.42/3.06      inference(instantiation,[status(thm)],[c_706]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_20,plain,
% 19.42/3.06      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
% 19.42/3.06      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 19.42/3.06      | k1_xboole_0 = X0 ),
% 19.42/3.06      inference(cnf_transformation,[],[f93]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_29,negated_conjecture,
% 19.42/3.06      ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
% 19.42/3.06      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 19.42/3.06      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
% 19.42/3.06      inference(cnf_transformation,[],[f89]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_354,plain,
% 19.42/3.06      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 19.42/3.06      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 19.42/3.06      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 19.42/3.06      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 19.42/3.06      | sK2 != X0
% 19.42/3.06      | sK1 != k1_xboole_0
% 19.42/3.06      | k1_xboole_0 = X0 ),
% 19.42/3.06      inference(resolution_lifted,[status(thm)],[c_20,c_29]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_355,plain,
% 19.42/3.06      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 19.42/3.06      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0)))
% 19.42/3.06      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 19.42/3.06      | k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 19.42/3.06      | sK1 != k1_xboole_0
% 19.42/3.06      | k1_xboole_0 = sK2 ),
% 19.42/3.06      inference(unflattening,[status(thm)],[c_354]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_1216,plain,
% 19.42/3.06      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 19.42/3.06      | sK1 != k1_xboole_0
% 19.42/3.06      | k1_xboole_0 = sK2
% 19.42/3.06      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 19.42/3.06      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
% 19.42/3.06      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 19.42/3.06      inference(predicate_to_equality,[status(thm)],[c_355]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_1396,plain,
% 19.42/3.06      ( k2_partfun1(sK0,sK1,sK3,sK2) != k1_xboole_0
% 19.42/3.06      | sK2 = k1_xboole_0
% 19.42/3.06      | sK1 != k1_xboole_0
% 19.42/3.06      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 19.42/3.06      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 19.42/3.06      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 19.42/3.06      inference(demodulation,[status(thm)],[c_1216,c_2]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_1678,plain,
% 19.42/3.06      ( ~ r1_tarski(sK2,k1_xboole_0) | k1_xboole_0 = sK2 ),
% 19.42/3.06      inference(instantiation,[status(thm)],[c_1]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_1568,plain,
% 19.42/3.06      ( r1_tarski(X0,X1) | ~ r1_tarski(sK2,sK0) | X0 != sK2 | X1 != sK0 ),
% 19.42/3.06      inference(instantiation,[status(thm)],[c_708]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_1683,plain,
% 19.42/3.06      ( r1_tarski(sK2,X0)
% 19.42/3.06      | ~ r1_tarski(sK2,sK0)
% 19.42/3.06      | X0 != sK0
% 19.42/3.06      | sK2 != sK2 ),
% 19.42/3.06      inference(instantiation,[status(thm)],[c_1568]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_1686,plain,
% 19.42/3.06      ( ~ r1_tarski(sK2,sK0)
% 19.42/3.06      | r1_tarski(sK2,k1_xboole_0)
% 19.42/3.06      | sK2 != sK2
% 19.42/3.06      | k1_xboole_0 != sK0 ),
% 19.42/3.06      inference(instantiation,[status(thm)],[c_1683]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_1551,plain,
% 19.42/3.06      ( sK2 != X0 | sK2 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 19.42/3.06      inference(instantiation,[status(thm)],[c_707]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_1814,plain,
% 19.42/3.06      ( sK2 != sK2 | sK2 = k1_xboole_0 | k1_xboole_0 != sK2 ),
% 19.42/3.06      inference(instantiation,[status(thm)],[c_1551]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_1970,plain,
% 19.42/3.06      ( sK1 != k1_xboole_0 | sK2 = k1_xboole_0 ),
% 19.42/3.06      inference(global_propositional_subsumption,
% 19.42/3.06                [status(thm)],
% 19.42/3.06                [c_1396,c_31,c_30,c_104,c_105,c_1678,c_1686,c_1684,
% 19.42/3.06                 c_1814,c_1895]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_1971,plain,
% 19.42/3.06      ( sK2 = k1_xboole_0 | sK1 != k1_xboole_0 ),
% 19.42/3.06      inference(renaming,[status(thm)],[c_1970]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_4313,plain,
% 19.42/3.06      ( r1_tarski(sK2,sK2)
% 19.42/3.06      | ~ r1_tarski(sK2,sK0)
% 19.42/3.06      | sK2 != sK2
% 19.42/3.06      | sK2 != sK0 ),
% 19.42/3.06      inference(instantiation,[status(thm)],[c_1683]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_4314,plain,
% 19.42/3.06      ( sK2 != sK2
% 19.42/3.06      | sK2 != sK0
% 19.42/3.06      | r1_tarski(sK2,sK2) = iProver_top
% 19.42/3.06      | r1_tarski(sK2,sK0) != iProver_top ),
% 19.42/3.06      inference(predicate_to_equality,[status(thm)],[c_4313]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_79273,plain,
% 19.42/3.06      ( r1_tarski(sK2,sK2) = iProver_top ),
% 19.42/3.06      inference(global_propositional_subsumption,
% 19.42/3.06                [status(thm)],
% 19.42/3.06                [c_8288,c_38,c_1554,c_1684,c_1971,c_2060,c_4314]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_4418,plain,
% 19.42/3.06      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) = iProver_top
% 19.42/3.06      | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X1) != iProver_top ),
% 19.42/3.06      inference(superposition,[status(thm)],[c_3004,c_1224]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_11842,plain,
% 19.42/3.06      ( k1_relset_1(X0,sK1,k7_relat_1(sK3,X1)) = k1_relat_1(k7_relat_1(sK3,X1))
% 19.42/3.06      | r1_tarski(k1_relat_1(k7_relat_1(sK3,X1)),X0) != iProver_top ),
% 19.42/3.06      inference(superposition,[status(thm)],[c_4418,c_1225]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_24422,plain,
% 19.42/3.06      ( k1_relset_1(X0,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
% 19.42/3.06      | sK1 = k1_xboole_0
% 19.42/3.06      | r1_tarski(sK2,X0) != iProver_top ),
% 19.42/3.06      inference(superposition,[status(thm)],[c_7475,c_11842]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_79299,plain,
% 19.42/3.06      ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) = k1_relat_1(k7_relat_1(sK3,sK2))
% 19.42/3.06      | sK1 = k1_xboole_0 ),
% 19.42/3.06      inference(superposition,[status(thm)],[c_79273,c_24422]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_23,plain,
% 19.42/3.06      ( v1_funct_2(X0,X1,X2)
% 19.42/3.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.42/3.06      | k1_relset_1(X1,X2,X0) != X1
% 19.42/3.06      | k1_xboole_0 = X2 ),
% 19.42/3.06      inference(cnf_transformation,[],[f77]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_432,plain,
% 19.42/3.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.42/3.06      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 19.42/3.06      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 19.42/3.06      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 19.42/3.06      | k1_relset_1(X1,X2,X0) != X1
% 19.42/3.06      | sK2 != X1
% 19.42/3.06      | sK1 != X2
% 19.42/3.06      | k1_xboole_0 = X2 ),
% 19.42/3.06      inference(resolution_lifted,[status(thm)],[c_23,c_29]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_433,plain,
% 19.42/3.06      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 19.42/3.06      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 19.42/3.06      | k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 19.42/3.06      | k1_xboole_0 = sK1 ),
% 19.42/3.06      inference(unflattening,[status(thm)],[c_432]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_1212,plain,
% 19.42/3.06      ( k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != sK2
% 19.42/3.06      | k1_xboole_0 = sK1
% 19.42/3.06      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 19.42/3.06      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 19.42/3.06      inference(predicate_to_equality,[status(thm)],[c_433]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_1845,plain,
% 19.42/3.06      ( k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) != sK2
% 19.42/3.06      | sK1 = k1_xboole_0
% 19.42/3.06      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 19.42/3.06      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 19.42/3.06      inference(demodulation,[status(thm)],[c_1840,c_1212]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_88118,plain,
% 19.42/3.06      ( k1_relat_1(k7_relat_1(sK3,sK2)) != sK2
% 19.42/3.06      | sK1 = k1_xboole_0
% 19.42/3.06      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 19.42/3.06      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 19.42/3.06      inference(superposition,[status(thm)],[c_79299,c_1845]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_89307,plain,
% 19.42/3.06      ( sK1 = k1_xboole_0
% 19.42/3.06      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 19.42/3.06      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 19.42/3.06      inference(global_propositional_subsumption,
% 19.42/3.06                [status(thm)],
% 19.42/3.06                [c_88118,c_7475]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_27,plain,
% 19.42/3.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 19.42/3.06      | ~ v1_funct_1(X0)
% 19.42/3.06      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) ),
% 19.42/3.06      inference(cnf_transformation,[],[f81]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_1221,plain,
% 19.42/3.06      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 19.42/3.06      | v1_funct_1(X0) != iProver_top
% 19.42/3.06      | v1_funct_1(k2_partfun1(X1,X2,X0,X3)) = iProver_top ),
% 19.42/3.06      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_2098,plain,
% 19.42/3.06      ( v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) = iProver_top
% 19.42/3.06      | v1_funct_1(sK3) != iProver_top ),
% 19.42/3.06      inference(superposition,[status(thm)],[c_1218,c_1221]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_2115,plain,
% 19.42/3.06      ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top
% 19.42/3.06      | v1_funct_1(sK3) != iProver_top ),
% 19.42/3.06      inference(light_normalisation,[status(thm)],[c_2098,c_1840]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_2391,plain,
% 19.42/3.06      ( v1_funct_1(k7_relat_1(sK3,X0)) = iProver_top ),
% 19.42/3.06      inference(global_propositional_subsumption,
% 19.42/3.06                [status(thm)],
% 19.42/3.06                [c_2115,c_35]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_89314,plain,
% 19.42/3.06      ( sK1 = k1_xboole_0
% 19.42/3.06      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 19.42/3.06      inference(forward_subsumption_resolution,
% 19.42/3.06                [status(thm)],
% 19.42/3.06                [c_89307,c_2391]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_89324,plain,
% 19.42/3.06      ( sK1 = k1_xboole_0
% 19.42/3.06      | r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top
% 19.42/3.06      | r1_tarski(sK0,sK2) != iProver_top ),
% 19.42/3.06      inference(superposition,[status(thm)],[c_22175,c_89314]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_4513,plain,
% 19.42/3.06      ( ~ v4_relat_1(k7_relat_1(sK3,X0),X0)
% 19.42/3.06      | r1_tarski(k1_relat_1(k7_relat_1(sK3,X0)),X0)
% 19.42/3.06      | ~ v1_relat_1(k7_relat_1(sK3,X0)) ),
% 19.42/3.06      inference(instantiation,[status(thm)],[c_7]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_10467,plain,
% 19.42/3.06      ( ~ v4_relat_1(k7_relat_1(sK3,sK2),sK2)
% 19.42/3.06      | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2)
% 19.42/3.06      | ~ v1_relat_1(k7_relat_1(sK3,sK2)) ),
% 19.42/3.06      inference(instantiation,[status(thm)],[c_4513]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_10473,plain,
% 19.42/3.06      ( v4_relat_1(k7_relat_1(sK3,sK2),sK2) != iProver_top
% 19.42/3.06      | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) = iProver_top
% 19.42/3.06      | v1_relat_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 19.42/3.06      inference(predicate_to_equality,[status(thm)],[c_10467]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_8,plain,
% 19.42/3.06      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 19.42/3.06      inference(cnf_transformation,[],[f63]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_15511,plain,
% 19.42/3.06      ( v1_relat_1(k7_relat_1(sK3,sK2)) | ~ v1_relat_1(sK3) ),
% 19.42/3.06      inference(instantiation,[status(thm)],[c_8]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_15512,plain,
% 19.42/3.06      ( v1_relat_1(k7_relat_1(sK3,sK2)) = iProver_top
% 19.42/3.06      | v1_relat_1(sK3) != iProver_top ),
% 19.42/3.06      inference(predicate_to_equality,[status(thm)],[c_15511]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_17065,plain,
% 19.42/3.06      ( v4_relat_1(k7_relat_1(sK3,sK2),sK2)
% 19.42/3.06      | ~ v4_relat_1(sK3,sK0)
% 19.42/3.06      | ~ v1_relat_1(sK3) ),
% 19.42/3.06      inference(instantiation,[status(thm)],[c_3719]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_17066,plain,
% 19.42/3.06      ( v4_relat_1(k7_relat_1(sK3,sK2),sK2) = iProver_top
% 19.42/3.06      | v4_relat_1(sK3,sK0) != iProver_top
% 19.42/3.06      | v1_relat_1(sK3) != iProver_top ),
% 19.42/3.06      inference(predicate_to_equality,[status(thm)],[c_17065]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_89328,plain,
% 19.42/3.06      ( sK1 = k1_xboole_0
% 19.42/3.06      | r1_tarski(k1_relat_1(k7_relat_1(sK3,sK2)),sK2) != iProver_top ),
% 19.42/3.06      inference(superposition,[status(thm)],[c_4418,c_89314]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_89465,plain,
% 19.42/3.06      ( sK1 = k1_xboole_0 ),
% 19.42/3.06      inference(global_propositional_subsumption,
% 19.42/3.06                [status(thm)],
% 19.42/3.06                [c_89324,c_37,c_1526,c_1770,c_2126,c_10473,c_15512,
% 19.42/3.06                 c_17066,c_89328]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_3015,plain,
% 19.42/3.06      ( k1_relset_1(sK0,sK1,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
% 19.42/3.06      inference(superposition,[status(thm)],[c_3004,c_1225]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_89764,plain,
% 19.42/3.06      ( k1_relset_1(sK0,k1_xboole_0,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
% 19.42/3.06      inference(demodulation,[status(thm)],[c_89465,c_3015]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_89776,plain,
% 19.42/3.06      ( sK0 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 19.42/3.06      inference(demodulation,[status(thm)],[c_89465,c_30]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_89777,plain,
% 19.42/3.06      ( sK0 = k1_xboole_0 ),
% 19.42/3.06      inference(equality_resolution_simp,[status(thm)],[c_89776]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_89842,plain,
% 19.42/3.06      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,X0)) = k1_relat_1(k7_relat_1(sK3,X0)) ),
% 19.42/3.06      inference(light_normalisation,[status(thm)],[c_89764,c_89777]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_89765,plain,
% 19.42/3.06      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
% 19.42/3.06      inference(demodulation,[status(thm)],[c_89465,c_3004]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_89828,plain,
% 19.42/3.06      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 19.42/3.06      inference(light_normalisation,[status(thm)],[c_89765,c_89777]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_89830,plain,
% 19.42/3.06      ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 19.42/3.06      inference(demodulation,[status(thm)],[c_89828,c_3]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_22,plain,
% 19.42/3.06      ( v1_funct_2(X0,k1_xboole_0,X1)
% 19.42/3.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 19.42/3.06      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 19.42/3.06      inference(cnf_transformation,[],[f95]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_400,plain,
% 19.42/3.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 19.42/3.06      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 19.42/3.06      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 19.42/3.06      | k2_partfun1(sK0,sK1,sK3,sK2) != X0
% 19.42/3.06      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 19.42/3.06      | sK2 != k1_xboole_0
% 19.42/3.06      | sK1 != X1 ),
% 19.42/3.06      inference(resolution_lifted,[status(thm)],[c_22,c_29]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_401,plain,
% 19.42/3.06      ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 19.42/3.06      | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 19.42/3.06      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
% 19.42/3.06      | k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
% 19.42/3.06      | sK2 != k1_xboole_0 ),
% 19.42/3.06      inference(unflattening,[status(thm)],[c_400]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_1214,plain,
% 19.42/3.06      ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
% 19.42/3.06      | sK2 != k1_xboole_0
% 19.42/3.06      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 19.42/3.06      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
% 19.42/3.06      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 19.42/3.06      inference(predicate_to_equality,[status(thm)],[c_401]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_1409,plain,
% 19.42/3.06      ( k1_relset_1(k1_xboole_0,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) != k1_xboole_0
% 19.42/3.06      | sK2 != k1_xboole_0
% 19.42/3.06      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 19.42/3.06      | m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 19.42/3.06      | v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) != iProver_top ),
% 19.42/3.06      inference(demodulation,[status(thm)],[c_1214,c_3]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_1975,plain,
% 19.42/3.06      ( k1_relset_1(k1_xboole_0,sK1,k7_relat_1(sK3,sK2)) != k1_xboole_0
% 19.42/3.06      | sK2 != k1_xboole_0
% 19.42/3.06      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 19.42/3.06      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 19.42/3.06      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 19.42/3.06      inference(demodulation,[status(thm)],[c_1409,c_1840]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_89768,plain,
% 19.42/3.06      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,sK2)) != k1_xboole_0
% 19.42/3.06      | sK2 != k1_xboole_0
% 19.42/3.06      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_xboole_0))) != iProver_top
% 19.42/3.06      | m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 19.42/3.06      | v1_funct_1(k7_relat_1(sK3,sK2)) != iProver_top ),
% 19.42/3.06      inference(demodulation,[status(thm)],[c_89465,c_1975]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_89769,plain,
% 19.42/3.06      ( sK2 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 19.42/3.06      inference(demodulation,[status(thm)],[c_89465,c_1971]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_89803,plain,
% 19.42/3.06      ( sK2 = k1_xboole_0 ),
% 19.42/3.06      inference(equality_resolution_simp,[status(thm)],[c_89769]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_89814,plain,
% 19.42/3.06      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0
% 19.42/3.06      | k1_xboole_0 != k1_xboole_0
% 19.42/3.06      | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 19.42/3.06      | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 19.42/3.06      | v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
% 19.42/3.06      inference(light_normalisation,[status(thm)],[c_89768,c_89803]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_89815,plain,
% 19.42/3.06      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0
% 19.42/3.06      | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 19.42/3.06      | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 19.42/3.06      | v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
% 19.42/3.06      inference(equality_resolution_simp,[status(thm)],[c_89814]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_89820,plain,
% 19.42/3.06      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0
% 19.42/3.06      | m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 19.42/3.06      | v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
% 19.42/3.06      inference(demodulation,[status(thm)],[c_89815,c_3]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_89833,plain,
% 19.42/3.06      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0
% 19.42/3.06      | v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
% 19.42/3.06      inference(backward_subsumption_resolution,
% 19.42/3.06                [status(thm)],
% 19.42/3.06                [c_89830,c_89820]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_89844,plain,
% 19.42/3.06      ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != k1_xboole_0
% 19.42/3.06      | v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
% 19.42/3.06      inference(demodulation,[status(thm)],[c_89842,c_89833]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_3480,plain,
% 19.42/3.06      ( k1_relat_1(X0) = k1_xboole_0
% 19.42/3.06      | v4_relat_1(X0,k1_xboole_0) != iProver_top
% 19.42/3.06      | v1_relat_1(X0) != iProver_top ),
% 19.42/3.06      inference(superposition,[status(thm)],[c_1235,c_1238]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_8137,plain,
% 19.42/3.06      ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0
% 19.42/3.06      | v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
% 19.42/3.06      inference(superposition,[status(thm)],[c_4855,c_3480]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_3034,plain,
% 19.42/3.06      ( v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = iProver_top
% 19.42/3.06      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top ),
% 19.42/3.06      inference(instantiation,[status(thm)],[c_3012]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_8662,plain,
% 19.42/3.06      ( k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
% 19.42/3.06      inference(global_propositional_subsumption,
% 19.42/3.06                [status(thm)],
% 19.42/3.06                [c_8137,c_2126,c_3034]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_89848,plain,
% 19.42/3.06      ( k1_xboole_0 != k1_xboole_0
% 19.42/3.06      | v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
% 19.42/3.06      inference(light_normalisation,[status(thm)],[c_89844,c_8662]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_89849,plain,
% 19.42/3.06      ( v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) != iProver_top ),
% 19.42/3.06      inference(equality_resolution_simp,[status(thm)],[c_89848]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(c_2123,plain,
% 19.42/3.06      ( v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) = iProver_top
% 19.42/3.06      | v1_funct_1(sK3) != iProver_top ),
% 19.42/3.06      inference(instantiation,[status(thm)],[c_2115]) ).
% 19.42/3.06  
% 19.42/3.06  cnf(contradiction,plain,
% 19.42/3.06      ( $false ),
% 19.42/3.06      inference(minisat,[status(thm)],[c_89849,c_2123,c_35]) ).
% 19.42/3.06  
% 19.42/3.06  
% 19.42/3.06  % SZS output end CNFRefutation for theBenchmark.p
% 19.42/3.06  
% 19.42/3.06  ------                               Statistics
% 19.42/3.06  
% 19.42/3.06  ------ General
% 19.42/3.06  
% 19.42/3.06  abstr_ref_over_cycles:                  0
% 19.42/3.06  abstr_ref_under_cycles:                 0
% 19.42/3.06  gc_basic_clause_elim:                   0
% 19.42/3.06  forced_gc_time:                         0
% 19.42/3.06  parsing_time:                           0.016
% 19.42/3.06  unif_index_cands_time:                  0.
% 19.42/3.06  unif_index_add_time:                    0.
% 19.42/3.06  orderings_time:                         0.
% 19.42/3.06  out_proof_time:                         0.027
% 19.42/3.06  total_time:                             2.355
% 19.42/3.06  num_of_symbols:                         48
% 19.42/3.06  num_of_terms:                           61514
% 19.42/3.06  
% 19.42/3.06  ------ Preprocessing
% 19.42/3.06  
% 19.42/3.06  num_of_splits:                          0
% 19.42/3.06  num_of_split_atoms:                     0
% 19.42/3.06  num_of_reused_defs:                     0
% 19.42/3.06  num_eq_ax_congr_red:                    11
% 19.42/3.06  num_of_sem_filtered_clauses:            1
% 19.42/3.06  num_of_subtypes:                        0
% 19.42/3.06  monotx_restored_types:                  0
% 19.42/3.06  sat_num_of_epr_types:                   0
% 19.42/3.06  sat_num_of_non_cyclic_types:            0
% 19.42/3.06  sat_guarded_non_collapsed_types:        0
% 19.42/3.06  num_pure_diseq_elim:                    0
% 19.42/3.06  simp_replaced_by:                       0
% 19.42/3.06  res_preprocessed:                       162
% 19.42/3.06  prep_upred:                             0
% 19.42/3.06  prep_unflattend:                        33
% 19.42/3.06  smt_new_axioms:                         0
% 19.42/3.06  pred_elim_cands:                        5
% 19.42/3.06  pred_elim:                              1
% 19.42/3.06  pred_elim_cl:                           1
% 19.42/3.06  pred_elim_cycles:                       3
% 19.42/3.06  merged_defs:                            0
% 19.42/3.06  merged_defs_ncl:                        0
% 19.42/3.06  bin_hyper_res:                          0
% 19.42/3.06  prep_cycles:                            4
% 19.42/3.06  pred_elim_time:                         0.003
% 19.42/3.06  splitting_time:                         0.
% 19.42/3.06  sem_filter_time:                        0.
% 19.42/3.06  monotx_time:                            0.
% 19.42/3.06  subtype_inf_time:                       0.
% 19.42/3.06  
% 19.42/3.06  ------ Problem properties
% 19.42/3.06  
% 19.42/3.06  clauses:                                34
% 19.42/3.06  conjectures:                            4
% 19.42/3.06  epr:                                    5
% 19.42/3.06  horn:                                   31
% 19.42/3.06  ground:                                 11
% 19.42/3.06  unary:                                  6
% 19.42/3.06  binary:                                 7
% 19.42/3.06  lits:                                   91
% 19.42/3.06  lits_eq:                                28
% 19.42/3.06  fd_pure:                                0
% 19.42/3.06  fd_pseudo:                              0
% 19.42/3.06  fd_cond:                                2
% 19.42/3.06  fd_pseudo_cond:                         0
% 19.42/3.06  ac_symbols:                             0
% 19.42/3.06  
% 19.42/3.06  ------ Propositional Solver
% 19.42/3.06  
% 19.42/3.06  prop_solver_calls:                      43
% 19.42/3.06  prop_fast_solver_calls:                 4357
% 19.42/3.06  smt_solver_calls:                       0
% 19.42/3.06  smt_fast_solver_calls:                  0
% 19.42/3.06  prop_num_of_clauses:                    29830
% 19.42/3.06  prop_preprocess_simplified:             45421
% 19.42/3.06  prop_fo_subsumed:                       254
% 19.42/3.06  prop_solver_time:                       0.
% 19.42/3.06  smt_solver_time:                        0.
% 19.42/3.06  smt_fast_solver_time:                   0.
% 19.42/3.06  prop_fast_solver_time:                  0.
% 19.42/3.06  prop_unsat_core_time:                   0.003
% 19.42/3.06  
% 19.42/3.06  ------ QBF
% 19.42/3.06  
% 19.42/3.06  qbf_q_res:                              0
% 19.42/3.06  qbf_num_tautologies:                    0
% 19.42/3.06  qbf_prep_cycles:                        0
% 19.42/3.06  
% 19.42/3.06  ------ BMC1
% 19.42/3.06  
% 19.42/3.06  bmc1_current_bound:                     -1
% 19.42/3.06  bmc1_last_solved_bound:                 -1
% 19.42/3.06  bmc1_unsat_core_size:                   -1
% 19.42/3.06  bmc1_unsat_core_parents_size:           -1
% 19.42/3.06  bmc1_merge_next_fun:                    0
% 19.42/3.06  bmc1_unsat_core_clauses_time:           0.
% 19.42/3.06  
% 19.42/3.06  ------ Instantiation
% 19.42/3.06  
% 19.42/3.06  inst_num_of_clauses:                    1980
% 19.42/3.06  inst_num_in_passive:                    642
% 19.42/3.06  inst_num_in_active:                     3752
% 19.42/3.06  inst_num_in_unprocessed:                398
% 19.42/3.06  inst_num_of_loops:                      3949
% 19.42/3.06  inst_num_of_learning_restarts:          1
% 19.42/3.06  inst_num_moves_active_passive:          188
% 19.42/3.06  inst_lit_activity:                      0
% 19.42/3.06  inst_lit_activity_moves:                0
% 19.42/3.06  inst_num_tautologies:                   0
% 19.42/3.06  inst_num_prop_implied:                  0
% 19.42/3.06  inst_num_existing_simplified:           0
% 19.42/3.06  inst_num_eq_res_simplified:             0
% 19.42/3.06  inst_num_child_elim:                    0
% 19.42/3.06  inst_num_of_dismatching_blockings:      3842
% 19.42/3.06  inst_num_of_non_proper_insts:           8759
% 19.42/3.06  inst_num_of_duplicates:                 0
% 19.42/3.06  inst_inst_num_from_inst_to_res:         0
% 19.42/3.06  inst_dismatching_checking_time:         0.
% 19.42/3.06  
% 19.42/3.06  ------ Resolution
% 19.42/3.06  
% 19.42/3.06  res_num_of_clauses:                     46
% 19.42/3.06  res_num_in_passive:                     46
% 19.42/3.06  res_num_in_active:                      0
% 19.42/3.06  res_num_of_loops:                       166
% 19.42/3.06  res_forward_subset_subsumed:            217
% 19.42/3.06  res_backward_subset_subsumed:           4
% 19.42/3.06  res_forward_subsumed:                   0
% 19.42/3.06  res_backward_subsumed:                  0
% 19.42/3.06  res_forward_subsumption_resolution:     0
% 19.42/3.06  res_backward_subsumption_resolution:    0
% 19.42/3.06  res_clause_to_clause_subsumption:       14738
% 19.42/3.06  res_orphan_elimination:                 0
% 19.42/3.06  res_tautology_del:                      494
% 19.42/3.06  res_num_eq_res_simplified:              1
% 19.42/3.06  res_num_sel_changes:                    0
% 19.42/3.06  res_moves_from_active_to_pass:          0
% 19.42/3.06  
% 19.42/3.06  ------ Superposition
% 19.42/3.06  
% 19.42/3.06  sup_time_total:                         0.
% 19.42/3.06  sup_time_generating:                    0.
% 19.42/3.06  sup_time_sim_full:                      0.
% 19.42/3.06  sup_time_sim_immed:                     0.
% 19.42/3.06  
% 19.42/3.06  sup_num_of_clauses:                     2647
% 19.42/3.06  sup_num_in_active:                      434
% 19.42/3.06  sup_num_in_passive:                     2213
% 19.42/3.06  sup_num_of_loops:                       788
% 19.42/3.06  sup_fw_superposition:                   2901
% 19.42/3.06  sup_bw_superposition:                   2137
% 19.42/3.06  sup_immediate_simplified:               1601
% 19.42/3.06  sup_given_eliminated:                   0
% 19.42/3.06  comparisons_done:                       0
% 19.42/3.06  comparisons_avoided:                    102
% 19.42/3.06  
% 19.42/3.06  ------ Simplifications
% 19.42/3.06  
% 19.42/3.06  
% 19.42/3.06  sim_fw_subset_subsumed:                 372
% 19.42/3.06  sim_bw_subset_subsumed:                 218
% 19.42/3.06  sim_fw_subsumed:                        622
% 19.42/3.06  sim_bw_subsumed:                        172
% 19.42/3.06  sim_fw_subsumption_res:                 107
% 19.42/3.06  sim_bw_subsumption_res:                 2
% 19.42/3.06  sim_tautology_del:                      89
% 19.42/3.06  sim_eq_tautology_del:                   95
% 19.42/3.06  sim_eq_res_simp:                        7
% 19.42/3.06  sim_fw_demodulated:                     121
% 19.42/3.06  sim_bw_demodulated:                     314
% 19.42/3.06  sim_light_normalised:                   466
% 19.42/3.06  sim_joinable_taut:                      0
% 19.42/3.06  sim_joinable_simp:                      0
% 19.42/3.06  sim_ac_normalised:                      0
% 19.42/3.06  sim_smt_subsumption:                    0
% 19.42/3.06  
%------------------------------------------------------------------------------
