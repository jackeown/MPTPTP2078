%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:05:15 EST 2020

% Result     : Theorem 3.20s
% Output     : CNFRefutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :  160 (2990 expanded)
%              Number of clauses        :   78 ( 379 expanded)
%              Number of leaves         :   24 ( 843 expanded)
%              Depth                    :   22
%              Number of atoms          :  392 (6614 expanded)
%              Number of equality atoms :  229 (3863 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f38,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f39,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f44,plain,
    ( ? [X0,X1,X2] :
        ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( k1_tarski(k1_funct_1(sK2,sK0)) != k2_relset_1(k1_tarski(sK0),sK1,sK2)
      & k1_xboole_0 != sK1
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
      & v1_funct_2(sK2,k1_tarski(sK0),sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( k1_tarski(k1_funct_1(sK2,sK0)) != k2_relset_1(k1_tarski(sK0),sK1,sK2)
    & k1_xboole_0 != sK1
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_2(sK2,k1_tarski(sK0),sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f39,f44])).

fof(f76,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f45])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f79,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f53,f54])).

fof(f80,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f52,f79])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f51,f80])).

fof(f82,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f50,f81])).

fof(f83,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f49,f82])).

fof(f84,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f48,f83])).

fof(f92,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f76,f84])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k8_relset_1(X0,X1,X2,X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f75,plain,(
    v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f93,plain,(
    v1_funct_2(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f75,f84])).

fof(f74,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f77,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f45])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f12,axiom,(
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
    inference(ennf_transformation,[],[f12])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f40])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = X0
      | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = X0
      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f55,f83,f84,f84,f83])).

fof(f78,plain,(
    k1_tarski(k1_funct_1(sK2,sK0)) != k2_relset_1(k1_tarski(sK0),sK1,sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f91,plain,(
    k6_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK2) ),
    inference(definition_unfolding,[],[f78,f84,f84])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k6_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f66,f84,f84])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f64,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f42])).

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

fof(f47,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1558,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1559,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2347,plain,
    ( k8_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_1558,c_1559])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k8_relset_1(X1,X2,X0,X2) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_362,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != X1
    | k8_relset_1(X1,X2,X0,X2) = X1
    | sK1 != X2
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_24])).

cnf(c_363,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)))
    | ~ v1_funct_1(sK2)
    | k8_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK2,sK1) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_362])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_22,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_365,plain,
    ( k8_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK2,sK1) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_363,c_25,c_23,c_22])).

cnf(c_2528,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k10_relat_1(sK2,sK1) ),
    inference(demodulation,[status(thm)],[c_2347,c_365])).

cnf(c_15,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_10,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_324,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_15,c_10])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_328,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_324,c_14])).

cnf(c_329,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_328])).

cnf(c_1557,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_329])).

cnf(c_1881,plain,
    ( r1_tarski(k1_relat_1(sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1558,c_1557])).

cnf(c_2582,plain,
    ( r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2528,c_1881])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = X0
    | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = X0
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1567,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = X2
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X2
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X2
    | k1_xboole_0 = X2
    | r1_tarski(X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2702,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = X0
    | k1_xboole_0 = X0
    | r1_tarski(X0,k10_relat_1(sK2,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2528,c_1567])).

cnf(c_2703,plain,
    ( k10_relat_1(sK2,sK1) = X0
    | k1_xboole_0 = X0
    | r1_tarski(X0,k10_relat_1(sK2,sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2702,c_2528])).

cnf(c_3041,plain,
    ( k10_relat_1(sK2,sK1) = k1_relat_1(sK2)
    | k1_relat_1(sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2582,c_2703])).

cnf(c_21,negated_conjecture,
    ( k6_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK2) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1095,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1595,plain,
    ( k6_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != X0
    | k6_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK2)
    | k2_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK2) != X0 ),
    inference(instantiation,[status(thm)],[c_1095])).

cnf(c_1647,plain,
    ( k6_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK2)
    | k6_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relat_1(sK2)
    | k2_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK2) != k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1595])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1707,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)))
    | k2_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK2) = k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_13,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k1_relat_1(X0)
    | k6_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_375,plain,
    ( ~ v1_relat_1(X0)
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k1_relat_1(X0)
    | k6_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_25])).

cnf(c_376,plain,
    ( ~ v1_relat_1(sK2)
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_relat_1(sK2)
    | k6_enumset1(k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_375])).

cnf(c_1555,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_relat_1(sK2)
    | k6_enumset1(k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0)) = k2_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_376])).

cnf(c_28,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_377,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_relat_1(sK2)
    | k6_enumset1(k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0)) = k2_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_376])).

cnf(c_1659,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1725,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1659])).

cnf(c_1726,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1725])).

cnf(c_1790,plain,
    ( k6_enumset1(k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0)) = k2_relat_1(sK2)
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1555,c_28,c_377,c_1726])).

cnf(c_1791,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_relat_1(sK2)
    | k6_enumset1(k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0)) = k2_relat_1(sK2) ),
    inference(renaming,[status(thm)],[c_1790])).

cnf(c_2593,plain,
    ( k6_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2)
    | k10_relat_1(sK2,sK1) != k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2528,c_1791])).

cnf(c_3260,plain,
    ( k1_relat_1(sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3041,c_23,c_21,c_1647,c_1707,c_2593])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1563,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3266,plain,
    ( sK2 = k1_xboole_0
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3260,c_1563])).

cnf(c_1094,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1769,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1094])).

cnf(c_1687,plain,
    ( X0 != X1
    | sK2 != X1
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_1095])).

cnf(c_1785,plain,
    ( X0 != sK2
    | sK2 = X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1687])).

cnf(c_2003,plain,
    ( sK2 != sK2
    | sK2 = k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_1785])).

cnf(c_2118,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) != k1_xboole_0
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_3743,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3266,c_23,c_21,c_1647,c_1707,c_1725,c_1769,c_2003,c_2118,c_2593,c_3041])).

cnf(c_3037,plain,
    ( k10_relat_1(sK2,sK1) != k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2593,c_23,c_21,c_1647,c_1707])).

cnf(c_3262,plain,
    ( k10_relat_1(sK2,sK1) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3260,c_3037])).

cnf(c_3750,plain,
    ( k10_relat_1(k1_xboole_0,sK1) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3743,c_3262])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1573,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1566,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2345,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1566,c_1559])).

cnf(c_4612,plain,
    ( k8_relset_1(X0,X1,k1_xboole_0,X2) = k10_relat_1(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_1573,c_2345])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1561,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1565,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2291,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k8_relset_1(X1,X2,X0,X3),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1561,c_1565])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1572,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3100,plain,
    ( k8_relset_1(k1_xboole_0,X0,X1,X2) = k1_xboole_0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2291,c_1572])).

cnf(c_3252,plain,
    ( k8_relset_1(k1_xboole_0,X0,X1,X2) = k1_xboole_0
    | r1_tarski(X1,k2_zfmisc_1(k1_xboole_0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1566,c_3100])).

cnf(c_3790,plain,
    ( k8_relset_1(k1_xboole_0,X0,k1_xboole_0,X1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1573,c_3252])).

cnf(c_4724,plain,
    ( k10_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4612,c_3790])).

cnf(c_5131,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3750,c_4724])).

cnf(c_5132,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_5131])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:43:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.20/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.20/0.98  
% 3.20/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.20/0.98  
% 3.20/0.98  ------  iProver source info
% 3.20/0.98  
% 3.20/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.20/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.20/0.98  git: non_committed_changes: false
% 3.20/0.98  git: last_make_outside_of_git: false
% 3.20/0.98  
% 3.20/0.98  ------ 
% 3.20/0.98  
% 3.20/0.98  ------ Input Options
% 3.20/0.98  
% 3.20/0.98  --out_options                           all
% 3.20/0.98  --tptp_safe_out                         true
% 3.20/0.98  --problem_path                          ""
% 3.20/0.98  --include_path                          ""
% 3.20/0.98  --clausifier                            res/vclausify_rel
% 3.20/0.98  --clausifier_options                    ""
% 3.20/0.98  --stdin                                 false
% 3.20/0.98  --stats_out                             all
% 3.20/0.98  
% 3.20/0.98  ------ General Options
% 3.20/0.98  
% 3.20/0.98  --fof                                   false
% 3.20/0.98  --time_out_real                         305.
% 3.20/0.98  --time_out_virtual                      -1.
% 3.20/0.98  --symbol_type_check                     false
% 3.20/0.98  --clausify_out                          false
% 3.20/0.98  --sig_cnt_out                           false
% 3.20/0.98  --trig_cnt_out                          false
% 3.20/0.98  --trig_cnt_out_tolerance                1.
% 3.20/0.98  --trig_cnt_out_sk_spl                   false
% 3.20/0.98  --abstr_cl_out                          false
% 3.20/0.98  
% 3.20/0.98  ------ Global Options
% 3.20/0.98  
% 3.20/0.98  --schedule                              default
% 3.20/0.98  --add_important_lit                     false
% 3.20/0.98  --prop_solver_per_cl                    1000
% 3.20/0.98  --min_unsat_core                        false
% 3.20/0.98  --soft_assumptions                      false
% 3.20/0.98  --soft_lemma_size                       3
% 3.20/0.98  --prop_impl_unit_size                   0
% 3.20/0.98  --prop_impl_unit                        []
% 3.20/0.98  --share_sel_clauses                     true
% 3.20/0.98  --reset_solvers                         false
% 3.20/0.98  --bc_imp_inh                            [conj_cone]
% 3.20/0.98  --conj_cone_tolerance                   3.
% 3.20/0.98  --extra_neg_conj                        none
% 3.20/0.98  --large_theory_mode                     true
% 3.20/0.98  --prolific_symb_bound                   200
% 3.20/0.98  --lt_threshold                          2000
% 3.20/0.98  --clause_weak_htbl                      true
% 3.20/0.98  --gc_record_bc_elim                     false
% 3.20/0.98  
% 3.20/0.98  ------ Preprocessing Options
% 3.20/0.98  
% 3.20/0.98  --preprocessing_flag                    true
% 3.20/0.98  --time_out_prep_mult                    0.1
% 3.20/0.98  --splitting_mode                        input
% 3.20/0.98  --splitting_grd                         true
% 3.20/0.98  --splitting_cvd                         false
% 3.20/0.98  --splitting_cvd_svl                     false
% 3.20/0.98  --splitting_nvd                         32
% 3.20/0.98  --sub_typing                            true
% 3.20/0.98  --prep_gs_sim                           true
% 3.20/0.98  --prep_unflatten                        true
% 3.20/0.98  --prep_res_sim                          true
% 3.20/0.98  --prep_upred                            true
% 3.20/0.98  --prep_sem_filter                       exhaustive
% 3.20/0.98  --prep_sem_filter_out                   false
% 3.20/0.98  --pred_elim                             true
% 3.20/0.98  --res_sim_input                         true
% 3.20/0.98  --eq_ax_congr_red                       true
% 3.20/0.98  --pure_diseq_elim                       true
% 3.20/0.98  --brand_transform                       false
% 3.20/0.98  --non_eq_to_eq                          false
% 3.20/0.98  --prep_def_merge                        true
% 3.20/0.98  --prep_def_merge_prop_impl              false
% 3.20/0.99  --prep_def_merge_mbd                    true
% 3.20/0.99  --prep_def_merge_tr_red                 false
% 3.20/0.99  --prep_def_merge_tr_cl                  false
% 3.20/0.99  --smt_preprocessing                     true
% 3.20/0.99  --smt_ac_axioms                         fast
% 3.20/0.99  --preprocessed_out                      false
% 3.20/0.99  --preprocessed_stats                    false
% 3.20/0.99  
% 3.20/0.99  ------ Abstraction refinement Options
% 3.20/0.99  
% 3.20/0.99  --abstr_ref                             []
% 3.20/0.99  --abstr_ref_prep                        false
% 3.20/0.99  --abstr_ref_until_sat                   false
% 3.20/0.99  --abstr_ref_sig_restrict                funpre
% 3.20/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.20/0.99  --abstr_ref_under                       []
% 3.20/0.99  
% 3.20/0.99  ------ SAT Options
% 3.20/0.99  
% 3.20/0.99  --sat_mode                              false
% 3.20/0.99  --sat_fm_restart_options                ""
% 3.20/0.99  --sat_gr_def                            false
% 3.20/0.99  --sat_epr_types                         true
% 3.20/0.99  --sat_non_cyclic_types                  false
% 3.20/0.99  --sat_finite_models                     false
% 3.20/0.99  --sat_fm_lemmas                         false
% 3.20/0.99  --sat_fm_prep                           false
% 3.20/0.99  --sat_fm_uc_incr                        true
% 3.20/0.99  --sat_out_model                         small
% 3.20/0.99  --sat_out_clauses                       false
% 3.20/0.99  
% 3.20/0.99  ------ QBF Options
% 3.20/0.99  
% 3.20/0.99  --qbf_mode                              false
% 3.20/0.99  --qbf_elim_univ                         false
% 3.20/0.99  --qbf_dom_inst                          none
% 3.20/0.99  --qbf_dom_pre_inst                      false
% 3.20/0.99  --qbf_sk_in                             false
% 3.20/0.99  --qbf_pred_elim                         true
% 3.20/0.99  --qbf_split                             512
% 3.20/0.99  
% 3.20/0.99  ------ BMC1 Options
% 3.20/0.99  
% 3.20/0.99  --bmc1_incremental                      false
% 3.20/0.99  --bmc1_axioms                           reachable_all
% 3.20/0.99  --bmc1_min_bound                        0
% 3.20/0.99  --bmc1_max_bound                        -1
% 3.20/0.99  --bmc1_max_bound_default                -1
% 3.20/0.99  --bmc1_symbol_reachability              true
% 3.20/0.99  --bmc1_property_lemmas                  false
% 3.20/0.99  --bmc1_k_induction                      false
% 3.20/0.99  --bmc1_non_equiv_states                 false
% 3.20/0.99  --bmc1_deadlock                         false
% 3.20/0.99  --bmc1_ucm                              false
% 3.20/0.99  --bmc1_add_unsat_core                   none
% 3.20/0.99  --bmc1_unsat_core_children              false
% 3.20/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.20/0.99  --bmc1_out_stat                         full
% 3.20/0.99  --bmc1_ground_init                      false
% 3.20/0.99  --bmc1_pre_inst_next_state              false
% 3.20/0.99  --bmc1_pre_inst_state                   false
% 3.20/0.99  --bmc1_pre_inst_reach_state             false
% 3.20/0.99  --bmc1_out_unsat_core                   false
% 3.20/0.99  --bmc1_aig_witness_out                  false
% 3.20/0.99  --bmc1_verbose                          false
% 3.20/0.99  --bmc1_dump_clauses_tptp                false
% 3.20/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.20/0.99  --bmc1_dump_file                        -
% 3.20/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.20/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.20/0.99  --bmc1_ucm_extend_mode                  1
% 3.20/0.99  --bmc1_ucm_init_mode                    2
% 3.20/0.99  --bmc1_ucm_cone_mode                    none
% 3.20/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.20/0.99  --bmc1_ucm_relax_model                  4
% 3.20/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.20/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.20/0.99  --bmc1_ucm_layered_model                none
% 3.20/0.99  --bmc1_ucm_max_lemma_size               10
% 3.20/0.99  
% 3.20/0.99  ------ AIG Options
% 3.20/0.99  
% 3.20/0.99  --aig_mode                              false
% 3.20/0.99  
% 3.20/0.99  ------ Instantiation Options
% 3.20/0.99  
% 3.20/0.99  --instantiation_flag                    true
% 3.20/0.99  --inst_sos_flag                         true
% 3.20/0.99  --inst_sos_phase                        true
% 3.20/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.20/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.20/0.99  --inst_lit_sel_side                     num_symb
% 3.20/0.99  --inst_solver_per_active                1400
% 3.20/0.99  --inst_solver_calls_frac                1.
% 3.20/0.99  --inst_passive_queue_type               priority_queues
% 3.20/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.20/0.99  --inst_passive_queues_freq              [25;2]
% 3.20/0.99  --inst_dismatching                      true
% 3.20/0.99  --inst_eager_unprocessed_to_passive     true
% 3.20/0.99  --inst_prop_sim_given                   true
% 3.20/0.99  --inst_prop_sim_new                     false
% 3.20/0.99  --inst_subs_new                         false
% 3.20/0.99  --inst_eq_res_simp                      false
% 3.20/0.99  --inst_subs_given                       false
% 3.20/0.99  --inst_orphan_elimination               true
% 3.20/0.99  --inst_learning_loop_flag               true
% 3.20/0.99  --inst_learning_start                   3000
% 3.20/0.99  --inst_learning_factor                  2
% 3.20/0.99  --inst_start_prop_sim_after_learn       3
% 3.20/0.99  --inst_sel_renew                        solver
% 3.20/0.99  --inst_lit_activity_flag                true
% 3.20/0.99  --inst_restr_to_given                   false
% 3.20/0.99  --inst_activity_threshold               500
% 3.20/0.99  --inst_out_proof                        true
% 3.20/0.99  
% 3.20/0.99  ------ Resolution Options
% 3.20/0.99  
% 3.20/0.99  --resolution_flag                       true
% 3.20/0.99  --res_lit_sel                           adaptive
% 3.20/0.99  --res_lit_sel_side                      none
% 3.20/0.99  --res_ordering                          kbo
% 3.20/0.99  --res_to_prop_solver                    active
% 3.20/0.99  --res_prop_simpl_new                    false
% 3.20/0.99  --res_prop_simpl_given                  true
% 3.20/0.99  --res_passive_queue_type                priority_queues
% 3.20/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.20/0.99  --res_passive_queues_freq               [15;5]
% 3.20/0.99  --res_forward_subs                      full
% 3.20/0.99  --res_backward_subs                     full
% 3.20/0.99  --res_forward_subs_resolution           true
% 3.20/0.99  --res_backward_subs_resolution          true
% 3.20/0.99  --res_orphan_elimination                true
% 3.20/0.99  --res_time_limit                        2.
% 3.20/0.99  --res_out_proof                         true
% 3.20/0.99  
% 3.20/0.99  ------ Superposition Options
% 3.20/0.99  
% 3.20/0.99  --superposition_flag                    true
% 3.20/0.99  --sup_passive_queue_type                priority_queues
% 3.20/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.20/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.20/0.99  --demod_completeness_check              fast
% 3.20/0.99  --demod_use_ground                      true
% 3.20/0.99  --sup_to_prop_solver                    passive
% 3.20/0.99  --sup_prop_simpl_new                    true
% 3.20/0.99  --sup_prop_simpl_given                  true
% 3.20/0.99  --sup_fun_splitting                     true
% 3.20/0.99  --sup_smt_interval                      50000
% 3.20/0.99  
% 3.20/0.99  ------ Superposition Simplification Setup
% 3.20/0.99  
% 3.20/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.20/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.20/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.20/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.20/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.20/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.20/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.20/0.99  --sup_immed_triv                        [TrivRules]
% 3.20/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.20/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.20/0.99  --sup_immed_bw_main                     []
% 3.20/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.20/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.20/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.20/0.99  --sup_input_bw                          []
% 3.20/0.99  
% 3.20/0.99  ------ Combination Options
% 3.20/0.99  
% 3.20/0.99  --comb_res_mult                         3
% 3.20/0.99  --comb_sup_mult                         2
% 3.20/0.99  --comb_inst_mult                        10
% 3.20/0.99  
% 3.20/0.99  ------ Debug Options
% 3.20/0.99  
% 3.20/0.99  --dbg_backtrace                         false
% 3.20/0.99  --dbg_dump_prop_clauses                 false
% 3.20/0.99  --dbg_dump_prop_clauses_file            -
% 3.20/0.99  --dbg_out_stat                          false
% 3.20/0.99  ------ Parsing...
% 3.20/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.20/0.99  
% 3.20/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.20/0.99  
% 3.20/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.20/0.99  
% 3.20/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.20/0.99  ------ Proving...
% 3.20/0.99  ------ Problem Properties 
% 3.20/0.99  
% 3.20/0.99  
% 3.20/0.99  clauses                                 22
% 3.20/0.99  conjectures                             3
% 3.20/0.99  EPR                                     3
% 3.20/0.99  Horn                                    21
% 3.20/0.99  unary                                   9
% 3.20/0.99  binary                                  8
% 3.20/0.99  lits                                    42
% 3.20/0.99  lits eq                                 18
% 3.20/0.99  fd_pure                                 0
% 3.20/0.99  fd_pseudo                               0
% 3.20/0.99  fd_cond                                 3
% 3.20/0.99  fd_pseudo_cond                          1
% 3.20/0.99  AC symbols                              0
% 3.20/0.99  
% 3.20/0.99  ------ Schedule dynamic 5 is on 
% 3.20/0.99  
% 3.20/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.20/0.99  
% 3.20/0.99  
% 3.20/0.99  ------ 
% 3.20/0.99  Current options:
% 3.20/0.99  ------ 
% 3.20/0.99  
% 3.20/0.99  ------ Input Options
% 3.20/0.99  
% 3.20/0.99  --out_options                           all
% 3.20/0.99  --tptp_safe_out                         true
% 3.20/0.99  --problem_path                          ""
% 3.20/0.99  --include_path                          ""
% 3.20/0.99  --clausifier                            res/vclausify_rel
% 3.20/0.99  --clausifier_options                    ""
% 3.20/0.99  --stdin                                 false
% 3.20/0.99  --stats_out                             all
% 3.20/0.99  
% 3.20/0.99  ------ General Options
% 3.20/0.99  
% 3.20/0.99  --fof                                   false
% 3.20/0.99  --time_out_real                         305.
% 3.20/0.99  --time_out_virtual                      -1.
% 3.20/0.99  --symbol_type_check                     false
% 3.20/0.99  --clausify_out                          false
% 3.20/0.99  --sig_cnt_out                           false
% 3.20/0.99  --trig_cnt_out                          false
% 3.20/0.99  --trig_cnt_out_tolerance                1.
% 3.20/0.99  --trig_cnt_out_sk_spl                   false
% 3.20/0.99  --abstr_cl_out                          false
% 3.20/0.99  
% 3.20/0.99  ------ Global Options
% 3.20/0.99  
% 3.20/0.99  --schedule                              default
% 3.20/0.99  --add_important_lit                     false
% 3.20/0.99  --prop_solver_per_cl                    1000
% 3.20/0.99  --min_unsat_core                        false
% 3.20/0.99  --soft_assumptions                      false
% 3.20/0.99  --soft_lemma_size                       3
% 3.20/0.99  --prop_impl_unit_size                   0
% 3.20/0.99  --prop_impl_unit                        []
% 3.20/0.99  --share_sel_clauses                     true
% 3.20/0.99  --reset_solvers                         false
% 3.20/0.99  --bc_imp_inh                            [conj_cone]
% 3.20/0.99  --conj_cone_tolerance                   3.
% 3.20/0.99  --extra_neg_conj                        none
% 3.20/0.99  --large_theory_mode                     true
% 3.20/0.99  --prolific_symb_bound                   200
% 3.20/0.99  --lt_threshold                          2000
% 3.20/0.99  --clause_weak_htbl                      true
% 3.20/0.99  --gc_record_bc_elim                     false
% 3.20/0.99  
% 3.20/0.99  ------ Preprocessing Options
% 3.20/0.99  
% 3.20/0.99  --preprocessing_flag                    true
% 3.20/0.99  --time_out_prep_mult                    0.1
% 3.20/0.99  --splitting_mode                        input
% 3.20/0.99  --splitting_grd                         true
% 3.20/0.99  --splitting_cvd                         false
% 3.20/0.99  --splitting_cvd_svl                     false
% 3.20/0.99  --splitting_nvd                         32
% 3.20/0.99  --sub_typing                            true
% 3.20/0.99  --prep_gs_sim                           true
% 3.20/0.99  --prep_unflatten                        true
% 3.20/0.99  --prep_res_sim                          true
% 3.20/0.99  --prep_upred                            true
% 3.20/0.99  --prep_sem_filter                       exhaustive
% 3.20/0.99  --prep_sem_filter_out                   false
% 3.20/0.99  --pred_elim                             true
% 3.20/0.99  --res_sim_input                         true
% 3.20/0.99  --eq_ax_congr_red                       true
% 3.20/0.99  --pure_diseq_elim                       true
% 3.20/0.99  --brand_transform                       false
% 3.20/0.99  --non_eq_to_eq                          false
% 3.20/0.99  --prep_def_merge                        true
% 3.20/0.99  --prep_def_merge_prop_impl              false
% 3.20/0.99  --prep_def_merge_mbd                    true
% 3.20/0.99  --prep_def_merge_tr_red                 false
% 3.20/0.99  --prep_def_merge_tr_cl                  false
% 3.20/0.99  --smt_preprocessing                     true
% 3.20/0.99  --smt_ac_axioms                         fast
% 3.20/0.99  --preprocessed_out                      false
% 3.20/0.99  --preprocessed_stats                    false
% 3.20/0.99  
% 3.20/0.99  ------ Abstraction refinement Options
% 3.20/0.99  
% 3.20/0.99  --abstr_ref                             []
% 3.20/0.99  --abstr_ref_prep                        false
% 3.20/0.99  --abstr_ref_until_sat                   false
% 3.20/0.99  --abstr_ref_sig_restrict                funpre
% 3.20/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.20/0.99  --abstr_ref_under                       []
% 3.20/0.99  
% 3.20/0.99  ------ SAT Options
% 3.20/0.99  
% 3.20/0.99  --sat_mode                              false
% 3.20/0.99  --sat_fm_restart_options                ""
% 3.20/0.99  --sat_gr_def                            false
% 3.20/0.99  --sat_epr_types                         true
% 3.20/0.99  --sat_non_cyclic_types                  false
% 3.20/0.99  --sat_finite_models                     false
% 3.20/0.99  --sat_fm_lemmas                         false
% 3.20/0.99  --sat_fm_prep                           false
% 3.20/0.99  --sat_fm_uc_incr                        true
% 3.20/0.99  --sat_out_model                         small
% 3.20/0.99  --sat_out_clauses                       false
% 3.20/0.99  
% 3.20/0.99  ------ QBF Options
% 3.20/0.99  
% 3.20/0.99  --qbf_mode                              false
% 3.20/0.99  --qbf_elim_univ                         false
% 3.20/0.99  --qbf_dom_inst                          none
% 3.20/0.99  --qbf_dom_pre_inst                      false
% 3.20/0.99  --qbf_sk_in                             false
% 3.20/0.99  --qbf_pred_elim                         true
% 3.20/0.99  --qbf_split                             512
% 3.20/0.99  
% 3.20/0.99  ------ BMC1 Options
% 3.20/0.99  
% 3.20/0.99  --bmc1_incremental                      false
% 3.20/0.99  --bmc1_axioms                           reachable_all
% 3.20/0.99  --bmc1_min_bound                        0
% 3.20/0.99  --bmc1_max_bound                        -1
% 3.20/0.99  --bmc1_max_bound_default                -1
% 3.20/0.99  --bmc1_symbol_reachability              true
% 3.20/0.99  --bmc1_property_lemmas                  false
% 3.20/0.99  --bmc1_k_induction                      false
% 3.20/0.99  --bmc1_non_equiv_states                 false
% 3.20/0.99  --bmc1_deadlock                         false
% 3.20/0.99  --bmc1_ucm                              false
% 3.20/0.99  --bmc1_add_unsat_core                   none
% 3.20/0.99  --bmc1_unsat_core_children              false
% 3.20/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.20/0.99  --bmc1_out_stat                         full
% 3.20/0.99  --bmc1_ground_init                      false
% 3.20/0.99  --bmc1_pre_inst_next_state              false
% 3.20/0.99  --bmc1_pre_inst_state                   false
% 3.20/0.99  --bmc1_pre_inst_reach_state             false
% 3.20/0.99  --bmc1_out_unsat_core                   false
% 3.20/0.99  --bmc1_aig_witness_out                  false
% 3.20/0.99  --bmc1_verbose                          false
% 3.20/0.99  --bmc1_dump_clauses_tptp                false
% 3.20/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.20/0.99  --bmc1_dump_file                        -
% 3.20/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.20/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.20/0.99  --bmc1_ucm_extend_mode                  1
% 3.20/0.99  --bmc1_ucm_init_mode                    2
% 3.20/0.99  --bmc1_ucm_cone_mode                    none
% 3.20/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.20/0.99  --bmc1_ucm_relax_model                  4
% 3.20/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.20/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.20/0.99  --bmc1_ucm_layered_model                none
% 3.20/0.99  --bmc1_ucm_max_lemma_size               10
% 3.20/0.99  
% 3.20/0.99  ------ AIG Options
% 3.20/0.99  
% 3.20/0.99  --aig_mode                              false
% 3.20/0.99  
% 3.20/0.99  ------ Instantiation Options
% 3.20/0.99  
% 3.20/0.99  --instantiation_flag                    true
% 3.20/0.99  --inst_sos_flag                         true
% 3.20/0.99  --inst_sos_phase                        true
% 3.20/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.20/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.20/0.99  --inst_lit_sel_side                     none
% 3.20/0.99  --inst_solver_per_active                1400
% 3.20/0.99  --inst_solver_calls_frac                1.
% 3.20/0.99  --inst_passive_queue_type               priority_queues
% 3.20/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.20/0.99  --inst_passive_queues_freq              [25;2]
% 3.20/0.99  --inst_dismatching                      true
% 3.20/0.99  --inst_eager_unprocessed_to_passive     true
% 3.20/0.99  --inst_prop_sim_given                   true
% 3.20/0.99  --inst_prop_sim_new                     false
% 3.20/0.99  --inst_subs_new                         false
% 3.20/0.99  --inst_eq_res_simp                      false
% 3.20/0.99  --inst_subs_given                       false
% 3.20/0.99  --inst_orphan_elimination               true
% 3.20/0.99  --inst_learning_loop_flag               true
% 3.20/0.99  --inst_learning_start                   3000
% 3.20/0.99  --inst_learning_factor                  2
% 3.20/0.99  --inst_start_prop_sim_after_learn       3
% 3.20/0.99  --inst_sel_renew                        solver
% 3.20/0.99  --inst_lit_activity_flag                true
% 3.20/0.99  --inst_restr_to_given                   false
% 3.20/0.99  --inst_activity_threshold               500
% 3.20/0.99  --inst_out_proof                        true
% 3.20/0.99  
% 3.20/0.99  ------ Resolution Options
% 3.20/0.99  
% 3.20/0.99  --resolution_flag                       false
% 3.20/0.99  --res_lit_sel                           adaptive
% 3.20/0.99  --res_lit_sel_side                      none
% 3.20/0.99  --res_ordering                          kbo
% 3.20/0.99  --res_to_prop_solver                    active
% 3.20/0.99  --res_prop_simpl_new                    false
% 3.20/0.99  --res_prop_simpl_given                  true
% 3.20/0.99  --res_passive_queue_type                priority_queues
% 3.20/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.20/0.99  --res_passive_queues_freq               [15;5]
% 3.20/0.99  --res_forward_subs                      full
% 3.20/0.99  --res_backward_subs                     full
% 3.20/0.99  --res_forward_subs_resolution           true
% 3.20/0.99  --res_backward_subs_resolution          true
% 3.20/0.99  --res_orphan_elimination                true
% 3.20/0.99  --res_time_limit                        2.
% 3.20/0.99  --res_out_proof                         true
% 3.20/0.99  
% 3.20/0.99  ------ Superposition Options
% 3.20/0.99  
% 3.20/0.99  --superposition_flag                    true
% 3.20/0.99  --sup_passive_queue_type                priority_queues
% 3.20/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.20/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.20/0.99  --demod_completeness_check              fast
% 3.20/0.99  --demod_use_ground                      true
% 3.20/0.99  --sup_to_prop_solver                    passive
% 3.20/0.99  --sup_prop_simpl_new                    true
% 3.20/0.99  --sup_prop_simpl_given                  true
% 3.20/0.99  --sup_fun_splitting                     true
% 3.20/0.99  --sup_smt_interval                      50000
% 3.20/0.99  
% 3.20/0.99  ------ Superposition Simplification Setup
% 3.20/0.99  
% 3.20/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.20/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.20/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.20/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.20/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.20/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.20/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.20/0.99  --sup_immed_triv                        [TrivRules]
% 3.20/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.20/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.20/0.99  --sup_immed_bw_main                     []
% 3.20/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.20/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.20/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.20/0.99  --sup_input_bw                          []
% 3.20/0.99  
% 3.20/0.99  ------ Combination Options
% 3.20/0.99  
% 3.20/0.99  --comb_res_mult                         3
% 3.20/0.99  --comb_sup_mult                         2
% 3.20/0.99  --comb_inst_mult                        10
% 3.20/0.99  
% 3.20/0.99  ------ Debug Options
% 3.20/0.99  
% 3.20/0.99  --dbg_backtrace                         false
% 3.20/0.99  --dbg_dump_prop_clauses                 false
% 3.20/0.99  --dbg_dump_prop_clauses_file            -
% 3.20/0.99  --dbg_out_stat                          false
% 3.20/0.99  
% 3.20/0.99  
% 3.20/0.99  
% 3.20/0.99  
% 3.20/0.99  ------ Proving...
% 3.20/0.99  
% 3.20/0.99  
% 3.20/0.99  % SZS status Theorem for theBenchmark.p
% 3.20/0.99  
% 3.20/0.99   Resolution empty clause
% 3.20/0.99  
% 3.20/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.20/0.99  
% 3.20/0.99  fof(f21,conjecture,(
% 3.20/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)))),
% 3.20/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f22,negated_conjecture,(
% 3.20/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)))),
% 3.20/0.99    inference(negated_conjecture,[],[f21])).
% 3.20/0.99  
% 3.20/0.99  fof(f38,plain,(
% 3.20/0.99    ? [X0,X1,X2] : ((k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 3.20/0.99    inference(ennf_transformation,[],[f22])).
% 3.20/0.99  
% 3.20/0.99  fof(f39,plain,(
% 3.20/0.99    ? [X0,X1,X2] : (k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 3.20/0.99    inference(flattening,[],[f38])).
% 3.20/0.99  
% 3.20/0.99  fof(f44,plain,(
% 3.20/0.99    ? [X0,X1,X2] : (k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_tarski(k1_funct_1(sK2,sK0)) != k2_relset_1(k1_tarski(sK0),sK1,sK2) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2))),
% 3.20/0.99    introduced(choice_axiom,[])).
% 3.20/0.99  
% 3.20/0.99  fof(f45,plain,(
% 3.20/0.99    k1_tarski(k1_funct_1(sK2,sK0)) != k2_relset_1(k1_tarski(sK0),sK1,sK2) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2)),
% 3.20/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f39,f44])).
% 3.20/0.99  
% 3.20/0.99  fof(f76,plain,(
% 3.20/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 3.20/0.99    inference(cnf_transformation,[],[f45])).
% 3.20/0.99  
% 3.20/0.99  fof(f3,axiom,(
% 3.20/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.20/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f48,plain,(
% 3.20/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.20/0.99    inference(cnf_transformation,[],[f3])).
% 3.20/0.99  
% 3.20/0.99  fof(f4,axiom,(
% 3.20/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.20/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f49,plain,(
% 3.20/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.20/0.99    inference(cnf_transformation,[],[f4])).
% 3.20/0.99  
% 3.20/0.99  fof(f5,axiom,(
% 3.20/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.20/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f50,plain,(
% 3.20/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.20/0.99    inference(cnf_transformation,[],[f5])).
% 3.20/0.99  
% 3.20/0.99  fof(f6,axiom,(
% 3.20/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.20/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f51,plain,(
% 3.20/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.20/0.99    inference(cnf_transformation,[],[f6])).
% 3.20/0.99  
% 3.20/0.99  fof(f7,axiom,(
% 3.20/0.99    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.20/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f52,plain,(
% 3.20/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.20/0.99    inference(cnf_transformation,[],[f7])).
% 3.20/0.99  
% 3.20/0.99  fof(f8,axiom,(
% 3.20/0.99    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.20/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f53,plain,(
% 3.20/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.20/0.99    inference(cnf_transformation,[],[f8])).
% 3.20/0.99  
% 3.20/0.99  fof(f9,axiom,(
% 3.20/0.99    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.20/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f54,plain,(
% 3.20/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.20/0.99    inference(cnf_transformation,[],[f9])).
% 3.20/0.99  
% 3.20/0.99  fof(f79,plain,(
% 3.20/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.20/0.99    inference(definition_unfolding,[],[f53,f54])).
% 3.20/0.99  
% 3.20/0.99  fof(f80,plain,(
% 3.20/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.20/0.99    inference(definition_unfolding,[],[f52,f79])).
% 3.20/0.99  
% 3.20/0.99  fof(f81,plain,(
% 3.20/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.20/0.99    inference(definition_unfolding,[],[f51,f80])).
% 3.20/0.99  
% 3.20/0.99  fof(f82,plain,(
% 3.20/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.20/0.99    inference(definition_unfolding,[],[f50,f81])).
% 3.20/0.99  
% 3.20/0.99  fof(f83,plain,(
% 3.20/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.20/0.99    inference(definition_unfolding,[],[f49,f82])).
% 3.20/0.99  
% 3.20/0.99  fof(f84,plain,(
% 3.20/0.99    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.20/0.99    inference(definition_unfolding,[],[f48,f83])).
% 3.20/0.99  
% 3.20/0.99  fof(f92,plain,(
% 3.20/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)))),
% 3.20/0.99    inference(definition_unfolding,[],[f76,f84])).
% 3.20/0.99  
% 3.20/0.99  fof(f19,axiom,(
% 3.20/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 3.20/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f35,plain,(
% 3.20/0.99    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.20/0.99    inference(ennf_transformation,[],[f19])).
% 3.20/0.99  
% 3.20/0.99  fof(f71,plain,(
% 3.20/0.99    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.20/0.99    inference(cnf_transformation,[],[f35])).
% 3.20/0.99  
% 3.20/0.99  fof(f20,axiom,(
% 3.20/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,X1) = X0))),
% 3.20/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f36,plain,(
% 3.20/0.99    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.20/0.99    inference(ennf_transformation,[],[f20])).
% 3.20/0.99  
% 3.20/0.99  fof(f37,plain,(
% 3.20/0.99    ! [X0,X1,X2] : (k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.20/0.99    inference(flattening,[],[f36])).
% 3.20/0.99  
% 3.20/0.99  fof(f72,plain,(
% 3.20/0.99    ( ! [X2,X0,X1] : (k8_relset_1(X0,X1,X2,X1) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.20/0.99    inference(cnf_transformation,[],[f37])).
% 3.20/0.99  
% 3.20/0.99  fof(f75,plain,(
% 3.20/0.99    v1_funct_2(sK2,k1_tarski(sK0),sK1)),
% 3.20/0.99    inference(cnf_transformation,[],[f45])).
% 3.20/0.99  
% 3.20/0.99  fof(f93,plain,(
% 3.20/0.99    v1_funct_2(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),
% 3.20/0.99    inference(definition_unfolding,[],[f75,f84])).
% 3.20/0.99  
% 3.20/0.99  fof(f74,plain,(
% 3.20/0.99    v1_funct_1(sK2)),
% 3.20/0.99    inference(cnf_transformation,[],[f45])).
% 3.20/0.99  
% 3.20/0.99  fof(f77,plain,(
% 3.20/0.99    k1_xboole_0 != sK1),
% 3.20/0.99    inference(cnf_transformation,[],[f45])).
% 3.20/0.99  
% 3.20/0.99  fof(f16,axiom,(
% 3.20/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.20/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f23,plain,(
% 3.20/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.20/0.99    inference(pure_predicate_removal,[],[f16])).
% 3.20/0.99  
% 3.20/0.99  fof(f32,plain,(
% 3.20/0.99    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.20/0.99    inference(ennf_transformation,[],[f23])).
% 3.20/0.99  
% 3.20/0.99  fof(f68,plain,(
% 3.20/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.20/0.99    inference(cnf_transformation,[],[f32])).
% 3.20/0.99  
% 3.20/0.99  fof(f12,axiom,(
% 3.20/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.20/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f26,plain,(
% 3.20/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.20/0.99    inference(ennf_transformation,[],[f12])).
% 3.20/0.99  
% 3.20/0.99  fof(f43,plain,(
% 3.20/0.99    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.20/0.99    inference(nnf_transformation,[],[f26])).
% 3.20/0.99  
% 3.20/0.99  fof(f62,plain,(
% 3.20/0.99    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.20/0.99    inference(cnf_transformation,[],[f43])).
% 3.20/0.99  
% 3.20/0.99  fof(f15,axiom,(
% 3.20/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.20/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f31,plain,(
% 3.20/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.20/0.99    inference(ennf_transformation,[],[f15])).
% 3.20/0.99  
% 3.20/0.99  fof(f67,plain,(
% 3.20/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.20/0.99    inference(cnf_transformation,[],[f31])).
% 3.20/0.99  
% 3.20/0.99  fof(f10,axiom,(
% 3.20/0.99    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 3.20/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f25,plain,(
% 3.20/0.99    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 3.20/0.99    inference(ennf_transformation,[],[f10])).
% 3.20/0.99  
% 3.20/0.99  fof(f40,plain,(
% 3.20/0.99    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 3.20/0.99    inference(nnf_transformation,[],[f25])).
% 3.20/0.99  
% 3.20/0.99  fof(f41,plain,(
% 3.20/0.99    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 3.20/0.99    inference(flattening,[],[f40])).
% 3.20/0.99  
% 3.20/0.99  fof(f55,plain,(
% 3.20/0.99    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 3.20/0.99    inference(cnf_transformation,[],[f41])).
% 3.20/0.99  
% 3.20/0.99  fof(f89,plain,(
% 3.20/0.99    ( ! [X2,X0,X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = X0 | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = X0 | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) )),
% 3.20/0.99    inference(definition_unfolding,[],[f55,f83,f84,f84,f83])).
% 3.20/0.99  
% 3.20/0.99  fof(f78,plain,(
% 3.20/0.99    k1_tarski(k1_funct_1(sK2,sK0)) != k2_relset_1(k1_tarski(sK0),sK1,sK2)),
% 3.20/0.99    inference(cnf_transformation,[],[f45])).
% 3.20/0.99  
% 3.20/0.99  fof(f91,plain,(
% 3.20/0.99    k6_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK2)),
% 3.20/0.99    inference(definition_unfolding,[],[f78,f84,f84])).
% 3.20/0.99  
% 3.20/0.99  fof(f18,axiom,(
% 3.20/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.20/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f34,plain,(
% 3.20/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.20/0.99    inference(ennf_transformation,[],[f18])).
% 3.20/0.99  
% 3.20/0.99  fof(f70,plain,(
% 3.20/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.20/0.99    inference(cnf_transformation,[],[f34])).
% 3.20/0.99  
% 3.20/0.99  fof(f14,axiom,(
% 3.20/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 3.20/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f29,plain,(
% 3.20/0.99    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.20/0.99    inference(ennf_transformation,[],[f14])).
% 3.20/0.99  
% 3.20/0.99  fof(f30,plain,(
% 3.20/0.99    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.20/0.99    inference(flattening,[],[f29])).
% 3.20/0.99  
% 3.20/0.99  fof(f66,plain,(
% 3.20/0.99    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.20/0.99    inference(cnf_transformation,[],[f30])).
% 3.20/0.99  
% 3.20/0.99  fof(f90,plain,(
% 3.20/0.99    ( ! [X0,X1] : (k6_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.20/0.99    inference(definition_unfolding,[],[f66,f84,f84])).
% 3.20/0.99  
% 3.20/0.99  fof(f13,axiom,(
% 3.20/0.99    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 3.20/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f27,plain,(
% 3.20/0.99    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.20/0.99    inference(ennf_transformation,[],[f13])).
% 3.20/0.99  
% 3.20/0.99  fof(f28,plain,(
% 3.20/0.99    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.20/0.99    inference(flattening,[],[f27])).
% 3.20/0.99  
% 3.20/0.99  fof(f64,plain,(
% 3.20/0.99    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.20/0.99    inference(cnf_transformation,[],[f28])).
% 3.20/0.99  
% 3.20/0.99  fof(f1,axiom,(
% 3.20/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.20/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f46,plain,(
% 3.20/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.20/0.99    inference(cnf_transformation,[],[f1])).
% 3.20/0.99  
% 3.20/0.99  fof(f11,axiom,(
% 3.20/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.20/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f42,plain,(
% 3.20/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.20/0.99    inference(nnf_transformation,[],[f11])).
% 3.20/0.99  
% 3.20/0.99  fof(f61,plain,(
% 3.20/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.20/0.99    inference(cnf_transformation,[],[f42])).
% 3.20/0.99  
% 3.20/0.99  fof(f17,axiom,(
% 3.20/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)))),
% 3.20/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f33,plain,(
% 3.20/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.20/0.99    inference(ennf_transformation,[],[f17])).
% 3.20/0.99  
% 3.20/0.99  fof(f69,plain,(
% 3.20/0.99    ( ! [X2,X0,X3,X1] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.20/0.99    inference(cnf_transformation,[],[f33])).
% 3.20/0.99  
% 3.20/0.99  fof(f60,plain,(
% 3.20/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.20/0.99    inference(cnf_transformation,[],[f42])).
% 3.20/0.99  
% 3.20/0.99  fof(f2,axiom,(
% 3.20/0.99    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 3.20/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.20/0.99  
% 3.20/0.99  fof(f24,plain,(
% 3.20/0.99    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 3.20/0.99    inference(ennf_transformation,[],[f2])).
% 3.20/0.99  
% 3.20/0.99  fof(f47,plain,(
% 3.20/0.99    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 3.20/0.99    inference(cnf_transformation,[],[f24])).
% 3.20/0.99  
% 3.20/0.99  cnf(c_23,negated_conjecture,
% 3.20/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) ),
% 3.20/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1558,plain,
% 3.20/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_18,plain,
% 3.20/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.20/0.99      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 3.20/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1559,plain,
% 3.20/0.99      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 3.20/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2347,plain,
% 3.20/0.99      ( k8_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK2,X0) = k10_relat_1(sK2,X0) ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_1558,c_1559]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_20,plain,
% 3.20/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.20/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.20/0.99      | ~ v1_funct_1(X0)
% 3.20/0.99      | k8_relset_1(X1,X2,X0,X2) = X1
% 3.20/0.99      | k1_xboole_0 = X2 ),
% 3.20/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_24,negated_conjecture,
% 3.20/0.99      ( v1_funct_2(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
% 3.20/0.99      inference(cnf_transformation,[],[f93]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_362,plain,
% 3.20/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.20/0.99      | ~ v1_funct_1(X0)
% 3.20/0.99      | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != X1
% 3.20/0.99      | k8_relset_1(X1,X2,X0,X2) = X1
% 3.20/0.99      | sK1 != X2
% 3.20/0.99      | sK2 != X0
% 3.20/0.99      | k1_xboole_0 = X2 ),
% 3.20/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_24]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_363,plain,
% 3.20/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)))
% 3.20/0.99      | ~ v1_funct_1(sK2)
% 3.20/0.99      | k8_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK2,sK1) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
% 3.20/0.99      | k1_xboole_0 = sK1 ),
% 3.20/0.99      inference(unflattening,[status(thm)],[c_362]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_25,negated_conjecture,
% 3.20/0.99      ( v1_funct_1(sK2) ),
% 3.20/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_22,negated_conjecture,
% 3.20/0.99      ( k1_xboole_0 != sK1 ),
% 3.20/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_365,plain,
% 3.20/0.99      ( k8_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK2,sK1) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
% 3.20/0.99      inference(global_propositional_subsumption,
% 3.20/0.99                [status(thm)],
% 3.20/0.99                [c_363,c_25,c_23,c_22]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2528,plain,
% 3.20/0.99      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k10_relat_1(sK2,sK1) ),
% 3.20/0.99      inference(demodulation,[status(thm)],[c_2347,c_365]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_15,plain,
% 3.20/0.99      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.20/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_10,plain,
% 3.20/0.99      ( ~ v4_relat_1(X0,X1) | r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 3.20/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_324,plain,
% 3.20/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.20/0.99      | r1_tarski(k1_relat_1(X0),X1)
% 3.20/0.99      | ~ v1_relat_1(X0) ),
% 3.20/0.99      inference(resolution,[status(thm)],[c_15,c_10]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_14,plain,
% 3.20/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 3.20/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_328,plain,
% 3.20/0.99      ( r1_tarski(k1_relat_1(X0),X1)
% 3.20/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.20/0.99      inference(global_propositional_subsumption,[status(thm)],[c_324,c_14]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_329,plain,
% 3.20/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.20/0.99      | r1_tarski(k1_relat_1(X0),X1) ),
% 3.20/0.99      inference(renaming,[status(thm)],[c_328]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1557,plain,
% 3.20/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.20/0.99      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_329]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1881,plain,
% 3.20/0.99      ( r1_tarski(k1_relat_1(sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_1558,c_1557]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2582,plain,
% 3.20/0.99      ( r1_tarski(k1_relat_1(sK2),k10_relat_1(sK2,sK1)) = iProver_top ),
% 3.20/0.99      inference(demodulation,[status(thm)],[c_2528,c_1881]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_6,plain,
% 3.20/0.99      ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
% 3.20/0.99      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = X0
% 3.20/0.99      | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = X0
% 3.20/0.99      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
% 3.20/0.99      | k1_xboole_0 = X0 ),
% 3.20/0.99      inference(cnf_transformation,[],[f89]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1567,plain,
% 3.20/0.99      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = X2
% 3.20/0.99      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X2
% 3.20/0.99      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X2
% 3.20/0.99      | k1_xboole_0 = X2
% 3.20/0.99      | r1_tarski(X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2702,plain,
% 3.20/0.99      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = X0
% 3.20/0.99      | k1_xboole_0 = X0
% 3.20/0.99      | r1_tarski(X0,k10_relat_1(sK2,sK1)) != iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_2528,c_1567]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2703,plain,
% 3.20/0.99      ( k10_relat_1(sK2,sK1) = X0
% 3.20/0.99      | k1_xboole_0 = X0
% 3.20/0.99      | r1_tarski(X0,k10_relat_1(sK2,sK1)) != iProver_top ),
% 3.20/0.99      inference(demodulation,[status(thm)],[c_2702,c_2528]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_3041,plain,
% 3.20/0.99      ( k10_relat_1(sK2,sK1) = k1_relat_1(sK2)
% 3.20/0.99      | k1_relat_1(sK2) = k1_xboole_0 ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_2582,c_2703]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_21,negated_conjecture,
% 3.20/0.99      ( k6_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK2) ),
% 3.20/0.99      inference(cnf_transformation,[],[f91]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1095,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1595,plain,
% 3.20/0.99      ( k6_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != X0
% 3.20/0.99      | k6_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK2)
% 3.20/0.99      | k2_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK2) != X0 ),
% 3.20/0.99      inference(instantiation,[status(thm)],[c_1095]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1647,plain,
% 3.20/0.99      ( k6_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK2)
% 3.20/0.99      | k6_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relat_1(sK2)
% 3.20/0.99      | k2_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK2) != k2_relat_1(sK2) ),
% 3.20/0.99      inference(instantiation,[status(thm)],[c_1595]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_17,plain,
% 3.20/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.20/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.20/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1707,plain,
% 3.20/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)))
% 3.20/0.99      | k2_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK2) = k2_relat_1(sK2) ),
% 3.20/0.99      inference(instantiation,[status(thm)],[c_17]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_13,plain,
% 3.20/0.99      ( ~ v1_funct_1(X0)
% 3.20/0.99      | ~ v1_relat_1(X0)
% 3.20/0.99      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k1_relat_1(X0)
% 3.20/0.99      | k6_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
% 3.20/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_375,plain,
% 3.20/0.99      ( ~ v1_relat_1(X0)
% 3.20/0.99      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k1_relat_1(X0)
% 3.20/0.99      | k6_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
% 3.20/0.99      | sK2 != X0 ),
% 3.20/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_25]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_376,plain,
% 3.20/0.99      ( ~ v1_relat_1(sK2)
% 3.20/0.99      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_relat_1(sK2)
% 3.20/0.99      | k6_enumset1(k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0)) = k2_relat_1(sK2) ),
% 3.20/0.99      inference(unflattening,[status(thm)],[c_375]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1555,plain,
% 3.20/0.99      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_relat_1(sK2)
% 3.20/0.99      | k6_enumset1(k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0)) = k2_relat_1(sK2)
% 3.20/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_376]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_28,plain,
% 3.20/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_377,plain,
% 3.20/0.99      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_relat_1(sK2)
% 3.20/0.99      | k6_enumset1(k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0)) = k2_relat_1(sK2)
% 3.20/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_376]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1659,plain,
% 3.20/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(sK2) ),
% 3.20/0.99      inference(instantiation,[status(thm)],[c_14]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1725,plain,
% 3.20/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)))
% 3.20/0.99      | v1_relat_1(sK2) ),
% 3.20/0.99      inference(instantiation,[status(thm)],[c_1659]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1726,plain,
% 3.20/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) != iProver_top
% 3.20/0.99      | v1_relat_1(sK2) = iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_1725]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1790,plain,
% 3.20/0.99      ( k6_enumset1(k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0)) = k2_relat_1(sK2)
% 3.20/0.99      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_relat_1(sK2) ),
% 3.20/0.99      inference(global_propositional_subsumption,
% 3.20/0.99                [status(thm)],
% 3.20/0.99                [c_1555,c_28,c_377,c_1726]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1791,plain,
% 3.20/0.99      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_relat_1(sK2)
% 3.20/0.99      | k6_enumset1(k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0)) = k2_relat_1(sK2) ),
% 3.20/0.99      inference(renaming,[status(thm)],[c_1790]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2593,plain,
% 3.20/0.99      ( k6_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2)
% 3.20/0.99      | k10_relat_1(sK2,sK1) != k1_relat_1(sK2) ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_2528,c_1791]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_3260,plain,
% 3.20/0.99      ( k1_relat_1(sK2) = k1_xboole_0 ),
% 3.20/0.99      inference(global_propositional_subsumption,
% 3.20/0.99                [status(thm)],
% 3.20/0.99                [c_3041,c_23,c_21,c_1647,c_1707,c_2593]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_12,plain,
% 3.20/0.99      ( ~ v1_relat_1(X0) | k1_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = X0 ),
% 3.20/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1563,plain,
% 3.20/0.99      ( k1_relat_1(X0) != k1_xboole_0
% 3.20/0.99      | k1_xboole_0 = X0
% 3.20/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_3266,plain,
% 3.20/0.99      ( sK2 = k1_xboole_0 | v1_relat_1(sK2) != iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_3260,c_1563]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1094,plain,( X0 = X0 ),theory(equality) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1769,plain,
% 3.20/0.99      ( sK2 = sK2 ),
% 3.20/0.99      inference(instantiation,[status(thm)],[c_1094]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1687,plain,
% 3.20/0.99      ( X0 != X1 | sK2 != X1 | sK2 = X0 ),
% 3.20/0.99      inference(instantiation,[status(thm)],[c_1095]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1785,plain,
% 3.20/0.99      ( X0 != sK2 | sK2 = X0 | sK2 != sK2 ),
% 3.20/0.99      inference(instantiation,[status(thm)],[c_1687]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2003,plain,
% 3.20/0.99      ( sK2 != sK2 | sK2 = k1_xboole_0 | k1_xboole_0 != sK2 ),
% 3.20/0.99      inference(instantiation,[status(thm)],[c_1785]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2118,plain,
% 3.20/0.99      ( ~ v1_relat_1(sK2)
% 3.20/0.99      | k1_relat_1(sK2) != k1_xboole_0
% 3.20/0.99      | k1_xboole_0 = sK2 ),
% 3.20/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_3743,plain,
% 3.20/0.99      ( sK2 = k1_xboole_0 ),
% 3.20/0.99      inference(global_propositional_subsumption,
% 3.20/0.99                [status(thm)],
% 3.20/0.99                [c_3266,c_23,c_21,c_1647,c_1707,c_1725,c_1769,c_2003,c_2118,
% 3.20/0.99                 c_2593,c_3041]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_3037,plain,
% 3.20/0.99      ( k10_relat_1(sK2,sK1) != k1_relat_1(sK2) ),
% 3.20/0.99      inference(global_propositional_subsumption,
% 3.20/0.99                [status(thm)],
% 3.20/0.99                [c_2593,c_23,c_21,c_1647,c_1707]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_3262,plain,
% 3.20/0.99      ( k10_relat_1(sK2,sK1) != k1_xboole_0 ),
% 3.20/0.99      inference(demodulation,[status(thm)],[c_3260,c_3037]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_3750,plain,
% 3.20/0.99      ( k10_relat_1(k1_xboole_0,sK1) != k1_xboole_0 ),
% 3.20/0.99      inference(demodulation,[status(thm)],[c_3743,c_3262]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_0,plain,
% 3.20/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 3.20/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1573,plain,
% 3.20/0.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_7,plain,
% 3.20/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.20/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1566,plain,
% 3.20/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.20/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2345,plain,
% 3.20/0.99      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 3.20/0.99      | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_1566,c_1559]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_4612,plain,
% 3.20/0.99      ( k8_relset_1(X0,X1,k1_xboole_0,X2) = k10_relat_1(k1_xboole_0,X2) ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_1573,c_2345]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_16,plain,
% 3.20/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.20/0.99      | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) ),
% 3.20/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1561,plain,
% 3.20/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.20/0.99      | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) = iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_8,plain,
% 3.20/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.20/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1565,plain,
% 3.20/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.20/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_2291,plain,
% 3.20/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.20/0.99      | r1_tarski(k8_relset_1(X1,X2,X0,X3),X1) = iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_1561,c_1565]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1,plain,
% 3.20/0.99      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 3.20/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_1572,plain,
% 3.20/0.99      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.20/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_3100,plain,
% 3.20/0.99      ( k8_relset_1(k1_xboole_0,X0,X1,X2) = k1_xboole_0
% 3.20/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_2291,c_1572]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_3252,plain,
% 3.20/0.99      ( k8_relset_1(k1_xboole_0,X0,X1,X2) = k1_xboole_0
% 3.20/0.99      | r1_tarski(X1,k2_zfmisc_1(k1_xboole_0,X0)) != iProver_top ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_1566,c_3100]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_3790,plain,
% 3.20/0.99      ( k8_relset_1(k1_xboole_0,X0,k1_xboole_0,X1) = k1_xboole_0 ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_1573,c_3252]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_4724,plain,
% 3.20/0.99      ( k10_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.20/0.99      inference(superposition,[status(thm)],[c_4612,c_3790]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_5131,plain,
% 3.20/0.99      ( k1_xboole_0 != k1_xboole_0 ),
% 3.20/0.99      inference(demodulation,[status(thm)],[c_3750,c_4724]) ).
% 3.20/0.99  
% 3.20/0.99  cnf(c_5132,plain,
% 3.20/0.99      ( $false ),
% 3.20/0.99      inference(equality_resolution_simp,[status(thm)],[c_5131]) ).
% 3.20/0.99  
% 3.20/0.99  
% 3.20/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.20/0.99  
% 3.20/0.99  ------                               Statistics
% 3.20/0.99  
% 3.20/0.99  ------ General
% 3.20/0.99  
% 3.20/0.99  abstr_ref_over_cycles:                  0
% 3.20/0.99  abstr_ref_under_cycles:                 0
% 3.20/0.99  gc_basic_clause_elim:                   0
% 3.20/0.99  forced_gc_time:                         0
% 3.20/0.99  parsing_time:                           0.011
% 3.20/0.99  unif_index_cands_time:                  0.
% 3.20/0.99  unif_index_add_time:                    0.
% 3.20/0.99  orderings_time:                         0.
% 3.20/0.99  out_proof_time:                         0.011
% 3.20/0.99  total_time:                             0.204
% 3.20/0.99  num_of_symbols:                         50
% 3.20/0.99  num_of_terms:                           5012
% 3.20/0.99  
% 3.20/0.99  ------ Preprocessing
% 3.20/0.99  
% 3.20/0.99  num_of_splits:                          0
% 3.20/0.99  num_of_split_atoms:                     0
% 3.20/0.99  num_of_reused_defs:                     0
% 3.20/0.99  num_eq_ax_congr_red:                    14
% 3.20/0.99  num_of_sem_filtered_clauses:            1
% 3.20/0.99  num_of_subtypes:                        0
% 3.20/0.99  monotx_restored_types:                  0
% 3.20/0.99  sat_num_of_epr_types:                   0
% 3.20/0.99  sat_num_of_non_cyclic_types:            0
% 3.20/0.99  sat_guarded_non_collapsed_types:        0
% 3.20/0.99  num_pure_diseq_elim:                    0
% 3.20/0.99  simp_replaced_by:                       0
% 3.20/0.99  res_preprocessed:                       119
% 3.20/0.99  prep_upred:                             0
% 3.20/0.99  prep_unflattend:                        72
% 3.20/0.99  smt_new_axioms:                         0
% 3.20/0.99  pred_elim_cands:                        3
% 3.20/0.99  pred_elim:                              3
% 3.20/0.99  pred_elim_cl:                           4
% 3.20/0.99  pred_elim_cycles:                       7
% 3.20/0.99  merged_defs:                            8
% 3.20/0.99  merged_defs_ncl:                        0
% 3.20/0.99  bin_hyper_res:                          8
% 3.20/0.99  prep_cycles:                            4
% 3.20/0.99  pred_elim_time:                         0.011
% 3.20/0.99  splitting_time:                         0.
% 3.20/0.99  sem_filter_time:                        0.
% 3.20/0.99  monotx_time:                            0.001
% 3.20/0.99  subtype_inf_time:                       0.
% 3.20/0.99  
% 3.20/0.99  ------ Problem properties
% 3.20/0.99  
% 3.20/0.99  clauses:                                22
% 3.20/0.99  conjectures:                            3
% 3.20/0.99  epr:                                    3
% 3.20/0.99  horn:                                   21
% 3.20/0.99  ground:                                 5
% 3.20/0.99  unary:                                  9
% 3.20/0.99  binary:                                 8
% 3.20/0.99  lits:                                   42
% 3.20/0.99  lits_eq:                                18
% 3.20/0.99  fd_pure:                                0
% 3.20/0.99  fd_pseudo:                              0
% 3.20/0.99  fd_cond:                                3
% 3.20/0.99  fd_pseudo_cond:                         1
% 3.20/0.99  ac_symbols:                             0
% 3.20/0.99  
% 3.20/0.99  ------ Propositional Solver
% 3.20/0.99  
% 3.20/0.99  prop_solver_calls:                      33
% 3.20/0.99  prop_fast_solver_calls:                 818
% 3.20/0.99  smt_solver_calls:                       0
% 3.20/0.99  smt_fast_solver_calls:                  0
% 3.20/0.99  prop_num_of_clauses:                    1883
% 3.20/0.99  prop_preprocess_simplified:             5807
% 3.20/0.99  prop_fo_subsumed:                       11
% 3.20/0.99  prop_solver_time:                       0.
% 3.20/0.99  smt_solver_time:                        0.
% 3.20/0.99  smt_fast_solver_time:                   0.
% 3.20/0.99  prop_fast_solver_time:                  0.
% 3.20/0.99  prop_unsat_core_time:                   0.
% 3.20/0.99  
% 3.20/0.99  ------ QBF
% 3.20/0.99  
% 3.20/0.99  qbf_q_res:                              0
% 3.20/0.99  qbf_num_tautologies:                    0
% 3.20/0.99  qbf_prep_cycles:                        0
% 3.20/0.99  
% 3.20/0.99  ------ BMC1
% 3.20/0.99  
% 3.20/0.99  bmc1_current_bound:                     -1
% 3.20/0.99  bmc1_last_solved_bound:                 -1
% 3.20/0.99  bmc1_unsat_core_size:                   -1
% 3.20/0.99  bmc1_unsat_core_parents_size:           -1
% 3.20/0.99  bmc1_merge_next_fun:                    0
% 3.20/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.20/0.99  
% 3.20/0.99  ------ Instantiation
% 3.20/0.99  
% 3.20/0.99  inst_num_of_clauses:                    609
% 3.20/0.99  inst_num_in_passive:                    116
% 3.20/0.99  inst_num_in_active:                     393
% 3.20/0.99  inst_num_in_unprocessed:                100
% 3.20/0.99  inst_num_of_loops:                      420
% 3.20/0.99  inst_num_of_learning_restarts:          0
% 3.20/0.99  inst_num_moves_active_passive:          21
% 3.20/0.99  inst_lit_activity:                      0
% 3.20/0.99  inst_lit_activity_moves:                0
% 3.20/0.99  inst_num_tautologies:                   0
% 3.20/0.99  inst_num_prop_implied:                  0
% 3.20/0.99  inst_num_existing_simplified:           0
% 3.20/0.99  inst_num_eq_res_simplified:             0
% 3.20/0.99  inst_num_child_elim:                    0
% 3.20/0.99  inst_num_of_dismatching_blockings:      317
% 3.20/0.99  inst_num_of_non_proper_insts:           780
% 3.20/0.99  inst_num_of_duplicates:                 0
% 3.20/0.99  inst_inst_num_from_inst_to_res:         0
% 3.20/0.99  inst_dismatching_checking_time:         0.
% 3.20/0.99  
% 3.20/0.99  ------ Resolution
% 3.20/0.99  
% 3.20/0.99  res_num_of_clauses:                     0
% 3.20/0.99  res_num_in_passive:                     0
% 3.20/0.99  res_num_in_active:                      0
% 3.20/0.99  res_num_of_loops:                       123
% 3.20/0.99  res_forward_subset_subsumed:            127
% 3.20/0.99  res_backward_subset_subsumed:           4
% 3.20/0.99  res_forward_subsumed:                   2
% 3.20/0.99  res_backward_subsumed:                  0
% 3.20/0.99  res_forward_subsumption_resolution:     0
% 3.20/0.99  res_backward_subsumption_resolution:    0
% 3.20/0.99  res_clause_to_clause_subsumption:       306
% 3.20/0.99  res_orphan_elimination:                 0
% 3.20/0.99  res_tautology_del:                      124
% 3.20/0.99  res_num_eq_res_simplified:              0
% 3.20/0.99  res_num_sel_changes:                    0
% 3.20/0.99  res_moves_from_active_to_pass:          0
% 3.20/0.99  
% 3.20/0.99  ------ Superposition
% 3.20/0.99  
% 3.20/0.99  sup_time_total:                         0.
% 3.20/0.99  sup_time_generating:                    0.
% 3.20/0.99  sup_time_sim_full:                      0.
% 3.20/0.99  sup_time_sim_immed:                     0.
% 3.20/0.99  
% 3.20/0.99  sup_num_of_clauses:                     74
% 3.20/0.99  sup_num_in_active:                      44
% 3.20/0.99  sup_num_in_passive:                     30
% 3.20/0.99  sup_num_of_loops:                       83
% 3.20/0.99  sup_fw_superposition:                   67
% 3.20/0.99  sup_bw_superposition:                   90
% 3.20/0.99  sup_immediate_simplified:               48
% 3.20/0.99  sup_given_eliminated:                   2
% 3.20/0.99  comparisons_done:                       0
% 3.20/0.99  comparisons_avoided:                    3
% 3.20/0.99  
% 3.20/0.99  ------ Simplifications
% 3.20/0.99  
% 3.20/0.99  
% 3.20/0.99  sim_fw_subset_subsumed:                 17
% 3.20/0.99  sim_bw_subset_subsumed:                 4
% 3.20/0.99  sim_fw_subsumed:                        21
% 3.20/0.99  sim_bw_subsumed:                        5
% 3.20/0.99  sim_fw_subsumption_res:                 0
% 3.20/0.99  sim_bw_subsumption_res:                 0
% 3.20/0.99  sim_tautology_del:                      2
% 3.20/0.99  sim_eq_tautology_del:                   13
% 3.20/0.99  sim_eq_res_simp:                        0
% 3.20/0.99  sim_fw_demodulated:                     13
% 3.20/0.99  sim_bw_demodulated:                     36
% 3.20/0.99  sim_light_normalised:                   10
% 3.20/0.99  sim_joinable_taut:                      0
% 3.20/0.99  sim_joinable_simp:                      0
% 3.20/0.99  sim_ac_normalised:                      0
% 3.20/0.99  sim_smt_subsumption:                    0
% 3.20/0.99  
%------------------------------------------------------------------------------
