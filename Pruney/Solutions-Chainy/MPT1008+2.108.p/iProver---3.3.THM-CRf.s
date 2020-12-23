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
% DateTime   : Thu Dec  3 12:05:26 EST 2020

% Result     : Theorem 3.22s
% Output     : CNFRefutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :  152 (1132 expanded)
%              Number of clauses        :   71 ( 180 expanded)
%              Number of leaves         :   22 ( 303 expanded)
%              Depth                    :   23
%              Number of atoms          :  540 (2870 expanded)
%              Number of equality atoms :  358 (1741 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   30 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f32,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f33,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f43,plain,
    ( ? [X0,X1,X2] :
        ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( k1_tarski(k1_funct_1(sK4,sK2)) != k2_relset_1(k1_tarski(sK2),sK3,sK4)
      & k1_xboole_0 != sK3
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3)))
      & v1_funct_2(sK4,k1_tarski(sK2),sK3)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( k1_tarski(k1_funct_1(sK4,sK2)) != k2_relset_1(k1_tarski(sK2),sK3,sK4)
    & k1_xboole_0 != sK3
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3)))
    & v1_funct_2(sK4,k1_tarski(sK2),sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f33,f43])).

fof(f85,plain,(
    v1_funct_2(sK4,k1_tarski(sK2),sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f7])).

fof(f89,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f50,f51])).

fof(f90,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f49,f89])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f48,f90])).

fof(f92,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f47,f91])).

fof(f93,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f46,f92])).

fof(f94,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f45,f93])).

fof(f101,plain,(
    v1_funct_2(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) ),
    inference(definition_unfolding,[],[f85,f94])).

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

fof(f28,plain,(
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
    inference(flattening,[],[f28])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f86,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) ),
    inference(cnf_transformation,[],[f44])).

fof(f100,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) ),
    inference(definition_unfolding,[],[f86,f94])).

fof(f87,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f44])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( k1_relset_1(X1,X0,X2) = k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1))
        & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X1,X0,X2) = k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1))
        & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k8_relset_1(X0,X1,X2,X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f84,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f44])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f11,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f97,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f69,f94])).

fof(f88,plain,(
    k1_tarski(k1_funct_1(sK4,sK2)) != k2_relset_1(k1_tarski(sK2),sK3,sK4) ),
    inference(cnf_transformation,[],[f44])).

fof(f99,plain,(
    k6_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) != k2_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK4) ),
    inference(definition_unfolding,[],[f88,f94,f94])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
    <=> ! [X7] :
          ( r2_hidden(X7,X6)
        <=> ~ ( X5 != X7
              & X4 != X7
              & X3 != X7
              & X2 != X7
              & X1 != X7
              & X0 != X7 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
    <=> ! [X7] :
          ( r2_hidden(X7,X6)
        <=> ( X5 = X7
            | X4 = X7
            | X3 = X7
            | X2 = X7
            | X1 = X7
            | X0 = X7 ) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f34,plain,(
    ! [X5,X4,X3,X2,X1,X0,X6] :
      ( sP0(X5,X4,X3,X2,X1,X0,X6)
    <=> ! [X7] :
          ( r2_hidden(X7,X6)
        <=> ( X5 = X7
            | X4 = X7
            | X3 = X7
            | X2 = X7
            | X1 = X7
            | X0 = X7 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
    <=> sP0(X5,X4,X3,X2,X1,X0,X6) ) ),
    inference(definition_folding,[],[f20,f34])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
        | ~ sP0(X5,X4,X3,X2,X1,X0,X6) )
      & ( sP0(X5,X4,X3,X2,X1,X0,X6)
        | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6 ) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f66,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( sP0(X5,X4,X3,X2,X1,X0,X6)
      | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f96,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( sP0(X5,X4,X3,X2,X1,X0,X6)
      | k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) != X6 ) ),
    inference(definition_unfolding,[],[f66,f89])).

fof(f108,plain,(
    ! [X4,X2,X0,X5,X3,X1] : sP0(X5,X4,X3,X2,X1,X0,k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) ),
    inference(equality_resolution,[],[f96])).

fof(f36,plain,(
    ! [X5,X4,X3,X2,X1,X0,X6] :
      ( ( sP0(X5,X4,X3,X2,X1,X0,X6)
        | ? [X7] :
            ( ( ( X5 != X7
                & X4 != X7
                & X3 != X7
                & X2 != X7
                & X1 != X7
                & X0 != X7 )
              | ~ r2_hidden(X7,X6) )
            & ( X5 = X7
              | X4 = X7
              | X3 = X7
              | X2 = X7
              | X1 = X7
              | X0 = X7
              | r2_hidden(X7,X6) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X6)
              | ( X5 != X7
                & X4 != X7
                & X3 != X7
                & X2 != X7
                & X1 != X7
                & X0 != X7 ) )
            & ( X5 = X7
              | X4 = X7
              | X3 = X7
              | X2 = X7
              | X1 = X7
              | X0 = X7
              | ~ r2_hidden(X7,X6) ) )
        | ~ sP0(X5,X4,X3,X2,X1,X0,X6) ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f37,plain,(
    ! [X5,X4,X3,X2,X1,X0,X6] :
      ( ( sP0(X5,X4,X3,X2,X1,X0,X6)
        | ? [X7] :
            ( ( ( X5 != X7
                & X4 != X7
                & X3 != X7
                & X2 != X7
                & X1 != X7
                & X0 != X7 )
              | ~ r2_hidden(X7,X6) )
            & ( X5 = X7
              | X4 = X7
              | X3 = X7
              | X2 = X7
              | X1 = X7
              | X0 = X7
              | r2_hidden(X7,X6) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X6)
              | ( X5 != X7
                & X4 != X7
                & X3 != X7
                & X2 != X7
                & X1 != X7
                & X0 != X7 ) )
            & ( X5 = X7
              | X4 = X7
              | X3 = X7
              | X2 = X7
              | X1 = X7
              | X0 = X7
              | ~ r2_hidden(X7,X6) ) )
        | ~ sP0(X5,X4,X3,X2,X1,X0,X6) ) ) ),
    inference(flattening,[],[f36])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( sP0(X0,X1,X2,X3,X4,X5,X6)
        | ? [X7] :
            ( ( ( X0 != X7
                & X1 != X7
                & X2 != X7
                & X3 != X7
                & X4 != X7
                & X5 != X7 )
              | ~ r2_hidden(X7,X6) )
            & ( X0 = X7
              | X1 = X7
              | X2 = X7
              | X3 = X7
              | X4 = X7
              | X5 = X7
              | r2_hidden(X7,X6) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X6)
              | ( X0 != X8
                & X1 != X8
                & X2 != X8
                & X3 != X8
                & X4 != X8
                & X5 != X8 ) )
            & ( X0 = X8
              | X1 = X8
              | X2 = X8
              | X3 = X8
              | X4 = X8
              | X5 = X8
              | ~ r2_hidden(X8,X6) ) )
        | ~ sP0(X0,X1,X2,X3,X4,X5,X6) ) ) ),
    inference(rectify,[],[f37])).

fof(f39,plain,(
    ! [X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X7] :
          ( ( ( X0 != X7
              & X1 != X7
              & X2 != X7
              & X3 != X7
              & X4 != X7
              & X5 != X7 )
            | ~ r2_hidden(X7,X6) )
          & ( X0 = X7
            | X1 = X7
            | X2 = X7
            | X3 = X7
            | X4 = X7
            | X5 = X7
            | r2_hidden(X7,X6) ) )
     => ( ( ( sK1(X0,X1,X2,X3,X4,X5,X6) != X0
            & sK1(X0,X1,X2,X3,X4,X5,X6) != X1
            & sK1(X0,X1,X2,X3,X4,X5,X6) != X2
            & sK1(X0,X1,X2,X3,X4,X5,X6) != X3
            & sK1(X0,X1,X2,X3,X4,X5,X6) != X4
            & sK1(X0,X1,X2,X3,X4,X5,X6) != X5 )
          | ~ r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6),X6) )
        & ( sK1(X0,X1,X2,X3,X4,X5,X6) = X0
          | sK1(X0,X1,X2,X3,X4,X5,X6) = X1
          | sK1(X0,X1,X2,X3,X4,X5,X6) = X2
          | sK1(X0,X1,X2,X3,X4,X5,X6) = X3
          | sK1(X0,X1,X2,X3,X4,X5,X6) = X4
          | sK1(X0,X1,X2,X3,X4,X5,X6) = X5
          | r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6),X6) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( sP0(X0,X1,X2,X3,X4,X5,X6)
        | ( ( ( sK1(X0,X1,X2,X3,X4,X5,X6) != X0
              & sK1(X0,X1,X2,X3,X4,X5,X6) != X1
              & sK1(X0,X1,X2,X3,X4,X5,X6) != X2
              & sK1(X0,X1,X2,X3,X4,X5,X6) != X3
              & sK1(X0,X1,X2,X3,X4,X5,X6) != X4
              & sK1(X0,X1,X2,X3,X4,X5,X6) != X5 )
            | ~ r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6),X6) )
          & ( sK1(X0,X1,X2,X3,X4,X5,X6) = X0
            | sK1(X0,X1,X2,X3,X4,X5,X6) = X1
            | sK1(X0,X1,X2,X3,X4,X5,X6) = X2
            | sK1(X0,X1,X2,X3,X4,X5,X6) = X3
            | sK1(X0,X1,X2,X3,X4,X5,X6) = X4
            | sK1(X0,X1,X2,X3,X4,X5,X6) = X5
            | r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6),X6) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X6)
              | ( X0 != X8
                & X1 != X8
                & X2 != X8
                & X3 != X8
                & X4 != X8
                & X5 != X8 ) )
            & ( X0 = X8
              | X1 = X8
              | X2 = X8
              | X3 = X8
              | X4 = X8
              | X5 = X8
              | ~ r2_hidden(X8,X6) ) )
        | ~ sP0(X0,X1,X2,X3,X4,X5,X6) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f38,f39])).

fof(f58,plain,(
    ! [X6,X4,X2,X0,X8,X5,X3,X1] :
      ( r2_hidden(X8,X6)
      | X0 != X8
      | ~ sP0(X0,X1,X2,X3,X4,X5,X6) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f102,plain,(
    ! [X6,X4,X2,X8,X5,X3,X1] :
      ( r2_hidden(X8,X6)
      | ~ sP0(X8,X1,X2,X3,X4,X5,X6) ) ),
    inference(equality_resolution,[],[f58])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f98,plain,(
    ! [X0,X1] :
      ( k6_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f71,f94])).

cnf(c_35,negated_conjecture,
    ( v1_funct_2(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_29,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_465,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_34])).

cnf(c_466,plain,
    ( ~ v1_funct_2(sK4,X0,X1)
    | k1_relset_1(X0,X1,sK4) = X0
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_465])).

cnf(c_743,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != X0
    | k1_relset_1(X0,X1,sK4) = X0
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK3 != X1
    | sK4 != sK4
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_35,c_466])).

cnf(c_744,plain,
    ( k1_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK4) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_743])).

cnf(c_33,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_745,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))
    | k1_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK4) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_744,c_33])).

cnf(c_746,plain,
    ( k1_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK4) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) ),
    inference(renaming,[status(thm)],[c_745])).

cnf(c_3111,plain,
    ( k1_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK4) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(equality_resolution_simp,[status(thm)],[c_746])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_528,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_34])).

cnf(c_529,plain,
    ( k1_relset_1(X0,X1,sK4) = k1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_528])).

cnf(c_8447,plain,
    ( k1_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK4) = k1_relat_1(sK4) ),
    inference(equality_resolution,[status(thm)],[c_529])).

cnf(c_8945,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k1_relat_1(sK4) ),
    inference(light_normalisation,[status(thm)],[c_3111,c_8447])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,k8_relset_1(X1,X2,X0,X2)) = k2_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_501,plain,
    ( k7_relset_1(X0,X1,X2,k8_relset_1(X0,X1,X2,X1)) = k2_relset_1(X0,X1,X2)
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_34])).

cnf(c_502,plain,
    ( k7_relset_1(X0,X1,sK4,k8_relset_1(X0,X1,sK4,X1)) = k2_relset_1(X0,X1,sK4)
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_501])).

cnf(c_8953,plain,
    ( k7_relset_1(X0,X1,sK4,k8_relset_1(X0,X1,sK4,X1)) = k2_relset_1(X0,X1,sK4)
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_8945,c_502])).

cnf(c_9876,plain,
    ( k7_relset_1(k1_relat_1(sK4),sK3,sK4,k8_relset_1(k1_relat_1(sK4),sK3,sK4,sK3)) = k2_relset_1(k1_relat_1(sK4),sK3,sK4) ),
    inference(equality_resolution,[status(thm)],[c_8953])).

cnf(c_31,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k8_relset_1(X1,X2,X0,X2) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_404,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X2) = X1
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_36])).

cnf(c_405,plain,
    ( ~ v1_funct_2(sK4,X0,X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k8_relset_1(X0,X1,sK4,X1) = X0
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_404])).

cnf(c_602,plain,
    ( ~ v1_funct_2(sK4,X0,X1)
    | k8_relset_1(X0,X1,sK4,X1) = X0
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK4 != sK4
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_405])).

cnf(c_733,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != X0
    | k8_relset_1(X0,X1,sK4,X1) = X0
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK3 != X1
    | sK4 != sK4
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_35,c_602])).

cnf(c_734,plain,
    ( k8_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK4,sK3) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_733])).

cnf(c_735,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))
    | k8_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK4,sK3) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_734,c_33])).

cnf(c_736,plain,
    ( k8_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK4,sK3) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) ),
    inference(renaming,[status(thm)],[c_735])).

cnf(c_3112,plain,
    ( k8_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK4,sK3) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(equality_resolution_simp,[status(thm)],[c_736])).

cnf(c_9437,plain,
    ( k8_relset_1(k1_relat_1(sK4),sK3,sK4,sK3) = k1_relat_1(sK4) ),
    inference(light_normalisation,[status(thm)],[c_3112,c_8945])).

cnf(c_9877,plain,
    ( k7_relset_1(k1_relat_1(sK4),sK3,sK4,k1_relat_1(sK4)) = k2_relset_1(k1_relat_1(sK4),sK3,sK4) ),
    inference(light_normalisation,[status(thm)],[c_9876,c_9437])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_519,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_34])).

cnf(c_520,plain,
    ( k7_relset_1(X0,X1,sK4,X2) = k9_relat_1(sK4,X2)
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_519])).

cnf(c_8450,plain,
    ( k7_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK4,X0) = k9_relat_1(sK4,X0) ),
    inference(equality_resolution,[status(thm)],[c_520])).

cnf(c_8947,plain,
    ( k7_relset_1(k1_relat_1(sK4),sK3,sK4,X0) = k9_relat_1(sK4,X0) ),
    inference(demodulation,[status(thm)],[c_8945,c_8450])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_450,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_34])).

cnf(c_451,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_450])).

cnf(c_8187,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(X0)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_451])).

cnf(c_7820,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_8431,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) = k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) ),
    inference(instantiation,[status(thm)],[c_7820])).

cnf(c_8426,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_451])).

cnf(c_8751,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))
    | v1_relat_1(sK4)
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) ),
    inference(instantiation,[status(thm)],[c_8426])).

cnf(c_8752,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))
    | v1_relat_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8751])).

cnf(c_18,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_9439,plain,
    ( v1_relat_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_9440,plain,
    ( v1_relat_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9439])).

cnf(c_9879,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8187,c_8431,c_8752,c_9440])).

cnf(c_17,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = k11_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_8190,plain,
    ( k9_relat_1(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = k11_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_10414,plain,
    ( k9_relat_1(sK4,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k11_relat_1(sK4,X0) ),
    inference(superposition,[status(thm)],[c_9879,c_8190])).

cnf(c_10889,plain,
    ( k9_relat_1(sK4,k1_relat_1(sK4)) = k11_relat_1(sK4,sK2) ),
    inference(superposition,[status(thm)],[c_8945,c_10414])).

cnf(c_11205,plain,
    ( k2_relset_1(k1_relat_1(sK4),sK3,sK4) = k11_relat_1(sK4,sK2) ),
    inference(demodulation,[status(thm)],[c_9877,c_8947,c_10889])).

cnf(c_32,negated_conjecture,
    ( k6_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) != k2_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK4) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_8956,plain,
    ( k6_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) != k2_relset_1(k1_relat_1(sK4),sK3,sK4) ),
    inference(demodulation,[status(thm)],[c_8945,c_32])).

cnf(c_11207,plain,
    ( k6_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) != k11_relat_1(sK4,sK2) ),
    inference(demodulation,[status(thm)],[c_11205,c_8956])).

cnf(c_15,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,k6_enumset1(X5,X5,X5,X4,X3,X2,X1,X0)) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_8191,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,k6_enumset1(X5,X5,X5,X4,X3,X2,X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_9618,plain,
    ( sP0(sK2,sK2,sK2,sK2,sK2,sK2,k1_relat_1(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8945,c_8191])).

cnf(c_7,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,X6)
    | r2_hidden(X0,X6) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k6_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_389,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k6_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_36])).

cnf(c_390,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | k6_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0) ),
    inference(unflattening,[status(thm)],[c_389])).

cnf(c_1576,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,X6)
    | ~ v1_relat_1(sK4)
    | X7 != X0
    | k6_enumset1(k1_funct_1(sK4,X7),k1_funct_1(sK4,X7),k1_funct_1(sK4,X7),k1_funct_1(sK4,X7),k1_funct_1(sK4,X7),k1_funct_1(sK4,X7),k1_funct_1(sK4,X7),k1_funct_1(sK4,X7)) = k11_relat_1(sK4,X7)
    | k1_relat_1(sK4) != X6 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_390])).

cnf(c_1577,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | k6_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0) ),
    inference(unflattening,[status(thm)],[c_1576])).

cnf(c_1578,plain,
    ( k6_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0)
    | sP0(X0,X1,X2,X3,X4,X5,k1_relat_1(sK4)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1577])).

cnf(c_1580,plain,
    ( k6_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) = k11_relat_1(sK4,sK2)
    | sP0(sK2,sK2,sK2,sK2,sK2,sK2,k1_relat_1(sK4)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1578])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11207,c_9618,c_9440,c_8752,c_8431,c_1580])).

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
% 0.13/0.33  % DateTime   : Tue Dec  1 21:07:15 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.22/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.22/0.98  
% 3.22/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.22/0.98  
% 3.22/0.98  ------  iProver source info
% 3.22/0.98  
% 3.22/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.22/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.22/0.98  git: non_committed_changes: false
% 3.22/0.98  git: last_make_outside_of_git: false
% 3.22/0.98  
% 3.22/0.98  ------ 
% 3.22/0.98  
% 3.22/0.98  ------ Input Options
% 3.22/0.98  
% 3.22/0.98  --out_options                           all
% 3.22/0.98  --tptp_safe_out                         true
% 3.22/0.98  --problem_path                          ""
% 3.22/0.98  --include_path                          ""
% 3.22/0.98  --clausifier                            res/vclausify_rel
% 3.22/0.98  --clausifier_options                    --mode clausify
% 3.22/0.98  --stdin                                 false
% 3.22/0.98  --stats_out                             all
% 3.22/0.98  
% 3.22/0.98  ------ General Options
% 3.22/0.98  
% 3.22/0.98  --fof                                   false
% 3.22/0.98  --time_out_real                         305.
% 3.22/0.98  --time_out_virtual                      -1.
% 3.22/0.98  --symbol_type_check                     false
% 3.22/0.98  --clausify_out                          false
% 3.22/0.98  --sig_cnt_out                           false
% 3.22/0.98  --trig_cnt_out                          false
% 3.22/0.98  --trig_cnt_out_tolerance                1.
% 3.22/0.98  --trig_cnt_out_sk_spl                   false
% 3.22/0.98  --abstr_cl_out                          false
% 3.22/0.98  
% 3.22/0.98  ------ Global Options
% 3.22/0.98  
% 3.22/0.98  --schedule                              default
% 3.22/0.98  --add_important_lit                     false
% 3.22/0.98  --prop_solver_per_cl                    1000
% 3.22/0.98  --min_unsat_core                        false
% 3.22/0.98  --soft_assumptions                      false
% 3.22/0.98  --soft_lemma_size                       3
% 3.22/0.98  --prop_impl_unit_size                   0
% 3.22/0.98  --prop_impl_unit                        []
% 3.22/0.98  --share_sel_clauses                     true
% 3.22/0.98  --reset_solvers                         false
% 3.22/0.98  --bc_imp_inh                            [conj_cone]
% 3.22/0.98  --conj_cone_tolerance                   3.
% 3.22/0.98  --extra_neg_conj                        none
% 3.22/0.98  --large_theory_mode                     true
% 3.22/0.98  --prolific_symb_bound                   200
% 3.22/0.98  --lt_threshold                          2000
% 3.22/0.98  --clause_weak_htbl                      true
% 3.22/0.98  --gc_record_bc_elim                     false
% 3.22/0.98  
% 3.22/0.98  ------ Preprocessing Options
% 3.22/0.98  
% 3.22/0.98  --preprocessing_flag                    true
% 3.22/0.98  --time_out_prep_mult                    0.1
% 3.22/0.98  --splitting_mode                        input
% 3.22/0.98  --splitting_grd                         true
% 3.22/0.98  --splitting_cvd                         false
% 3.22/0.98  --splitting_cvd_svl                     false
% 3.22/0.98  --splitting_nvd                         32
% 3.22/0.98  --sub_typing                            true
% 3.22/0.98  --prep_gs_sim                           true
% 3.22/0.98  --prep_unflatten                        true
% 3.22/0.98  --prep_res_sim                          true
% 3.22/0.98  --prep_upred                            true
% 3.22/0.98  --prep_sem_filter                       exhaustive
% 3.22/0.98  --prep_sem_filter_out                   false
% 3.22/0.98  --pred_elim                             true
% 3.22/0.98  --res_sim_input                         true
% 3.22/0.98  --eq_ax_congr_red                       true
% 3.22/0.98  --pure_diseq_elim                       true
% 3.22/0.98  --brand_transform                       false
% 3.22/0.98  --non_eq_to_eq                          false
% 3.22/0.98  --prep_def_merge                        true
% 3.22/0.98  --prep_def_merge_prop_impl              false
% 3.22/0.98  --prep_def_merge_mbd                    true
% 3.22/0.98  --prep_def_merge_tr_red                 false
% 3.22/0.98  --prep_def_merge_tr_cl                  false
% 3.22/0.98  --smt_preprocessing                     true
% 3.22/0.98  --smt_ac_axioms                         fast
% 3.22/0.98  --preprocessed_out                      false
% 3.22/0.98  --preprocessed_stats                    false
% 3.22/0.98  
% 3.22/0.98  ------ Abstraction refinement Options
% 3.22/0.98  
% 3.22/0.98  --abstr_ref                             []
% 3.22/0.98  --abstr_ref_prep                        false
% 3.22/0.98  --abstr_ref_until_sat                   false
% 3.22/0.98  --abstr_ref_sig_restrict                funpre
% 3.22/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.22/0.98  --abstr_ref_under                       []
% 3.22/0.98  
% 3.22/0.98  ------ SAT Options
% 3.22/0.98  
% 3.22/0.98  --sat_mode                              false
% 3.22/0.98  --sat_fm_restart_options                ""
% 3.22/0.98  --sat_gr_def                            false
% 3.22/0.98  --sat_epr_types                         true
% 3.22/0.98  --sat_non_cyclic_types                  false
% 3.22/0.98  --sat_finite_models                     false
% 3.22/0.98  --sat_fm_lemmas                         false
% 3.22/0.98  --sat_fm_prep                           false
% 3.22/0.98  --sat_fm_uc_incr                        true
% 3.22/0.98  --sat_out_model                         small
% 3.22/0.98  --sat_out_clauses                       false
% 3.22/0.98  
% 3.22/0.98  ------ QBF Options
% 3.22/0.98  
% 3.22/0.98  --qbf_mode                              false
% 3.22/0.98  --qbf_elim_univ                         false
% 3.22/0.98  --qbf_dom_inst                          none
% 3.22/0.98  --qbf_dom_pre_inst                      false
% 3.22/0.98  --qbf_sk_in                             false
% 3.22/0.98  --qbf_pred_elim                         true
% 3.22/0.98  --qbf_split                             512
% 3.22/0.98  
% 3.22/0.98  ------ BMC1 Options
% 3.22/0.98  
% 3.22/0.98  --bmc1_incremental                      false
% 3.22/0.98  --bmc1_axioms                           reachable_all
% 3.22/0.98  --bmc1_min_bound                        0
% 3.22/0.98  --bmc1_max_bound                        -1
% 3.22/0.98  --bmc1_max_bound_default                -1
% 3.22/0.98  --bmc1_symbol_reachability              true
% 3.22/0.98  --bmc1_property_lemmas                  false
% 3.22/0.98  --bmc1_k_induction                      false
% 3.22/0.98  --bmc1_non_equiv_states                 false
% 3.22/0.98  --bmc1_deadlock                         false
% 3.22/0.98  --bmc1_ucm                              false
% 3.22/0.98  --bmc1_add_unsat_core                   none
% 3.22/0.98  --bmc1_unsat_core_children              false
% 3.22/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.22/0.98  --bmc1_out_stat                         full
% 3.22/0.98  --bmc1_ground_init                      false
% 3.22/0.98  --bmc1_pre_inst_next_state              false
% 3.22/0.98  --bmc1_pre_inst_state                   false
% 3.22/0.98  --bmc1_pre_inst_reach_state             false
% 3.22/0.98  --bmc1_out_unsat_core                   false
% 3.22/0.98  --bmc1_aig_witness_out                  false
% 3.22/0.98  --bmc1_verbose                          false
% 3.22/0.98  --bmc1_dump_clauses_tptp                false
% 3.22/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.22/0.98  --bmc1_dump_file                        -
% 3.22/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.22/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.22/0.98  --bmc1_ucm_extend_mode                  1
% 3.22/0.98  --bmc1_ucm_init_mode                    2
% 3.22/0.98  --bmc1_ucm_cone_mode                    none
% 3.22/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.22/0.98  --bmc1_ucm_relax_model                  4
% 3.22/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.22/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.22/0.98  --bmc1_ucm_layered_model                none
% 3.22/0.98  --bmc1_ucm_max_lemma_size               10
% 3.22/0.98  
% 3.22/0.98  ------ AIG Options
% 3.22/0.98  
% 3.22/0.98  --aig_mode                              false
% 3.22/0.98  
% 3.22/0.98  ------ Instantiation Options
% 3.22/0.98  
% 3.22/0.98  --instantiation_flag                    true
% 3.22/0.98  --inst_sos_flag                         false
% 3.22/0.98  --inst_sos_phase                        true
% 3.22/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.22/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.22/0.98  --inst_lit_sel_side                     num_symb
% 3.22/0.98  --inst_solver_per_active                1400
% 3.22/0.98  --inst_solver_calls_frac                1.
% 3.22/0.98  --inst_passive_queue_type               priority_queues
% 3.22/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.22/0.98  --inst_passive_queues_freq              [25;2]
% 3.22/0.98  --inst_dismatching                      true
% 3.22/0.98  --inst_eager_unprocessed_to_passive     true
% 3.22/0.98  --inst_prop_sim_given                   true
% 3.22/0.98  --inst_prop_sim_new                     false
% 3.22/0.98  --inst_subs_new                         false
% 3.22/0.98  --inst_eq_res_simp                      false
% 3.22/0.98  --inst_subs_given                       false
% 3.22/0.98  --inst_orphan_elimination               true
% 3.22/0.98  --inst_learning_loop_flag               true
% 3.22/0.98  --inst_learning_start                   3000
% 3.22/0.98  --inst_learning_factor                  2
% 3.22/0.98  --inst_start_prop_sim_after_learn       3
% 3.22/0.98  --inst_sel_renew                        solver
% 3.22/0.98  --inst_lit_activity_flag                true
% 3.22/0.98  --inst_restr_to_given                   false
% 3.22/0.98  --inst_activity_threshold               500
% 3.22/0.98  --inst_out_proof                        true
% 3.22/0.98  
% 3.22/0.98  ------ Resolution Options
% 3.22/0.98  
% 3.22/0.98  --resolution_flag                       true
% 3.22/0.98  --res_lit_sel                           adaptive
% 3.22/0.98  --res_lit_sel_side                      none
% 3.22/0.98  --res_ordering                          kbo
% 3.22/0.98  --res_to_prop_solver                    active
% 3.22/0.98  --res_prop_simpl_new                    false
% 3.22/0.98  --res_prop_simpl_given                  true
% 3.22/0.98  --res_passive_queue_type                priority_queues
% 3.22/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.22/0.98  --res_passive_queues_freq               [15;5]
% 3.22/0.98  --res_forward_subs                      full
% 3.22/0.98  --res_backward_subs                     full
% 3.22/0.98  --res_forward_subs_resolution           true
% 3.22/0.98  --res_backward_subs_resolution          true
% 3.22/0.98  --res_orphan_elimination                true
% 3.22/0.98  --res_time_limit                        2.
% 3.22/0.98  --res_out_proof                         true
% 3.22/0.98  
% 3.22/0.98  ------ Superposition Options
% 3.22/0.98  
% 3.22/0.98  --superposition_flag                    true
% 3.22/0.98  --sup_passive_queue_type                priority_queues
% 3.22/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.22/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.22/0.98  --demod_completeness_check              fast
% 3.22/0.98  --demod_use_ground                      true
% 3.22/0.98  --sup_to_prop_solver                    passive
% 3.22/0.98  --sup_prop_simpl_new                    true
% 3.22/0.98  --sup_prop_simpl_given                  true
% 3.22/0.98  --sup_fun_splitting                     false
% 3.22/0.98  --sup_smt_interval                      50000
% 3.22/0.98  
% 3.22/0.98  ------ Superposition Simplification Setup
% 3.22/0.98  
% 3.22/0.98  --sup_indices_passive                   []
% 3.22/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.22/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.22/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.22/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.22/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.22/0.98  --sup_full_bw                           [BwDemod]
% 3.22/0.98  --sup_immed_triv                        [TrivRules]
% 3.22/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.22/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.22/0.98  --sup_immed_bw_main                     []
% 3.22/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.22/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.22/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.22/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.22/0.98  
% 3.22/0.98  ------ Combination Options
% 3.22/0.98  
% 3.22/0.98  --comb_res_mult                         3
% 3.22/0.98  --comb_sup_mult                         2
% 3.22/0.98  --comb_inst_mult                        10
% 3.22/0.98  
% 3.22/0.98  ------ Debug Options
% 3.22/0.98  
% 3.22/0.98  --dbg_backtrace                         false
% 3.22/0.98  --dbg_dump_prop_clauses                 false
% 3.22/0.98  --dbg_dump_prop_clauses_file            -
% 3.22/0.98  --dbg_out_stat                          false
% 3.22/0.98  ------ Parsing...
% 3.22/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.22/0.98  
% 3.22/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.22/0.98  
% 3.22/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.22/0.98  
% 3.22/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.22/0.98  ------ Proving...
% 3.22/0.98  ------ Problem Properties 
% 3.22/0.98  
% 3.22/0.98  
% 3.22/0.98  clauses                                 33
% 3.22/0.98  conjectures                             2
% 3.22/0.98  EPR                                     8
% 3.22/0.98  Horn                                    29
% 3.22/0.98  unary                                   6
% 3.22/0.98  binary                                  12
% 3.22/0.98  lits                                    87
% 3.22/0.98  lits eq                                 51
% 3.22/0.98  fd_pure                                 0
% 3.22/0.98  fd_pseudo                               0
% 3.22/0.98  fd_cond                                 0
% 3.22/0.98  fd_pseudo_cond                          2
% 3.22/0.98  AC symbols                              0
% 3.22/0.98  
% 3.22/0.98  ------ Schedule dynamic 5 is on 
% 3.22/0.98  
% 3.22/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.22/0.98  
% 3.22/0.98  
% 3.22/0.98  ------ 
% 3.22/0.98  Current options:
% 3.22/0.98  ------ 
% 3.22/0.98  
% 3.22/0.98  ------ Input Options
% 3.22/0.98  
% 3.22/0.98  --out_options                           all
% 3.22/0.98  --tptp_safe_out                         true
% 3.22/0.98  --problem_path                          ""
% 3.22/0.98  --include_path                          ""
% 3.22/0.98  --clausifier                            res/vclausify_rel
% 3.22/0.98  --clausifier_options                    --mode clausify
% 3.22/0.98  --stdin                                 false
% 3.22/0.98  --stats_out                             all
% 3.22/0.98  
% 3.22/0.98  ------ General Options
% 3.22/0.98  
% 3.22/0.98  --fof                                   false
% 3.22/0.98  --time_out_real                         305.
% 3.22/0.98  --time_out_virtual                      -1.
% 3.22/0.98  --symbol_type_check                     false
% 3.22/0.98  --clausify_out                          false
% 3.22/0.98  --sig_cnt_out                           false
% 3.22/0.98  --trig_cnt_out                          false
% 3.22/0.98  --trig_cnt_out_tolerance                1.
% 3.22/0.98  --trig_cnt_out_sk_spl                   false
% 3.22/0.98  --abstr_cl_out                          false
% 3.22/0.98  
% 3.22/0.98  ------ Global Options
% 3.22/0.98  
% 3.22/0.98  --schedule                              default
% 3.22/0.98  --add_important_lit                     false
% 3.22/0.98  --prop_solver_per_cl                    1000
% 3.22/0.98  --min_unsat_core                        false
% 3.22/0.98  --soft_assumptions                      false
% 3.22/0.98  --soft_lemma_size                       3
% 3.22/0.98  --prop_impl_unit_size                   0
% 3.22/0.98  --prop_impl_unit                        []
% 3.22/0.98  --share_sel_clauses                     true
% 3.22/0.98  --reset_solvers                         false
% 3.22/0.98  --bc_imp_inh                            [conj_cone]
% 3.22/0.98  --conj_cone_tolerance                   3.
% 3.22/0.98  --extra_neg_conj                        none
% 3.22/0.98  --large_theory_mode                     true
% 3.22/0.98  --prolific_symb_bound                   200
% 3.22/0.98  --lt_threshold                          2000
% 3.22/0.98  --clause_weak_htbl                      true
% 3.22/0.98  --gc_record_bc_elim                     false
% 3.22/0.98  
% 3.22/0.98  ------ Preprocessing Options
% 3.22/0.98  
% 3.22/0.98  --preprocessing_flag                    true
% 3.22/0.98  --time_out_prep_mult                    0.1
% 3.22/0.98  --splitting_mode                        input
% 3.22/0.98  --splitting_grd                         true
% 3.22/0.98  --splitting_cvd                         false
% 3.22/0.98  --splitting_cvd_svl                     false
% 3.22/0.98  --splitting_nvd                         32
% 3.22/0.98  --sub_typing                            true
% 3.22/0.98  --prep_gs_sim                           true
% 3.22/0.98  --prep_unflatten                        true
% 3.22/0.98  --prep_res_sim                          true
% 3.22/0.98  --prep_upred                            true
% 3.22/0.98  --prep_sem_filter                       exhaustive
% 3.22/0.98  --prep_sem_filter_out                   false
% 3.22/0.98  --pred_elim                             true
% 3.22/0.98  --res_sim_input                         true
% 3.22/0.98  --eq_ax_congr_red                       true
% 3.22/0.98  --pure_diseq_elim                       true
% 3.22/0.98  --brand_transform                       false
% 3.22/0.98  --non_eq_to_eq                          false
% 3.22/0.98  --prep_def_merge                        true
% 3.22/0.98  --prep_def_merge_prop_impl              false
% 3.22/0.98  --prep_def_merge_mbd                    true
% 3.22/0.98  --prep_def_merge_tr_red                 false
% 3.22/0.98  --prep_def_merge_tr_cl                  false
% 3.22/0.98  --smt_preprocessing                     true
% 3.22/0.98  --smt_ac_axioms                         fast
% 3.22/0.98  --preprocessed_out                      false
% 3.22/0.98  --preprocessed_stats                    false
% 3.22/0.98  
% 3.22/0.98  ------ Abstraction refinement Options
% 3.22/0.98  
% 3.22/0.98  --abstr_ref                             []
% 3.22/0.98  --abstr_ref_prep                        false
% 3.22/0.98  --abstr_ref_until_sat                   false
% 3.22/0.98  --abstr_ref_sig_restrict                funpre
% 3.22/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.22/0.98  --abstr_ref_under                       []
% 3.22/0.98  
% 3.22/0.98  ------ SAT Options
% 3.22/0.98  
% 3.22/0.98  --sat_mode                              false
% 3.22/0.98  --sat_fm_restart_options                ""
% 3.22/0.98  --sat_gr_def                            false
% 3.22/0.98  --sat_epr_types                         true
% 3.22/0.98  --sat_non_cyclic_types                  false
% 3.22/0.98  --sat_finite_models                     false
% 3.22/0.98  --sat_fm_lemmas                         false
% 3.22/0.98  --sat_fm_prep                           false
% 3.22/0.98  --sat_fm_uc_incr                        true
% 3.22/0.98  --sat_out_model                         small
% 3.22/0.98  --sat_out_clauses                       false
% 3.22/0.98  
% 3.22/0.98  ------ QBF Options
% 3.22/0.98  
% 3.22/0.98  --qbf_mode                              false
% 3.22/0.98  --qbf_elim_univ                         false
% 3.22/0.98  --qbf_dom_inst                          none
% 3.22/0.98  --qbf_dom_pre_inst                      false
% 3.22/0.98  --qbf_sk_in                             false
% 3.22/0.98  --qbf_pred_elim                         true
% 3.22/0.98  --qbf_split                             512
% 3.22/0.98  
% 3.22/0.98  ------ BMC1 Options
% 3.22/0.98  
% 3.22/0.98  --bmc1_incremental                      false
% 3.22/0.98  --bmc1_axioms                           reachable_all
% 3.22/0.98  --bmc1_min_bound                        0
% 3.22/0.98  --bmc1_max_bound                        -1
% 3.22/0.98  --bmc1_max_bound_default                -1
% 3.22/0.98  --bmc1_symbol_reachability              true
% 3.22/0.98  --bmc1_property_lemmas                  false
% 3.22/0.98  --bmc1_k_induction                      false
% 3.22/0.98  --bmc1_non_equiv_states                 false
% 3.22/0.98  --bmc1_deadlock                         false
% 3.22/0.98  --bmc1_ucm                              false
% 3.22/0.98  --bmc1_add_unsat_core                   none
% 3.22/0.98  --bmc1_unsat_core_children              false
% 3.22/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.22/0.98  --bmc1_out_stat                         full
% 3.22/0.98  --bmc1_ground_init                      false
% 3.22/0.98  --bmc1_pre_inst_next_state              false
% 3.22/0.98  --bmc1_pre_inst_state                   false
% 3.22/0.98  --bmc1_pre_inst_reach_state             false
% 3.22/0.98  --bmc1_out_unsat_core                   false
% 3.22/0.98  --bmc1_aig_witness_out                  false
% 3.22/0.98  --bmc1_verbose                          false
% 3.22/0.98  --bmc1_dump_clauses_tptp                false
% 3.22/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.22/0.98  --bmc1_dump_file                        -
% 3.22/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.22/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.22/0.98  --bmc1_ucm_extend_mode                  1
% 3.22/0.98  --bmc1_ucm_init_mode                    2
% 3.22/0.98  --bmc1_ucm_cone_mode                    none
% 3.22/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.22/0.98  --bmc1_ucm_relax_model                  4
% 3.22/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.22/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.22/0.98  --bmc1_ucm_layered_model                none
% 3.22/0.98  --bmc1_ucm_max_lemma_size               10
% 3.22/0.98  
% 3.22/0.98  ------ AIG Options
% 3.22/0.98  
% 3.22/0.98  --aig_mode                              false
% 3.22/0.98  
% 3.22/0.98  ------ Instantiation Options
% 3.22/0.98  
% 3.22/0.98  --instantiation_flag                    true
% 3.22/0.98  --inst_sos_flag                         false
% 3.22/0.98  --inst_sos_phase                        true
% 3.22/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.22/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.22/0.98  --inst_lit_sel_side                     none
% 3.22/0.98  --inst_solver_per_active                1400
% 3.22/0.98  --inst_solver_calls_frac                1.
% 3.22/0.98  --inst_passive_queue_type               priority_queues
% 3.22/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.22/0.98  --inst_passive_queues_freq              [25;2]
% 3.22/0.98  --inst_dismatching                      true
% 3.22/0.98  --inst_eager_unprocessed_to_passive     true
% 3.22/0.98  --inst_prop_sim_given                   true
% 3.22/0.98  --inst_prop_sim_new                     false
% 3.22/0.98  --inst_subs_new                         false
% 3.22/0.98  --inst_eq_res_simp                      false
% 3.22/0.98  --inst_subs_given                       false
% 3.22/0.98  --inst_orphan_elimination               true
% 3.22/0.98  --inst_learning_loop_flag               true
% 3.22/0.98  --inst_learning_start                   3000
% 3.22/0.98  --inst_learning_factor                  2
% 3.22/0.98  --inst_start_prop_sim_after_learn       3
% 3.22/0.98  --inst_sel_renew                        solver
% 3.22/0.98  --inst_lit_activity_flag                true
% 3.22/0.98  --inst_restr_to_given                   false
% 3.22/0.98  --inst_activity_threshold               500
% 3.22/0.98  --inst_out_proof                        true
% 3.22/0.98  
% 3.22/0.98  ------ Resolution Options
% 3.22/0.98  
% 3.22/0.98  --resolution_flag                       false
% 3.22/0.98  --res_lit_sel                           adaptive
% 3.22/0.98  --res_lit_sel_side                      none
% 3.22/0.98  --res_ordering                          kbo
% 3.22/0.98  --res_to_prop_solver                    active
% 3.22/0.98  --res_prop_simpl_new                    false
% 3.22/0.98  --res_prop_simpl_given                  true
% 3.22/0.98  --res_passive_queue_type                priority_queues
% 3.22/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.22/0.98  --res_passive_queues_freq               [15;5]
% 3.22/0.98  --res_forward_subs                      full
% 3.22/0.98  --res_backward_subs                     full
% 3.22/0.98  --res_forward_subs_resolution           true
% 3.22/0.98  --res_backward_subs_resolution          true
% 3.22/0.98  --res_orphan_elimination                true
% 3.22/0.98  --res_time_limit                        2.
% 3.22/0.98  --res_out_proof                         true
% 3.22/0.98  
% 3.22/0.98  ------ Superposition Options
% 3.22/0.98  
% 3.22/0.98  --superposition_flag                    true
% 3.22/0.98  --sup_passive_queue_type                priority_queues
% 3.22/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.22/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.22/0.98  --demod_completeness_check              fast
% 3.22/0.98  --demod_use_ground                      true
% 3.22/0.98  --sup_to_prop_solver                    passive
% 3.22/0.98  --sup_prop_simpl_new                    true
% 3.22/0.98  --sup_prop_simpl_given                  true
% 3.22/0.98  --sup_fun_splitting                     false
% 3.22/0.98  --sup_smt_interval                      50000
% 3.22/0.98  
% 3.22/0.98  ------ Superposition Simplification Setup
% 3.22/0.98  
% 3.22/0.98  --sup_indices_passive                   []
% 3.22/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.22/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.22/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.22/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.22/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.22/0.98  --sup_full_bw                           [BwDemod]
% 3.22/0.98  --sup_immed_triv                        [TrivRules]
% 3.22/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.22/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.22/0.98  --sup_immed_bw_main                     []
% 3.22/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.22/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.22/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.22/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.22/0.98  
% 3.22/0.98  ------ Combination Options
% 3.22/0.98  
% 3.22/0.98  --comb_res_mult                         3
% 3.22/0.98  --comb_sup_mult                         2
% 3.22/0.98  --comb_inst_mult                        10
% 3.22/0.98  
% 3.22/0.98  ------ Debug Options
% 3.22/0.98  
% 3.22/0.98  --dbg_backtrace                         false
% 3.22/0.98  --dbg_dump_prop_clauses                 false
% 3.22/0.98  --dbg_dump_prop_clauses_file            -
% 3.22/0.98  --dbg_out_stat                          false
% 3.22/0.98  
% 3.22/0.98  
% 3.22/0.98  
% 3.22/0.98  
% 3.22/0.98  ------ Proving...
% 3.22/0.98  
% 3.22/0.98  
% 3.22/0.98  % SZS status Theorem for theBenchmark.p
% 3.22/0.98  
% 3.22/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.22/0.98  
% 3.22/0.98  fof(f18,conjecture,(
% 3.22/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)))),
% 3.22/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/0.98  
% 3.22/0.98  fof(f19,negated_conjecture,(
% 3.22/0.98    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)))),
% 3.22/0.98    inference(negated_conjecture,[],[f18])).
% 3.22/0.98  
% 3.22/0.98  fof(f32,plain,(
% 3.22/0.98    ? [X0,X1,X2] : ((k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 3.22/0.98    inference(ennf_transformation,[],[f19])).
% 3.22/0.98  
% 3.22/0.98  fof(f33,plain,(
% 3.22/0.98    ? [X0,X1,X2] : (k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 3.22/0.98    inference(flattening,[],[f32])).
% 3.22/0.98  
% 3.22/0.98  fof(f43,plain,(
% 3.22/0.98    ? [X0,X1,X2] : (k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_tarski(k1_funct_1(sK4,sK2)) != k2_relset_1(k1_tarski(sK2),sK3,sK4) & k1_xboole_0 != sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) & v1_funct_2(sK4,k1_tarski(sK2),sK3) & v1_funct_1(sK4))),
% 3.22/0.98    introduced(choice_axiom,[])).
% 3.22/0.98  
% 3.22/0.98  fof(f44,plain,(
% 3.22/0.98    k1_tarski(k1_funct_1(sK4,sK2)) != k2_relset_1(k1_tarski(sK2),sK3,sK4) & k1_xboole_0 != sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) & v1_funct_2(sK4,k1_tarski(sK2),sK3) & v1_funct_1(sK4)),
% 3.22/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f33,f43])).
% 3.22/0.98  
% 3.22/0.98  fof(f85,plain,(
% 3.22/0.98    v1_funct_2(sK4,k1_tarski(sK2),sK3)),
% 3.22/0.98    inference(cnf_transformation,[],[f44])).
% 3.22/0.98  
% 3.22/0.98  fof(f1,axiom,(
% 3.22/0.98    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.22/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/0.98  
% 3.22/0.98  fof(f45,plain,(
% 3.22/0.98    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.22/0.98    inference(cnf_transformation,[],[f1])).
% 3.22/0.98  
% 3.22/0.98  fof(f2,axiom,(
% 3.22/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.22/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/0.98  
% 3.22/0.98  fof(f46,plain,(
% 3.22/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.22/0.98    inference(cnf_transformation,[],[f2])).
% 3.22/0.98  
% 3.22/0.98  fof(f3,axiom,(
% 3.22/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.22/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/0.98  
% 3.22/0.98  fof(f47,plain,(
% 3.22/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.22/0.98    inference(cnf_transformation,[],[f3])).
% 3.22/0.98  
% 3.22/0.98  fof(f4,axiom,(
% 3.22/0.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.22/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/0.98  
% 3.22/0.98  fof(f48,plain,(
% 3.22/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.22/0.98    inference(cnf_transformation,[],[f4])).
% 3.22/0.98  
% 3.22/0.98  fof(f5,axiom,(
% 3.22/0.98    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.22/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/0.98  
% 3.22/0.98  fof(f49,plain,(
% 3.22/0.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.22/0.98    inference(cnf_transformation,[],[f5])).
% 3.22/0.98  
% 3.22/0.98  fof(f6,axiom,(
% 3.22/0.98    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.22/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/0.98  
% 3.22/0.98  fof(f50,plain,(
% 3.22/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.22/0.98    inference(cnf_transformation,[],[f6])).
% 3.22/0.98  
% 3.22/0.98  fof(f7,axiom,(
% 3.22/0.98    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.22/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/0.98  
% 3.22/0.98  fof(f51,plain,(
% 3.22/0.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.22/0.98    inference(cnf_transformation,[],[f7])).
% 3.22/0.98  
% 3.22/0.98  fof(f89,plain,(
% 3.22/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.22/0.98    inference(definition_unfolding,[],[f50,f51])).
% 3.22/0.98  
% 3.22/0.98  fof(f90,plain,(
% 3.22/0.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.22/0.98    inference(definition_unfolding,[],[f49,f89])).
% 3.22/0.98  
% 3.22/0.98  fof(f91,plain,(
% 3.22/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.22/0.98    inference(definition_unfolding,[],[f48,f90])).
% 3.22/0.98  
% 3.22/0.98  fof(f92,plain,(
% 3.22/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.22/0.98    inference(definition_unfolding,[],[f47,f91])).
% 3.22/0.98  
% 3.22/0.98  fof(f93,plain,(
% 3.22/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.22/0.98    inference(definition_unfolding,[],[f46,f92])).
% 3.22/0.98  
% 3.22/0.98  fof(f94,plain,(
% 3.22/0.98    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.22/0.98    inference(definition_unfolding,[],[f45,f93])).
% 3.22/0.98  
% 3.22/0.98  fof(f101,plain,(
% 3.22/0.98    v1_funct_2(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)),
% 3.22/0.98    inference(definition_unfolding,[],[f85,f94])).
% 3.22/0.98  
% 3.22/0.98  fof(f16,axiom,(
% 3.22/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.22/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/0.98  
% 3.22/0.98  fof(f28,plain,(
% 3.22/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.22/0.98    inference(ennf_transformation,[],[f16])).
% 3.22/0.98  
% 3.22/0.98  fof(f29,plain,(
% 3.22/0.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.22/0.98    inference(flattening,[],[f28])).
% 3.22/0.98  
% 3.22/0.98  fof(f42,plain,(
% 3.22/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.22/0.98    inference(nnf_transformation,[],[f29])).
% 3.22/0.98  
% 3.22/0.98  fof(f76,plain,(
% 3.22/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.22/0.98    inference(cnf_transformation,[],[f42])).
% 3.22/0.98  
% 3.22/0.98  fof(f86,plain,(
% 3.22/0.98    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3)))),
% 3.22/0.98    inference(cnf_transformation,[],[f44])).
% 3.22/0.98  
% 3.22/0.98  fof(f100,plain,(
% 3.22/0.98    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)))),
% 3.22/0.98    inference(definition_unfolding,[],[f86,f94])).
% 3.22/0.98  
% 3.22/0.98  fof(f87,plain,(
% 3.22/0.98    k1_xboole_0 != sK3),
% 3.22/0.98    inference(cnf_transformation,[],[f44])).
% 3.22/0.98  
% 3.22/0.98  fof(f13,axiom,(
% 3.22/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.22/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/0.98  
% 3.22/0.98  fof(f25,plain,(
% 3.22/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.22/0.98    inference(ennf_transformation,[],[f13])).
% 3.22/0.98  
% 3.22/0.98  fof(f72,plain,(
% 3.22/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.22/0.98    inference(cnf_transformation,[],[f25])).
% 3.22/0.98  
% 3.22/0.98  fof(f15,axiom,(
% 3.22/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (k1_relset_1(X1,X0,X2) = k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2)))),
% 3.22/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/0.98  
% 3.22/0.98  fof(f27,plain,(
% 3.22/0.98    ! [X0,X1,X2] : ((k1_relset_1(X1,X0,X2) = k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 3.22/0.98    inference(ennf_transformation,[],[f15])).
% 3.22/0.98  
% 3.22/0.98  fof(f74,plain,(
% 3.22/0.98    ( ! [X2,X0,X1] : (k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 3.22/0.98    inference(cnf_transformation,[],[f27])).
% 3.22/0.98  
% 3.22/0.98  fof(f17,axiom,(
% 3.22/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,X1) = X0))),
% 3.22/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/0.98  
% 3.22/0.98  fof(f30,plain,(
% 3.22/0.98    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.22/0.98    inference(ennf_transformation,[],[f17])).
% 3.22/0.98  
% 3.22/0.98  fof(f31,plain,(
% 3.22/0.98    ! [X0,X1,X2] : (k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.22/0.98    inference(flattening,[],[f30])).
% 3.22/0.98  
% 3.22/0.98  fof(f82,plain,(
% 3.22/0.98    ( ! [X2,X0,X1] : (k8_relset_1(X0,X1,X2,X1) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.22/0.98    inference(cnf_transformation,[],[f31])).
% 3.22/0.98  
% 3.22/0.98  fof(f84,plain,(
% 3.22/0.98    v1_funct_1(sK4)),
% 3.22/0.98    inference(cnf_transformation,[],[f44])).
% 3.22/0.98  
% 3.22/0.98  fof(f14,axiom,(
% 3.22/0.98    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.22/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/0.98  
% 3.22/0.98  fof(f26,plain,(
% 3.22/0.98    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.22/0.98    inference(ennf_transformation,[],[f14])).
% 3.22/0.98  
% 3.22/0.98  fof(f73,plain,(
% 3.22/0.98    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.22/0.98    inference(cnf_transformation,[],[f26])).
% 3.22/0.98  
% 3.22/0.98  fof(f9,axiom,(
% 3.22/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.22/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/0.98  
% 3.22/0.98  fof(f21,plain,(
% 3.22/0.98    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.22/0.98    inference(ennf_transformation,[],[f9])).
% 3.22/0.98  
% 3.22/0.98  fof(f68,plain,(
% 3.22/0.98    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.22/0.98    inference(cnf_transformation,[],[f21])).
% 3.22/0.98  
% 3.22/0.98  fof(f11,axiom,(
% 3.22/0.98    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.22/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/0.98  
% 3.22/0.98  fof(f70,plain,(
% 3.22/0.98    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.22/0.98    inference(cnf_transformation,[],[f11])).
% 3.22/0.98  
% 3.22/0.98  fof(f10,axiom,(
% 3.22/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 3.22/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/0.98  
% 3.22/0.98  fof(f22,plain,(
% 3.22/0.98    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 3.22/0.98    inference(ennf_transformation,[],[f10])).
% 3.22/0.98  
% 3.22/0.98  fof(f69,plain,(
% 3.22/0.98    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 3.22/0.98    inference(cnf_transformation,[],[f22])).
% 3.22/0.98  
% 3.22/0.98  fof(f97,plain,(
% 3.22/0.98    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | ~v1_relat_1(X0)) )),
% 3.22/0.98    inference(definition_unfolding,[],[f69,f94])).
% 3.22/0.98  
% 3.22/0.98  fof(f88,plain,(
% 3.22/0.98    k1_tarski(k1_funct_1(sK4,sK2)) != k2_relset_1(k1_tarski(sK2),sK3,sK4)),
% 3.22/0.98    inference(cnf_transformation,[],[f44])).
% 3.22/0.98  
% 3.22/0.98  fof(f99,plain,(
% 3.22/0.98    k6_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) != k2_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK4)),
% 3.22/0.98    inference(definition_unfolding,[],[f88,f94,f94])).
% 3.22/0.98  
% 3.22/0.98  fof(f8,axiom,(
% 3.22/0.98    ! [X0,X1,X2,X3,X4,X5,X6] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 <=> ! [X7] : (r2_hidden(X7,X6) <=> ~(X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)))),
% 3.22/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/0.98  
% 3.22/0.98  fof(f20,plain,(
% 3.22/0.98    ! [X0,X1,X2,X3,X4,X5,X6] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 <=> ! [X7] : (r2_hidden(X7,X6) <=> (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7)))),
% 3.22/0.98    inference(ennf_transformation,[],[f8])).
% 3.22/0.98  
% 3.22/0.98  fof(f34,plain,(
% 3.22/0.98    ! [X5,X4,X3,X2,X1,X0,X6] : (sP0(X5,X4,X3,X2,X1,X0,X6) <=> ! [X7] : (r2_hidden(X7,X6) <=> (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7)))),
% 3.22/0.98    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.22/0.98  
% 3.22/0.98  fof(f35,plain,(
% 3.22/0.98    ! [X0,X1,X2,X3,X4,X5,X6] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 <=> sP0(X5,X4,X3,X2,X1,X0,X6))),
% 3.22/0.98    inference(definition_folding,[],[f20,f34])).
% 3.22/0.98  
% 3.22/0.98  fof(f41,plain,(
% 3.22/0.98    ! [X0,X1,X2,X3,X4,X5,X6] : ((k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 | ~sP0(X5,X4,X3,X2,X1,X0,X6)) & (sP0(X5,X4,X3,X2,X1,X0,X6) | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6))),
% 3.22/0.98    inference(nnf_transformation,[],[f35])).
% 3.22/0.98  
% 3.22/0.98  fof(f66,plain,(
% 3.22/0.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (sP0(X5,X4,X3,X2,X1,X0,X6) | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6) )),
% 3.22/0.98    inference(cnf_transformation,[],[f41])).
% 3.22/0.98  
% 3.22/0.98  fof(f96,plain,(
% 3.22/0.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (sP0(X5,X4,X3,X2,X1,X0,X6) | k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) != X6) )),
% 3.22/0.98    inference(definition_unfolding,[],[f66,f89])).
% 3.22/0.98  
% 3.22/0.98  fof(f108,plain,(
% 3.22/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (sP0(X5,X4,X3,X2,X1,X0,k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5))) )),
% 3.22/0.98    inference(equality_resolution,[],[f96])).
% 3.22/0.98  
% 3.22/0.98  fof(f36,plain,(
% 3.22/0.98    ! [X5,X4,X3,X2,X1,X0,X6] : ((sP0(X5,X4,X3,X2,X1,X0,X6) | ? [X7] : (((X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7) | ~r2_hidden(X7,X6)) & ((X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7) | r2_hidden(X7,X6)))) & (! [X7] : ((r2_hidden(X7,X6) | (X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)) & ((X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7) | ~r2_hidden(X7,X6))) | ~sP0(X5,X4,X3,X2,X1,X0,X6)))),
% 3.22/0.98    inference(nnf_transformation,[],[f34])).
% 3.22/0.98  
% 3.22/0.98  fof(f37,plain,(
% 3.22/0.98    ! [X5,X4,X3,X2,X1,X0,X6] : ((sP0(X5,X4,X3,X2,X1,X0,X6) | ? [X7] : (((X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7) | ~r2_hidden(X7,X6)) & (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7 | r2_hidden(X7,X6)))) & (! [X7] : ((r2_hidden(X7,X6) | (X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)) & (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7 | ~r2_hidden(X7,X6))) | ~sP0(X5,X4,X3,X2,X1,X0,X6)))),
% 3.22/0.98    inference(flattening,[],[f36])).
% 3.22/0.98  
% 3.22/0.98  fof(f38,plain,(
% 3.22/0.98    ! [X0,X1,X2,X3,X4,X5,X6] : ((sP0(X0,X1,X2,X3,X4,X5,X6) | ? [X7] : (((X0 != X7 & X1 != X7 & X2 != X7 & X3 != X7 & X4 != X7 & X5 != X7) | ~r2_hidden(X7,X6)) & (X0 = X7 | X1 = X7 | X2 = X7 | X3 = X7 | X4 = X7 | X5 = X7 | r2_hidden(X7,X6)))) & (! [X8] : ((r2_hidden(X8,X6) | (X0 != X8 & X1 != X8 & X2 != X8 & X3 != X8 & X4 != X8 & X5 != X8)) & (X0 = X8 | X1 = X8 | X2 = X8 | X3 = X8 | X4 = X8 | X5 = X8 | ~r2_hidden(X8,X6))) | ~sP0(X0,X1,X2,X3,X4,X5,X6)))),
% 3.22/0.98    inference(rectify,[],[f37])).
% 3.22/0.98  
% 3.22/0.98  fof(f39,plain,(
% 3.22/0.98    ! [X6,X5,X4,X3,X2,X1,X0] : (? [X7] : (((X0 != X7 & X1 != X7 & X2 != X7 & X3 != X7 & X4 != X7 & X5 != X7) | ~r2_hidden(X7,X6)) & (X0 = X7 | X1 = X7 | X2 = X7 | X3 = X7 | X4 = X7 | X5 = X7 | r2_hidden(X7,X6))) => (((sK1(X0,X1,X2,X3,X4,X5,X6) != X0 & sK1(X0,X1,X2,X3,X4,X5,X6) != X1 & sK1(X0,X1,X2,X3,X4,X5,X6) != X2 & sK1(X0,X1,X2,X3,X4,X5,X6) != X3 & sK1(X0,X1,X2,X3,X4,X5,X6) != X4 & sK1(X0,X1,X2,X3,X4,X5,X6) != X5) | ~r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6),X6)) & (sK1(X0,X1,X2,X3,X4,X5,X6) = X0 | sK1(X0,X1,X2,X3,X4,X5,X6) = X1 | sK1(X0,X1,X2,X3,X4,X5,X6) = X2 | sK1(X0,X1,X2,X3,X4,X5,X6) = X3 | sK1(X0,X1,X2,X3,X4,X5,X6) = X4 | sK1(X0,X1,X2,X3,X4,X5,X6) = X5 | r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6),X6))))),
% 3.22/0.98    introduced(choice_axiom,[])).
% 3.22/0.98  
% 3.22/0.98  fof(f40,plain,(
% 3.22/0.98    ! [X0,X1,X2,X3,X4,X5,X6] : ((sP0(X0,X1,X2,X3,X4,X5,X6) | (((sK1(X0,X1,X2,X3,X4,X5,X6) != X0 & sK1(X0,X1,X2,X3,X4,X5,X6) != X1 & sK1(X0,X1,X2,X3,X4,X5,X6) != X2 & sK1(X0,X1,X2,X3,X4,X5,X6) != X3 & sK1(X0,X1,X2,X3,X4,X5,X6) != X4 & sK1(X0,X1,X2,X3,X4,X5,X6) != X5) | ~r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6),X6)) & (sK1(X0,X1,X2,X3,X4,X5,X6) = X0 | sK1(X0,X1,X2,X3,X4,X5,X6) = X1 | sK1(X0,X1,X2,X3,X4,X5,X6) = X2 | sK1(X0,X1,X2,X3,X4,X5,X6) = X3 | sK1(X0,X1,X2,X3,X4,X5,X6) = X4 | sK1(X0,X1,X2,X3,X4,X5,X6) = X5 | r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6),X6)))) & (! [X8] : ((r2_hidden(X8,X6) | (X0 != X8 & X1 != X8 & X2 != X8 & X3 != X8 & X4 != X8 & X5 != X8)) & (X0 = X8 | X1 = X8 | X2 = X8 | X3 = X8 | X4 = X8 | X5 = X8 | ~r2_hidden(X8,X6))) | ~sP0(X0,X1,X2,X3,X4,X5,X6)))),
% 3.22/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f38,f39])).
% 3.22/0.98  
% 3.22/0.98  fof(f58,plain,(
% 3.22/0.98    ( ! [X6,X4,X2,X0,X8,X5,X3,X1] : (r2_hidden(X8,X6) | X0 != X8 | ~sP0(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.22/0.98    inference(cnf_transformation,[],[f40])).
% 3.22/0.98  
% 3.22/0.98  fof(f102,plain,(
% 3.22/0.98    ( ! [X6,X4,X2,X8,X5,X3,X1] : (r2_hidden(X8,X6) | ~sP0(X8,X1,X2,X3,X4,X5,X6)) )),
% 3.22/0.98    inference(equality_resolution,[],[f58])).
% 3.22/0.98  
% 3.22/0.98  fof(f12,axiom,(
% 3.22/0.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)))),
% 3.22/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.22/0.98  
% 3.22/0.98  fof(f23,plain,(
% 3.22/0.98    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.22/0.98    inference(ennf_transformation,[],[f12])).
% 3.22/0.98  
% 3.22/0.98  fof(f24,plain,(
% 3.22/0.98    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.22/0.98    inference(flattening,[],[f23])).
% 3.22/0.98  
% 3.22/0.98  fof(f71,plain,(
% 3.22/0.98    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.22/0.98    inference(cnf_transformation,[],[f24])).
% 3.22/0.98  
% 3.22/0.98  fof(f98,plain,(
% 3.22/0.98    ( ! [X0,X1] : (k6_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.22/0.98    inference(definition_unfolding,[],[f71,f94])).
% 3.22/0.98  
% 3.22/0.98  cnf(c_35,negated_conjecture,
% 3.22/0.98      ( v1_funct_2(sK4,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3) ),
% 3.22/0.98      inference(cnf_transformation,[],[f101]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_29,plain,
% 3.22/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.22/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.22/0.98      | k1_relset_1(X1,X2,X0) = X1
% 3.22/0.98      | k1_xboole_0 = X2 ),
% 3.22/0.98      inference(cnf_transformation,[],[f76]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_34,negated_conjecture,
% 3.22/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))) ),
% 3.22/0.98      inference(cnf_transformation,[],[f100]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_465,plain,
% 3.22/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.22/0.98      | k1_relset_1(X1,X2,X0) = X1
% 3.22/0.98      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 3.22/0.98      | sK4 != X0
% 3.22/0.98      | k1_xboole_0 = X2 ),
% 3.22/0.98      inference(resolution_lifted,[status(thm)],[c_29,c_34]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_466,plain,
% 3.22/0.98      ( ~ v1_funct_2(sK4,X0,X1)
% 3.22/0.98      | k1_relset_1(X0,X1,sK4) = X0
% 3.22/0.98      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.22/0.98      | k1_xboole_0 = X1 ),
% 3.22/0.98      inference(unflattening,[status(thm)],[c_465]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_743,plain,
% 3.22/0.98      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != X0
% 3.22/0.98      | k1_relset_1(X0,X1,sK4) = X0
% 3.22/0.98      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.22/0.98      | sK3 != X1
% 3.22/0.98      | sK4 != sK4
% 3.22/0.98      | k1_xboole_0 = X1 ),
% 3.22/0.98      inference(resolution_lifted,[status(thm)],[c_35,c_466]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_744,plain,
% 3.22/0.98      ( k1_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK4) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
% 3.22/0.98      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))
% 3.22/0.98      | k1_xboole_0 = sK3 ),
% 3.22/0.98      inference(unflattening,[status(thm)],[c_743]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_33,negated_conjecture,
% 3.22/0.98      ( k1_xboole_0 != sK3 ),
% 3.22/0.98      inference(cnf_transformation,[],[f87]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_745,plain,
% 3.22/0.98      ( k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))
% 3.22/0.98      | k1_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK4) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 3.22/0.98      inference(global_propositional_subsumption,
% 3.22/0.98                [status(thm)],
% 3.22/0.98                [c_744,c_33]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_746,plain,
% 3.22/0.98      ( k1_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK4) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
% 3.22/0.98      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) ),
% 3.22/0.98      inference(renaming,[status(thm)],[c_745]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_3111,plain,
% 3.22/0.98      ( k1_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK4) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 3.22/0.98      inference(equality_resolution_simp,[status(thm)],[c_746]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_20,plain,
% 3.22/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.22/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.22/0.98      inference(cnf_transformation,[],[f72]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_528,plain,
% 3.22/0.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.22/0.98      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.22/0.98      | sK4 != X2 ),
% 3.22/0.98      inference(resolution_lifted,[status(thm)],[c_20,c_34]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_529,plain,
% 3.22/0.98      ( k1_relset_1(X0,X1,sK4) = k1_relat_1(sK4)
% 3.22/0.98      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 3.22/0.98      inference(unflattening,[status(thm)],[c_528]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_8447,plain,
% 3.22/0.98      ( k1_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK4) = k1_relat_1(sK4) ),
% 3.22/0.98      inference(equality_resolution,[status(thm)],[c_529]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_8945,plain,
% 3.22/0.98      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k1_relat_1(sK4) ),
% 3.22/0.98      inference(light_normalisation,[status(thm)],[c_3111,c_8447]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_23,plain,
% 3.22/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.22/0.98      | k7_relset_1(X1,X2,X0,k8_relset_1(X1,X2,X0,X2)) = k2_relset_1(X1,X2,X0) ),
% 3.22/0.98      inference(cnf_transformation,[],[f74]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_501,plain,
% 3.22/0.98      ( k7_relset_1(X0,X1,X2,k8_relset_1(X0,X1,X2,X1)) = k2_relset_1(X0,X1,X2)
% 3.22/0.98      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.22/0.98      | sK4 != X2 ),
% 3.22/0.98      inference(resolution_lifted,[status(thm)],[c_23,c_34]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_502,plain,
% 3.22/0.98      ( k7_relset_1(X0,X1,sK4,k8_relset_1(X0,X1,sK4,X1)) = k2_relset_1(X0,X1,sK4)
% 3.22/0.98      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 3.22/0.98      inference(unflattening,[status(thm)],[c_501]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_8953,plain,
% 3.22/0.98      ( k7_relset_1(X0,X1,sK4,k8_relset_1(X0,X1,sK4,X1)) = k2_relset_1(X0,X1,sK4)
% 3.22/0.98      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 3.22/0.98      inference(demodulation,[status(thm)],[c_8945,c_502]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_9876,plain,
% 3.22/0.98      ( k7_relset_1(k1_relat_1(sK4),sK3,sK4,k8_relset_1(k1_relat_1(sK4),sK3,sK4,sK3)) = k2_relset_1(k1_relat_1(sK4),sK3,sK4) ),
% 3.22/0.98      inference(equality_resolution,[status(thm)],[c_8953]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_31,plain,
% 3.22/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.22/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.22/0.98      | ~ v1_funct_1(X0)
% 3.22/0.98      | k8_relset_1(X1,X2,X0,X2) = X1
% 3.22/0.98      | k1_xboole_0 = X2 ),
% 3.22/0.98      inference(cnf_transformation,[],[f82]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_36,negated_conjecture,
% 3.22/0.98      ( v1_funct_1(sK4) ),
% 3.22/0.98      inference(cnf_transformation,[],[f84]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_404,plain,
% 3.22/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.22/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.22/0.98      | k8_relset_1(X1,X2,X0,X2) = X1
% 3.22/0.98      | sK4 != X0
% 3.22/0.98      | k1_xboole_0 = X2 ),
% 3.22/0.98      inference(resolution_lifted,[status(thm)],[c_31,c_36]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_405,plain,
% 3.22/0.98      ( ~ v1_funct_2(sK4,X0,X1)
% 3.22/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.22/0.98      | k8_relset_1(X0,X1,sK4,X1) = X0
% 3.22/0.98      | k1_xboole_0 = X1 ),
% 3.22/0.98      inference(unflattening,[status(thm)],[c_404]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_602,plain,
% 3.22/0.98      ( ~ v1_funct_2(sK4,X0,X1)
% 3.22/0.98      | k8_relset_1(X0,X1,sK4,X1) = X0
% 3.22/0.98      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.22/0.98      | sK4 != sK4
% 3.22/0.98      | k1_xboole_0 = X1 ),
% 3.22/0.98      inference(resolution_lifted,[status(thm)],[c_34,c_405]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_733,plain,
% 3.22/0.98      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != X0
% 3.22/0.98      | k8_relset_1(X0,X1,sK4,X1) = X0
% 3.22/0.98      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.22/0.98      | sK3 != X1
% 3.22/0.98      | sK4 != sK4
% 3.22/0.98      | k1_xboole_0 = X1 ),
% 3.22/0.98      inference(resolution_lifted,[status(thm)],[c_35,c_602]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_734,plain,
% 3.22/0.98      ( k8_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK4,sK3) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
% 3.22/0.98      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))
% 3.22/0.98      | k1_xboole_0 = sK3 ),
% 3.22/0.98      inference(unflattening,[status(thm)],[c_733]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_735,plain,
% 3.22/0.98      ( k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))
% 3.22/0.98      | k8_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK4,sK3) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 3.22/0.98      inference(global_propositional_subsumption,
% 3.22/0.98                [status(thm)],
% 3.22/0.98                [c_734,c_33]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_736,plain,
% 3.22/0.98      ( k8_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK4,sK3) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
% 3.22/0.98      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) ),
% 3.22/0.98      inference(renaming,[status(thm)],[c_735]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_3112,plain,
% 3.22/0.98      ( k8_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK4,sK3) = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
% 3.22/0.98      inference(equality_resolution_simp,[status(thm)],[c_736]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_9437,plain,
% 3.22/0.98      ( k8_relset_1(k1_relat_1(sK4),sK3,sK4,sK3) = k1_relat_1(sK4) ),
% 3.22/0.98      inference(light_normalisation,[status(thm)],[c_3112,c_8945]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_9877,plain,
% 3.22/0.98      ( k7_relset_1(k1_relat_1(sK4),sK3,sK4,k1_relat_1(sK4)) = k2_relset_1(k1_relat_1(sK4),sK3,sK4) ),
% 3.22/0.98      inference(light_normalisation,[status(thm)],[c_9876,c_9437]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_21,plain,
% 3.22/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.22/0.98      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.22/0.98      inference(cnf_transformation,[],[f73]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_519,plain,
% 3.22/0.98      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.22/0.98      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.22/0.98      | sK4 != X2 ),
% 3.22/0.98      inference(resolution_lifted,[status(thm)],[c_21,c_34]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_520,plain,
% 3.22/0.98      ( k7_relset_1(X0,X1,sK4,X2) = k9_relat_1(sK4,X2)
% 3.22/0.98      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 3.22/0.98      inference(unflattening,[status(thm)],[c_519]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_8450,plain,
% 3.22/0.98      ( k7_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK4,X0) = k9_relat_1(sK4,X0) ),
% 3.22/0.98      inference(equality_resolution,[status(thm)],[c_520]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_8947,plain,
% 3.22/0.98      ( k7_relset_1(k1_relat_1(sK4),sK3,sK4,X0) = k9_relat_1(sK4,X0) ),
% 3.22/0.98      inference(demodulation,[status(thm)],[c_8945,c_8450]) ).
% 3.22/0.98  
% 3.22/0.98  cnf(c_16,plain,
% 3.22/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.22/0.98      | ~ v1_relat_1(X1)
% 3.22/0.98      | v1_relat_1(X0) ),
% 3.22/0.98      inference(cnf_transformation,[],[f68]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_450,plain,
% 3.22/0.99      ( ~ v1_relat_1(X0)
% 3.22/0.99      | v1_relat_1(X1)
% 3.22/0.99      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(X0)
% 3.22/0.99      | sK4 != X1 ),
% 3.22/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_34]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_451,plain,
% 3.22/0.99      ( ~ v1_relat_1(X0)
% 3.22/0.99      | v1_relat_1(sK4)
% 3.22/0.99      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(X0) ),
% 3.22/0.99      inference(unflattening,[status(thm)],[c_450]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_8187,plain,
% 3.22/0.99      ( k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(X0)
% 3.22/0.99      | v1_relat_1(X0) != iProver_top
% 3.22/0.99      | v1_relat_1(sK4) = iProver_top ),
% 3.22/0.99      inference(predicate_to_equality,[status(thm)],[c_451]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_7820,plain,( X0 = X0 ),theory(equality) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_8431,plain,
% 3.22/0.99      ( k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) = k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_7820]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_8426,plain,
% 3.22/0.99      ( ~ v1_relat_1(k2_zfmisc_1(X0,X1))
% 3.22/0.99      | v1_relat_1(sK4)
% 3.22/0.99      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_451]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_8751,plain,
% 3.22/0.99      ( ~ v1_relat_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))
% 3.22/0.99      | v1_relat_1(sK4)
% 3.22/0.99      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_8426]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_8752,plain,
% 3.22/0.99      ( k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3))
% 3.22/0.99      | v1_relat_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) != iProver_top
% 3.22/0.99      | v1_relat_1(sK4) = iProver_top ),
% 3.22/0.99      inference(predicate_to_equality,[status(thm)],[c_8751]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_18,plain,
% 3.22/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.22/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_9439,plain,
% 3.22/0.99      ( v1_relat_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_18]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_9440,plain,
% 3.22/0.99      ( v1_relat_1(k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3)) = iProver_top ),
% 3.22/0.99      inference(predicate_to_equality,[status(thm)],[c_9439]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_9879,plain,
% 3.22/0.99      ( v1_relat_1(sK4) = iProver_top ),
% 3.22/0.99      inference(global_propositional_subsumption,
% 3.22/0.99                [status(thm)],
% 3.22/0.99                [c_8187,c_8431,c_8752,c_9440]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_17,plain,
% 3.22/0.99      ( ~ v1_relat_1(X0)
% 3.22/0.99      | k9_relat_1(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = k11_relat_1(X0,X1) ),
% 3.22/0.99      inference(cnf_transformation,[],[f97]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_8190,plain,
% 3.22/0.99      ( k9_relat_1(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) = k11_relat_1(X0,X1)
% 3.22/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.22/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_10414,plain,
% 3.22/0.99      ( k9_relat_1(sK4,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k11_relat_1(sK4,X0) ),
% 3.22/0.99      inference(superposition,[status(thm)],[c_9879,c_8190]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_10889,plain,
% 3.22/0.99      ( k9_relat_1(sK4,k1_relat_1(sK4)) = k11_relat_1(sK4,sK2) ),
% 3.22/0.99      inference(superposition,[status(thm)],[c_8945,c_10414]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_11205,plain,
% 3.22/0.99      ( k2_relset_1(k1_relat_1(sK4),sK3,sK4) = k11_relat_1(sK4,sK2) ),
% 3.22/0.99      inference(demodulation,[status(thm)],[c_9877,c_8947,c_10889]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_32,negated_conjecture,
% 3.22/0.99      ( k6_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) != k2_relset_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK3,sK4) ),
% 3.22/0.99      inference(cnf_transformation,[],[f99]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_8956,plain,
% 3.22/0.99      ( k6_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) != k2_relset_1(k1_relat_1(sK4),sK3,sK4) ),
% 3.22/0.99      inference(demodulation,[status(thm)],[c_8945,c_32]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_11207,plain,
% 3.22/0.99      ( k6_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) != k11_relat_1(sK4,sK2) ),
% 3.22/0.99      inference(demodulation,[status(thm)],[c_11205,c_8956]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_15,plain,
% 3.22/0.99      ( sP0(X0,X1,X2,X3,X4,X5,k6_enumset1(X5,X5,X5,X4,X3,X2,X1,X0)) ),
% 3.22/0.99      inference(cnf_transformation,[],[f108]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_8191,plain,
% 3.22/0.99      ( sP0(X0,X1,X2,X3,X4,X5,k6_enumset1(X5,X5,X5,X4,X3,X2,X1,X0)) = iProver_top ),
% 3.22/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_9618,plain,
% 3.22/0.99      ( sP0(sK2,sK2,sK2,sK2,sK2,sK2,k1_relat_1(sK4)) = iProver_top ),
% 3.22/0.99      inference(superposition,[status(thm)],[c_8945,c_8191]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_7,plain,
% 3.22/0.99      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6) | r2_hidden(X0,X6) ),
% 3.22/0.99      inference(cnf_transformation,[],[f102]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_19,plain,
% 3.22/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.22/0.99      | ~ v1_funct_1(X1)
% 3.22/0.99      | ~ v1_relat_1(X1)
% 3.22/0.99      | k6_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ),
% 3.22/0.99      inference(cnf_transformation,[],[f98]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_389,plain,
% 3.22/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.22/0.99      | ~ v1_relat_1(X1)
% 3.22/0.99      | k6_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
% 3.22/0.99      | sK4 != X1 ),
% 3.22/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_36]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_390,plain,
% 3.22/0.99      ( ~ r2_hidden(X0,k1_relat_1(sK4))
% 3.22/0.99      | ~ v1_relat_1(sK4)
% 3.22/0.99      | k6_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0) ),
% 3.22/0.99      inference(unflattening,[status(thm)],[c_389]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1576,plain,
% 3.22/0.99      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6)
% 3.22/0.99      | ~ v1_relat_1(sK4)
% 3.22/0.99      | X7 != X0
% 3.22/0.99      | k6_enumset1(k1_funct_1(sK4,X7),k1_funct_1(sK4,X7),k1_funct_1(sK4,X7),k1_funct_1(sK4,X7),k1_funct_1(sK4,X7),k1_funct_1(sK4,X7),k1_funct_1(sK4,X7),k1_funct_1(sK4,X7)) = k11_relat_1(sK4,X7)
% 3.22/0.99      | k1_relat_1(sK4) != X6 ),
% 3.22/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_390]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1577,plain,
% 3.22/0.99      ( ~ sP0(X0,X1,X2,X3,X4,X5,k1_relat_1(sK4))
% 3.22/0.99      | ~ v1_relat_1(sK4)
% 3.22/0.99      | k6_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0) ),
% 3.22/0.99      inference(unflattening,[status(thm)],[c_1576]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1578,plain,
% 3.22/0.99      ( k6_enumset1(k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0),k1_funct_1(sK4,X0)) = k11_relat_1(sK4,X0)
% 3.22/0.99      | sP0(X0,X1,X2,X3,X4,X5,k1_relat_1(sK4)) != iProver_top
% 3.22/0.99      | v1_relat_1(sK4) != iProver_top ),
% 3.22/0.99      inference(predicate_to_equality,[status(thm)],[c_1577]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(c_1580,plain,
% 3.22/0.99      ( k6_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) = k11_relat_1(sK4,sK2)
% 3.22/0.99      | sP0(sK2,sK2,sK2,sK2,sK2,sK2,k1_relat_1(sK4)) != iProver_top
% 3.22/0.99      | v1_relat_1(sK4) != iProver_top ),
% 3.22/0.99      inference(instantiation,[status(thm)],[c_1578]) ).
% 3.22/0.99  
% 3.22/0.99  cnf(contradiction,plain,
% 3.22/0.99      ( $false ),
% 3.22/0.99      inference(minisat,
% 3.22/0.99                [status(thm)],
% 3.22/0.99                [c_11207,c_9618,c_9440,c_8752,c_8431,c_1580]) ).
% 3.22/0.99  
% 3.22/0.99  
% 3.22/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.22/0.99  
% 3.22/0.99  ------                               Statistics
% 3.22/0.99  
% 3.22/0.99  ------ General
% 3.22/0.99  
% 3.22/0.99  abstr_ref_over_cycles:                  0
% 3.22/0.99  abstr_ref_under_cycles:                 0
% 3.22/0.99  gc_basic_clause_elim:                   0
% 3.22/0.99  forced_gc_time:                         0
% 3.22/0.99  parsing_time:                           0.013
% 3.22/0.99  unif_index_cands_time:                  0.
% 3.22/0.99  unif_index_add_time:                    0.
% 3.22/0.99  orderings_time:                         0.
% 3.22/0.99  out_proof_time:                         0.01
% 3.22/0.99  total_time:                             0.263
% 3.22/0.99  num_of_symbols:                         53
% 3.22/0.99  num_of_terms:                           5593
% 3.22/0.99  
% 3.22/0.99  ------ Preprocessing
% 3.22/0.99  
% 3.22/0.99  num_of_splits:                          0
% 3.22/0.99  num_of_split_atoms:                     0
% 3.22/0.99  num_of_reused_defs:                     0
% 3.22/0.99  num_eq_ax_congr_red:                    72
% 3.22/0.99  num_of_sem_filtered_clauses:            1
% 3.22/0.99  num_of_subtypes:                        0
% 3.22/0.99  monotx_restored_types:                  0
% 3.22/0.99  sat_num_of_epr_types:                   0
% 3.22/0.99  sat_num_of_non_cyclic_types:            0
% 3.22/0.99  sat_guarded_non_collapsed_types:        0
% 3.22/0.99  num_pure_diseq_elim:                    0
% 3.22/0.99  simp_replaced_by:                       0
% 3.22/0.99  res_preprocessed:                       202
% 3.22/0.99  prep_upred:                             0
% 3.22/0.99  prep_unflattend:                        509
% 3.22/0.99  smt_new_axioms:                         0
% 3.22/0.99  pred_elim_cands:                        3
% 3.22/0.99  pred_elim:                              3
% 3.22/0.99  pred_elim_cl:                           3
% 3.22/0.99  pred_elim_cycles:                       9
% 3.22/0.99  merged_defs:                            0
% 3.22/0.99  merged_defs_ncl:                        0
% 3.22/0.99  bin_hyper_res:                          0
% 3.22/0.99  prep_cycles:                            5
% 3.22/0.99  pred_elim_time:                         0.089
% 3.22/0.99  splitting_time:                         0.
% 3.22/0.99  sem_filter_time:                        0.
% 3.22/0.99  monotx_time:                            0.
% 3.22/0.99  subtype_inf_time:                       0.
% 3.22/0.99  
% 3.22/0.99  ------ Problem properties
% 3.22/0.99  
% 3.22/0.99  clauses:                                33
% 3.22/0.99  conjectures:                            2
% 3.22/0.99  epr:                                    8
% 3.22/0.99  horn:                                   29
% 3.22/0.99  ground:                                 7
% 3.22/0.99  unary:                                  6
% 3.22/0.99  binary:                                 12
% 3.22/0.99  lits:                                   87
% 3.22/0.99  lits_eq:                                51
% 3.22/0.99  fd_pure:                                0
% 3.22/0.99  fd_pseudo:                              0
% 3.22/0.99  fd_cond:                                0
% 3.22/0.99  fd_pseudo_cond:                         2
% 3.22/0.99  ac_symbols:                             0
% 3.22/0.99  
% 3.22/0.99  ------ Propositional Solver
% 3.22/0.99  
% 3.22/0.99  prop_solver_calls:                      29
% 3.22/0.99  prop_fast_solver_calls:                 2690
% 3.22/0.99  smt_solver_calls:                       0
% 3.22/0.99  smt_fast_solver_calls:                  0
% 3.22/0.99  prop_num_of_clauses:                    1630
% 3.22/0.99  prop_preprocess_simplified:             9073
% 3.22/0.99  prop_fo_subsumed:                       5
% 3.22/0.99  prop_solver_time:                       0.
% 3.22/0.99  smt_solver_time:                        0.
% 3.22/0.99  smt_fast_solver_time:                   0.
% 3.22/0.99  prop_fast_solver_time:                  0.
% 3.22/0.99  prop_unsat_core_time:                   0.
% 3.22/0.99  
% 3.22/0.99  ------ QBF
% 3.22/0.99  
% 3.22/0.99  qbf_q_res:                              0
% 3.22/0.99  qbf_num_tautologies:                    0
% 3.22/0.99  qbf_prep_cycles:                        0
% 3.22/0.99  
% 3.22/0.99  ------ BMC1
% 3.22/0.99  
% 3.22/0.99  bmc1_current_bound:                     -1
% 3.22/0.99  bmc1_last_solved_bound:                 -1
% 3.22/0.99  bmc1_unsat_core_size:                   -1
% 3.22/0.99  bmc1_unsat_core_parents_size:           -1
% 3.22/0.99  bmc1_merge_next_fun:                    0
% 3.22/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.22/0.99  
% 3.22/0.99  ------ Instantiation
% 3.22/0.99  
% 3.22/0.99  inst_num_of_clauses:                    387
% 3.22/0.99  inst_num_in_passive:                    13
% 3.22/0.99  inst_num_in_active:                     198
% 3.22/0.99  inst_num_in_unprocessed:                176
% 3.22/0.99  inst_num_of_loops:                      220
% 3.22/0.99  inst_num_of_learning_restarts:          0
% 3.22/0.99  inst_num_moves_active_passive:          21
% 3.22/0.99  inst_lit_activity:                      0
% 3.22/0.99  inst_lit_activity_moves:                0
% 3.22/0.99  inst_num_tautologies:                   0
% 3.22/0.99  inst_num_prop_implied:                  0
% 3.22/0.99  inst_num_existing_simplified:           0
% 3.22/0.99  inst_num_eq_res_simplified:             0
% 3.22/0.99  inst_num_child_elim:                    0
% 3.22/0.99  inst_num_of_dismatching_blockings:      36
% 3.22/0.99  inst_num_of_non_proper_insts:           290
% 3.22/0.99  inst_num_of_duplicates:                 0
% 3.22/0.99  inst_inst_num_from_inst_to_res:         0
% 3.22/0.99  inst_dismatching_checking_time:         0.
% 3.22/0.99  
% 3.22/0.99  ------ Resolution
% 3.22/0.99  
% 3.22/0.99  res_num_of_clauses:                     0
% 3.22/0.99  res_num_in_passive:                     0
% 3.22/0.99  res_num_in_active:                      0
% 3.22/0.99  res_num_of_loops:                       207
% 3.22/0.99  res_forward_subset_subsumed:            141
% 3.22/0.99  res_backward_subset_subsumed:           0
% 3.22/0.99  res_forward_subsumed:                   0
% 3.22/0.99  res_backward_subsumed:                  0
% 3.22/0.99  res_forward_subsumption_resolution:     0
% 3.22/0.99  res_backward_subsumption_resolution:    0
% 3.22/0.99  res_clause_to_clause_subsumption:       4502
% 3.22/0.99  res_orphan_elimination:                 0
% 3.22/0.99  res_tautology_del:                      37
% 3.22/0.99  res_num_eq_res_simplified:              4
% 3.22/0.99  res_num_sel_changes:                    0
% 3.22/0.99  res_moves_from_active_to_pass:          0
% 3.22/0.99  
% 3.22/0.99  ------ Superposition
% 3.22/0.99  
% 3.22/0.99  sup_time_total:                         0.
% 3.22/0.99  sup_time_generating:                    0.
% 3.22/0.99  sup_time_sim_full:                      0.
% 3.22/0.99  sup_time_sim_immed:                     0.
% 3.22/0.99  
% 3.22/0.99  sup_num_of_clauses:                     51
% 3.22/0.99  sup_num_in_active:                      31
% 3.22/0.99  sup_num_in_passive:                     20
% 3.22/0.99  sup_num_of_loops:                       43
% 3.22/0.99  sup_fw_superposition:                   5
% 3.22/0.99  sup_bw_superposition:                   13
% 3.22/0.99  sup_immediate_simplified:               2
% 3.22/0.99  sup_given_eliminated:                   0
% 3.22/0.99  comparisons_done:                       0
% 3.22/0.99  comparisons_avoided:                    0
% 3.22/0.99  
% 3.22/0.99  ------ Simplifications
% 3.22/0.99  
% 3.22/0.99  
% 3.22/0.99  sim_fw_subset_subsumed:                 1
% 3.22/0.99  sim_bw_subset_subsumed:                 0
% 3.22/0.99  sim_fw_subsumed:                        0
% 3.22/0.99  sim_bw_subsumed:                        0
% 3.22/0.99  sim_fw_subsumption_res:                 0
% 3.22/0.99  sim_bw_subsumption_res:                 0
% 3.22/0.99  sim_tautology_del:                      0
% 3.22/0.99  sim_eq_tautology_del:                   0
% 3.22/0.99  sim_eq_res_simp:                        0
% 3.22/0.99  sim_fw_demodulated:                     2
% 3.22/0.99  sim_bw_demodulated:                     12
% 3.22/0.99  sim_light_normalised:                   8
% 3.22/0.99  sim_joinable_taut:                      0
% 3.22/0.99  sim_joinable_simp:                      0
% 3.22/0.99  sim_ac_normalised:                      0
% 3.22/0.99  sim_smt_subsumption:                    0
% 3.22/0.99  
%------------------------------------------------------------------------------
