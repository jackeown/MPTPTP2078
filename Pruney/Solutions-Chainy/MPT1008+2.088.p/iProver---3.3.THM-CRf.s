%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:05:22 EST 2020

% Result     : Theorem 0.67s
% Output     : CNFRefutation 0.67s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 919 expanded)
%              Number of clauses        :   74 ( 201 expanded)
%              Number of leaves         :   15 ( 226 expanded)
%              Depth                    :   19
%              Number of atoms          :  282 (2676 expanded)
%              Number of equality atoms :  183 (1353 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f26,plain,
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

fof(f27,plain,
    ( k1_tarski(k1_funct_1(sK2,sK0)) != k2_relset_1(k1_tarski(sK0),sK1,sK2)
    & k1_xboole_0 != sK1
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_2(sK2,k1_tarski(sK0),sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f26])).

fof(f44,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f47,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f29,f30])).

fof(f48,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f28,f47])).

fof(f51,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f44,f48])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k8_relset_1(X0,X1,X2,X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f43,plain,(
    v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f52,plain,(
    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f43,f48])).

fof(f42,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f45,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f27])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)
        & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)
        & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f31,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f32,f48,f48])).

fof(f46,plain,(
    k1_tarski(k1_funct_1(sK2,sK0)) != k2_relset_1(k1_tarski(sK0),sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f50,plain,(
    k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) ),
    inference(definition_unfolding,[],[f46,f48,f48])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_320,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_13])).

cnf(c_321,plain,
    ( k8_relset_1(X0,X1,sK2,X2) = k10_relat_1(sK2,X2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_320])).

cnf(c_469,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))
    | k8_relset_1(X0_47,X1_47,sK2,X2_47) = k10_relat_1(sK2,X2_47) ),
    inference(subtyping,[status(esa)],[c_321])).

cnf(c_642,plain,
    ( k8_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2,X0_47) = k10_relat_1(sK2,X0_47) ),
    inference(equality_resolution,[status(thm)],[c_469])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k8_relset_1(X1,X2,X0,X2) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_14,negated_conjecture,
    ( v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_223,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k8_relset_1(X1,X2,X0,X2) = X1
    | k2_enumset1(sK0,sK0,sK0,sK0) != X1
    | sK1 != X2
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_14])).

cnf(c_224,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | ~ v1_funct_1(sK2)
    | k8_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2,sK1) = k2_enumset1(sK0,sK0,sK0,sK0)
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_223])).

cnf(c_15,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_12,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_226,plain,
    ( k8_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2,sK1) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_224,c_15,c_13,c_12])).

cnf(c_475,plain,
    ( k8_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2,sK1) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(subtyping,[status(esa)],[c_226])).

cnf(c_795,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k10_relat_1(sK2,sK1) ),
    inference(demodulation,[status(thm)],[c_642,c_475])).

cnf(c_842,plain,
    ( k8_relset_1(k10_relat_1(sK2,sK1),sK1,sK2,X0_47) = k10_relat_1(sK2,X0_47) ),
    inference(demodulation,[status(thm)],[c_795,c_642])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,k7_relset_1(X1,X2,X0,X1)) = k1_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_293,plain,
    ( k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = k1_relset_1(X0,X1,X2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_13])).

cnf(c_294,plain,
    ( k8_relset_1(X0,X1,sK2,k7_relset_1(X0,X1,sK2,X0)) = k1_relset_1(X0,X1,sK2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_293])).

cnf(c_472,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))
    | k8_relset_1(X0_47,X1_47,sK2,k7_relset_1(X0_47,X1_47,sK2,X0_47)) = k1_relset_1(X0_47,X1_47,sK2) ),
    inference(subtyping,[status(esa)],[c_294])).

cnf(c_846,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k10_relat_1(sK2,sK1),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))
    | k8_relset_1(X0_47,X1_47,sK2,k7_relset_1(X0_47,X1_47,sK2,X0_47)) = k1_relset_1(X0_47,X1_47,sK2) ),
    inference(demodulation,[status(thm)],[c_795,c_472])).

cnf(c_1199,plain,
    ( k8_relset_1(k10_relat_1(sK2,sK1),sK1,sK2,k7_relset_1(k10_relat_1(sK2,sK1),sK1,sK2,k10_relat_1(sK2,sK1))) = k1_relset_1(k10_relat_1(sK2,sK1),sK1,sK2) ),
    inference(equality_resolution,[status(thm)],[c_846])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X2) = k1_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_311,plain,
    ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_13])).

cnf(c_312,plain,
    ( k8_relset_1(X0,X1,sK2,X1) = k1_relset_1(X0,X1,sK2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_311])).

cnf(c_470,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))
    | k8_relset_1(X0_47,X1_47,sK2,X1_47) = k1_relset_1(X0_47,X1_47,sK2) ),
    inference(subtyping,[status(esa)],[c_312])).

cnf(c_646,plain,
    ( k8_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2,sK1) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) ),
    inference(equality_resolution,[status(thm)],[c_470])).

cnf(c_647,plain,
    ( k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(light_normalisation,[status(thm)],[c_646,c_475])).

cnf(c_892,plain,
    ( k1_relset_1(k10_relat_1(sK2,sK1),sK1,sK2) = k10_relat_1(sK2,sK1) ),
    inference(light_normalisation,[status(thm)],[c_647,c_795])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X1) = k2_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_302,plain,
    ( k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_13])).

cnf(c_303,plain,
    ( k7_relset_1(X0,X1,sK2,X0) = k2_relset_1(X0,X1,sK2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_302])).

cnf(c_471,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))
    | k7_relset_1(X0_47,X1_47,sK2,X0_47) = k2_relset_1(X0_47,X1_47,sK2) ),
    inference(subtyping,[status(esa)],[c_303])).

cnf(c_669,plain,
    ( k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2,k2_enumset1(sK0,sK0,sK0,sK0)) = k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) ),
    inference(equality_resolution,[status(thm)],[c_471])).

cnf(c_984,plain,
    ( k7_relset_1(k10_relat_1(sK2,sK1),sK1,sK2,k10_relat_1(sK2,sK1)) = k2_relset_1(k10_relat_1(sK2,sK1),sK1,sK2) ),
    inference(light_normalisation,[status(thm)],[c_669,c_795])).

cnf(c_1200,plain,
    ( k8_relset_1(k10_relat_1(sK2,sK1),sK1,sK2,k2_relset_1(k10_relat_1(sK2,sK1),sK1,sK2)) = k10_relat_1(sK2,sK1) ),
    inference(light_normalisation,[status(thm)],[c_1199,c_892,c_984])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_329,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_13])).

cnf(c_330,plain,
    ( k2_relset_1(X0,X1,sK2) = k2_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_329])).

cnf(c_468,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))
    | k2_relset_1(X0_47,X1_47,sK2) = k2_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_330])).

cnf(c_624,plain,
    ( k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_relat_1(sK2) ),
    inference(equality_resolution,[status(thm)],[c_468])).

cnf(c_843,plain,
    ( k2_relset_1(k10_relat_1(sK2,sK1),sK1,sK2) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_795,c_624])).

cnf(c_1272,plain,
    ( k8_relset_1(k10_relat_1(sK2,sK1),sK1,sK2,k2_relat_1(sK2)) = k10_relat_1(sK2,sK1) ),
    inference(light_normalisation,[status(thm)],[c_1200,c_843])).

cnf(c_1274,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k10_relat_1(sK2,sK1) ),
    inference(superposition,[status(thm)],[c_842,c_1272])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_338,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_13])).

cnf(c_339,plain,
    ( v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_338])).

cnf(c_467,plain,
    ( v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) ),
    inference(subtyping,[status(esa)],[c_339])).

cnf(c_542,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_467])).

cnf(c_480,plain,
    ( X0_50 = X0_50 ),
    theory(equality)).

cnf(c_601,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) = k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
    inference(instantiation,[status(thm)],[c_480])).

cnf(c_608,plain,
    ( v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
    inference(instantiation,[status(thm)],[c_467])).

cnf(c_609,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_608])).

cnf(c_924,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_542,c_601,c_609])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_478,plain,
    ( ~ v1_relat_1(X0_48)
    | k10_relat_1(X0_48,k2_relat_1(X0_48)) = k1_relat_1(X0_48) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_540,plain,
    ( k10_relat_1(X0_48,k2_relat_1(X0_48)) = k1_relat_1(X0_48)
    | v1_relat_1(X0_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_478])).

cnf(c_929,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_924,c_540])).

cnf(c_1276,plain,
    ( k10_relat_1(sK2,sK1) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_1274,c_929])).

cnf(c_1,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
    | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_236,plain,
    ( ~ v1_relat_1(X0)
    | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
    | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_15])).

cnf(c_237,plain,
    ( ~ v1_relat_1(sK2)
    | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK2)
    | k2_enumset1(k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_236])).

cnf(c_474,plain,
    ( ~ v1_relat_1(sK2)
    | k2_enumset1(X0_49,X0_49,X0_49,X0_49) != k1_relat_1(sK2)
    | k2_enumset1(k1_funct_1(sK2,X0_49),k1_funct_1(sK2,X0_49),k1_funct_1(sK2,X0_49),k1_funct_1(sK2,X0_49)) = k2_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_237])).

cnf(c_541,plain,
    ( k2_enumset1(X0_49,X0_49,X0_49,X0_49) != k1_relat_1(sK2)
    | k2_enumset1(k1_funct_1(sK2,X0_49),k1_funct_1(sK2,X0_49),k1_funct_1(sK2,X0_49),k1_funct_1(sK2,X0_49)) = k2_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_474])).

cnf(c_1023,plain,
    ( k2_enumset1(k1_funct_1(sK2,X0_49),k1_funct_1(sK2,X0_49),k1_funct_1(sK2,X0_49),k1_funct_1(sK2,X0_49)) = k2_relat_1(sK2)
    | k2_enumset1(X0_49,X0_49,X0_49,X0_49) != k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_541,c_474,c_601,c_608])).

cnf(c_1024,plain,
    ( k2_enumset1(X0_49,X0_49,X0_49,X0_49) != k1_relat_1(sK2)
    | k2_enumset1(k1_funct_1(sK2,X0_49),k1_funct_1(sK2,X0_49),k1_funct_1(sK2,X0_49),k1_funct_1(sK2,X0_49)) = k2_relat_1(sK2) ),
    inference(renaming,[status(thm)],[c_1023])).

cnf(c_1028,plain,
    ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2)
    | k10_relat_1(sK2,sK1) != k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_795,c_1024])).

cnf(c_482,plain,
    ( X0_47 != X1_47
    | X2_47 != X1_47
    | X2_47 = X0_47 ),
    theory(equality)).

cnf(c_617,plain,
    ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != X0_47
    | k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)
    | k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != X0_47 ),
    inference(instantiation,[status(thm)],[c_482])).

cnf(c_648,plain,
    ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)
    | k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relat_1(sK2)
    | k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_617])).

cnf(c_607,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
    | k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_468])).

cnf(c_11,negated_conjecture,
    ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_477,negated_conjecture,
    ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1276,c_1028,c_648,c_607,c_601,c_477])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:41:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 0.67/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.67/1.01  
% 0.67/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.67/1.01  
% 0.67/1.01  ------  iProver source info
% 0.67/1.01  
% 0.67/1.01  git: date: 2020-06-30 10:37:57 +0100
% 0.67/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.67/1.01  git: non_committed_changes: false
% 0.67/1.01  git: last_make_outside_of_git: false
% 0.67/1.01  
% 0.67/1.01  ------ 
% 0.67/1.01  
% 0.67/1.01  ------ Input Options
% 0.67/1.01  
% 0.67/1.01  --out_options                           all
% 0.67/1.01  --tptp_safe_out                         true
% 0.67/1.01  --problem_path                          ""
% 0.67/1.01  --include_path                          ""
% 0.67/1.01  --clausifier                            res/vclausify_rel
% 0.67/1.01  --clausifier_options                    --mode clausify
% 0.67/1.01  --stdin                                 false
% 0.67/1.01  --stats_out                             all
% 0.67/1.01  
% 0.67/1.01  ------ General Options
% 0.67/1.01  
% 0.67/1.01  --fof                                   false
% 0.67/1.01  --time_out_real                         305.
% 0.67/1.01  --time_out_virtual                      -1.
% 0.67/1.01  --symbol_type_check                     false
% 0.67/1.01  --clausify_out                          false
% 0.67/1.01  --sig_cnt_out                           false
% 0.67/1.01  --trig_cnt_out                          false
% 0.67/1.01  --trig_cnt_out_tolerance                1.
% 0.67/1.01  --trig_cnt_out_sk_spl                   false
% 0.67/1.01  --abstr_cl_out                          false
% 0.67/1.01  
% 0.67/1.01  ------ Global Options
% 0.67/1.01  
% 0.67/1.01  --schedule                              default
% 0.67/1.01  --add_important_lit                     false
% 0.67/1.01  --prop_solver_per_cl                    1000
% 0.67/1.01  --min_unsat_core                        false
% 0.67/1.01  --soft_assumptions                      false
% 0.67/1.01  --soft_lemma_size                       3
% 0.67/1.01  --prop_impl_unit_size                   0
% 0.67/1.01  --prop_impl_unit                        []
% 0.67/1.01  --share_sel_clauses                     true
% 0.67/1.01  --reset_solvers                         false
% 0.67/1.01  --bc_imp_inh                            [conj_cone]
% 0.67/1.01  --conj_cone_tolerance                   3.
% 0.67/1.01  --extra_neg_conj                        none
% 0.67/1.01  --large_theory_mode                     true
% 0.67/1.01  --prolific_symb_bound                   200
% 0.67/1.01  --lt_threshold                          2000
% 0.67/1.01  --clause_weak_htbl                      true
% 0.67/1.01  --gc_record_bc_elim                     false
% 0.67/1.01  
% 0.67/1.01  ------ Preprocessing Options
% 0.67/1.01  
% 0.67/1.01  --preprocessing_flag                    true
% 0.67/1.01  --time_out_prep_mult                    0.1
% 0.67/1.01  --splitting_mode                        input
% 0.67/1.01  --splitting_grd                         true
% 0.67/1.01  --splitting_cvd                         false
% 0.67/1.01  --splitting_cvd_svl                     false
% 0.67/1.01  --splitting_nvd                         32
% 0.67/1.01  --sub_typing                            true
% 0.67/1.01  --prep_gs_sim                           true
% 0.67/1.01  --prep_unflatten                        true
% 0.67/1.01  --prep_res_sim                          true
% 0.67/1.01  --prep_upred                            true
% 0.67/1.01  --prep_sem_filter                       exhaustive
% 0.67/1.01  --prep_sem_filter_out                   false
% 0.67/1.01  --pred_elim                             true
% 0.67/1.01  --res_sim_input                         true
% 0.67/1.01  --eq_ax_congr_red                       true
% 0.67/1.01  --pure_diseq_elim                       true
% 0.67/1.01  --brand_transform                       false
% 0.67/1.01  --non_eq_to_eq                          false
% 0.67/1.01  --prep_def_merge                        true
% 0.67/1.01  --prep_def_merge_prop_impl              false
% 0.67/1.01  --prep_def_merge_mbd                    true
% 0.67/1.01  --prep_def_merge_tr_red                 false
% 0.67/1.01  --prep_def_merge_tr_cl                  false
% 0.67/1.01  --smt_preprocessing                     true
% 0.67/1.01  --smt_ac_axioms                         fast
% 0.67/1.01  --preprocessed_out                      false
% 0.67/1.01  --preprocessed_stats                    false
% 0.67/1.01  
% 0.67/1.01  ------ Abstraction refinement Options
% 0.67/1.01  
% 0.67/1.01  --abstr_ref                             []
% 0.67/1.01  --abstr_ref_prep                        false
% 0.67/1.01  --abstr_ref_until_sat                   false
% 0.67/1.01  --abstr_ref_sig_restrict                funpre
% 0.67/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 0.67/1.01  --abstr_ref_under                       []
% 0.67/1.01  
% 0.67/1.01  ------ SAT Options
% 0.67/1.01  
% 0.67/1.01  --sat_mode                              false
% 0.67/1.01  --sat_fm_restart_options                ""
% 0.67/1.01  --sat_gr_def                            false
% 0.67/1.01  --sat_epr_types                         true
% 0.67/1.01  --sat_non_cyclic_types                  false
% 0.67/1.01  --sat_finite_models                     false
% 0.67/1.01  --sat_fm_lemmas                         false
% 0.67/1.01  --sat_fm_prep                           false
% 0.67/1.01  --sat_fm_uc_incr                        true
% 0.67/1.01  --sat_out_model                         small
% 0.67/1.01  --sat_out_clauses                       false
% 0.67/1.01  
% 0.67/1.01  ------ QBF Options
% 0.67/1.01  
% 0.67/1.01  --qbf_mode                              false
% 0.67/1.01  --qbf_elim_univ                         false
% 0.67/1.01  --qbf_dom_inst                          none
% 0.67/1.01  --qbf_dom_pre_inst                      false
% 0.67/1.01  --qbf_sk_in                             false
% 0.67/1.01  --qbf_pred_elim                         true
% 0.67/1.01  --qbf_split                             512
% 0.67/1.01  
% 0.67/1.01  ------ BMC1 Options
% 0.67/1.01  
% 0.67/1.01  --bmc1_incremental                      false
% 0.67/1.01  --bmc1_axioms                           reachable_all
% 0.67/1.01  --bmc1_min_bound                        0
% 0.67/1.01  --bmc1_max_bound                        -1
% 0.67/1.01  --bmc1_max_bound_default                -1
% 0.67/1.01  --bmc1_symbol_reachability              true
% 0.67/1.01  --bmc1_property_lemmas                  false
% 0.67/1.01  --bmc1_k_induction                      false
% 0.67/1.01  --bmc1_non_equiv_states                 false
% 0.67/1.01  --bmc1_deadlock                         false
% 0.67/1.01  --bmc1_ucm                              false
% 0.67/1.01  --bmc1_add_unsat_core                   none
% 0.67/1.01  --bmc1_unsat_core_children              false
% 0.67/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 0.67/1.01  --bmc1_out_stat                         full
% 0.67/1.01  --bmc1_ground_init                      false
% 0.67/1.01  --bmc1_pre_inst_next_state              false
% 0.67/1.01  --bmc1_pre_inst_state                   false
% 0.67/1.01  --bmc1_pre_inst_reach_state             false
% 0.67/1.01  --bmc1_out_unsat_core                   false
% 0.67/1.01  --bmc1_aig_witness_out                  false
% 0.67/1.01  --bmc1_verbose                          false
% 0.67/1.01  --bmc1_dump_clauses_tptp                false
% 0.67/1.01  --bmc1_dump_unsat_core_tptp             false
% 0.67/1.01  --bmc1_dump_file                        -
% 0.67/1.01  --bmc1_ucm_expand_uc_limit              128
% 0.67/1.01  --bmc1_ucm_n_expand_iterations          6
% 0.67/1.01  --bmc1_ucm_extend_mode                  1
% 0.67/1.01  --bmc1_ucm_init_mode                    2
% 0.67/1.01  --bmc1_ucm_cone_mode                    none
% 0.67/1.01  --bmc1_ucm_reduced_relation_type        0
% 0.67/1.01  --bmc1_ucm_relax_model                  4
% 0.67/1.01  --bmc1_ucm_full_tr_after_sat            true
% 0.67/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 0.67/1.01  --bmc1_ucm_layered_model                none
% 0.67/1.01  --bmc1_ucm_max_lemma_size               10
% 0.67/1.01  
% 0.67/1.01  ------ AIG Options
% 0.67/1.01  
% 0.67/1.01  --aig_mode                              false
% 0.67/1.01  
% 0.67/1.01  ------ Instantiation Options
% 0.67/1.01  
% 0.67/1.01  --instantiation_flag                    true
% 0.67/1.01  --inst_sos_flag                         false
% 0.67/1.01  --inst_sos_phase                        true
% 0.67/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.67/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.67/1.01  --inst_lit_sel_side                     num_symb
% 0.67/1.01  --inst_solver_per_active                1400
% 0.67/1.01  --inst_solver_calls_frac                1.
% 0.67/1.01  --inst_passive_queue_type               priority_queues
% 0.67/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.67/1.01  --inst_passive_queues_freq              [25;2]
% 0.67/1.01  --inst_dismatching                      true
% 0.67/1.01  --inst_eager_unprocessed_to_passive     true
% 0.67/1.01  --inst_prop_sim_given                   true
% 0.67/1.01  --inst_prop_sim_new                     false
% 0.67/1.01  --inst_subs_new                         false
% 0.67/1.01  --inst_eq_res_simp                      false
% 0.67/1.01  --inst_subs_given                       false
% 0.67/1.01  --inst_orphan_elimination               true
% 0.67/1.01  --inst_learning_loop_flag               true
% 0.67/1.01  --inst_learning_start                   3000
% 0.67/1.01  --inst_learning_factor                  2
% 0.67/1.01  --inst_start_prop_sim_after_learn       3
% 0.67/1.01  --inst_sel_renew                        solver
% 0.67/1.01  --inst_lit_activity_flag                true
% 0.67/1.01  --inst_restr_to_given                   false
% 0.67/1.01  --inst_activity_threshold               500
% 0.67/1.01  --inst_out_proof                        true
% 0.67/1.01  
% 0.67/1.01  ------ Resolution Options
% 0.67/1.01  
% 0.67/1.01  --resolution_flag                       true
% 0.67/1.01  --res_lit_sel                           adaptive
% 0.67/1.01  --res_lit_sel_side                      none
% 0.67/1.01  --res_ordering                          kbo
% 0.67/1.01  --res_to_prop_solver                    active
% 0.67/1.01  --res_prop_simpl_new                    false
% 0.67/1.01  --res_prop_simpl_given                  true
% 0.67/1.01  --res_passive_queue_type                priority_queues
% 0.67/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.67/1.01  --res_passive_queues_freq               [15;5]
% 0.67/1.01  --res_forward_subs                      full
% 0.67/1.01  --res_backward_subs                     full
% 0.67/1.01  --res_forward_subs_resolution           true
% 0.67/1.01  --res_backward_subs_resolution          true
% 0.67/1.01  --res_orphan_elimination                true
% 0.67/1.01  --res_time_limit                        2.
% 0.67/1.01  --res_out_proof                         true
% 0.67/1.01  
% 0.67/1.01  ------ Superposition Options
% 0.67/1.01  
% 0.67/1.01  --superposition_flag                    true
% 0.67/1.01  --sup_passive_queue_type                priority_queues
% 0.67/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.67/1.01  --sup_passive_queues_freq               [8;1;4]
% 0.67/1.01  --demod_completeness_check              fast
% 0.67/1.01  --demod_use_ground                      true
% 0.67/1.01  --sup_to_prop_solver                    passive
% 0.67/1.01  --sup_prop_simpl_new                    true
% 0.67/1.01  --sup_prop_simpl_given                  true
% 0.67/1.01  --sup_fun_splitting                     false
% 0.67/1.01  --sup_smt_interval                      50000
% 0.67/1.01  
% 0.67/1.01  ------ Superposition Simplification Setup
% 0.67/1.01  
% 0.67/1.01  --sup_indices_passive                   []
% 0.67/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.67/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.67/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.67/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 0.67/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.67/1.01  --sup_full_bw                           [BwDemod]
% 0.67/1.01  --sup_immed_triv                        [TrivRules]
% 0.67/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.67/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.67/1.01  --sup_immed_bw_main                     []
% 0.67/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.67/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 0.67/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.67/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.67/1.01  
% 0.67/1.01  ------ Combination Options
% 0.67/1.01  
% 0.67/1.01  --comb_res_mult                         3
% 0.67/1.01  --comb_sup_mult                         2
% 0.67/1.01  --comb_inst_mult                        10
% 0.67/1.01  
% 0.67/1.01  ------ Debug Options
% 0.67/1.01  
% 0.67/1.01  --dbg_backtrace                         false
% 0.67/1.01  --dbg_dump_prop_clauses                 false
% 0.67/1.01  --dbg_dump_prop_clauses_file            -
% 0.67/1.01  --dbg_out_stat                          false
% 0.67/1.01  ------ Parsing...
% 0.67/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.67/1.01  
% 0.67/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 0.67/1.01  
% 0.67/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.67/1.01  
% 0.67/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 0.67/1.01  ------ Proving...
% 0.67/1.01  ------ Problem Properties 
% 0.67/1.01  
% 0.67/1.01  
% 0.67/1.01  clauses                                 13
% 0.67/1.01  conjectures                             2
% 0.67/1.01  EPR                                     1
% 0.67/1.01  Horn                                    13
% 0.67/1.01  unary                                   3
% 0.67/1.01  binary                                  8
% 0.67/1.01  lits                                    25
% 0.67/1.01  lits eq                                 22
% 0.67/1.01  fd_pure                                 0
% 0.67/1.01  fd_pseudo                               0
% 0.67/1.01  fd_cond                                 0
% 0.67/1.01  fd_pseudo_cond                          0
% 0.67/1.01  AC symbols                              0
% 0.67/1.01  
% 0.67/1.01  ------ Schedule dynamic 5 is on 
% 0.67/1.01  
% 0.67/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.67/1.01  
% 0.67/1.01  
% 0.67/1.01  ------ 
% 0.67/1.01  Current options:
% 0.67/1.01  ------ 
% 0.67/1.01  
% 0.67/1.01  ------ Input Options
% 0.67/1.01  
% 0.67/1.01  --out_options                           all
% 0.67/1.01  --tptp_safe_out                         true
% 0.67/1.01  --problem_path                          ""
% 0.67/1.01  --include_path                          ""
% 0.67/1.01  --clausifier                            res/vclausify_rel
% 0.67/1.01  --clausifier_options                    --mode clausify
% 0.67/1.01  --stdin                                 false
% 0.67/1.01  --stats_out                             all
% 0.67/1.01  
% 0.67/1.01  ------ General Options
% 0.67/1.01  
% 0.67/1.01  --fof                                   false
% 0.67/1.01  --time_out_real                         305.
% 0.67/1.01  --time_out_virtual                      -1.
% 0.67/1.01  --symbol_type_check                     false
% 0.67/1.01  --clausify_out                          false
% 0.67/1.01  --sig_cnt_out                           false
% 0.67/1.01  --trig_cnt_out                          false
% 0.67/1.01  --trig_cnt_out_tolerance                1.
% 0.67/1.01  --trig_cnt_out_sk_spl                   false
% 0.67/1.01  --abstr_cl_out                          false
% 0.67/1.01  
% 0.67/1.01  ------ Global Options
% 0.67/1.01  
% 0.67/1.01  --schedule                              default
% 0.67/1.01  --add_important_lit                     false
% 0.67/1.01  --prop_solver_per_cl                    1000
% 0.67/1.01  --min_unsat_core                        false
% 0.67/1.01  --soft_assumptions                      false
% 0.67/1.01  --soft_lemma_size                       3
% 0.67/1.01  --prop_impl_unit_size                   0
% 0.67/1.01  --prop_impl_unit                        []
% 0.67/1.01  --share_sel_clauses                     true
% 0.67/1.01  --reset_solvers                         false
% 0.67/1.01  --bc_imp_inh                            [conj_cone]
% 0.67/1.01  --conj_cone_tolerance                   3.
% 0.67/1.02  --extra_neg_conj                        none
% 0.67/1.02  --large_theory_mode                     true
% 0.67/1.02  --prolific_symb_bound                   200
% 0.67/1.02  --lt_threshold                          2000
% 0.67/1.02  --clause_weak_htbl                      true
% 0.67/1.02  --gc_record_bc_elim                     false
% 0.67/1.02  
% 0.67/1.02  ------ Preprocessing Options
% 0.67/1.02  
% 0.67/1.02  --preprocessing_flag                    true
% 0.67/1.02  --time_out_prep_mult                    0.1
% 0.67/1.02  --splitting_mode                        input
% 0.67/1.02  --splitting_grd                         true
% 0.67/1.02  --splitting_cvd                         false
% 0.67/1.02  --splitting_cvd_svl                     false
% 0.67/1.02  --splitting_nvd                         32
% 0.67/1.02  --sub_typing                            true
% 0.67/1.02  --prep_gs_sim                           true
% 0.67/1.02  --prep_unflatten                        true
% 0.67/1.02  --prep_res_sim                          true
% 0.67/1.02  --prep_upred                            true
% 0.67/1.02  --prep_sem_filter                       exhaustive
% 0.67/1.02  --prep_sem_filter_out                   false
% 0.67/1.02  --pred_elim                             true
% 0.67/1.02  --res_sim_input                         true
% 0.67/1.02  --eq_ax_congr_red                       true
% 0.67/1.02  --pure_diseq_elim                       true
% 0.67/1.02  --brand_transform                       false
% 0.67/1.02  --non_eq_to_eq                          false
% 0.67/1.02  --prep_def_merge                        true
% 0.67/1.02  --prep_def_merge_prop_impl              false
% 0.67/1.02  --prep_def_merge_mbd                    true
% 0.67/1.02  --prep_def_merge_tr_red                 false
% 0.67/1.02  --prep_def_merge_tr_cl                  false
% 0.67/1.02  --smt_preprocessing                     true
% 0.67/1.02  --smt_ac_axioms                         fast
% 0.67/1.02  --preprocessed_out                      false
% 0.67/1.02  --preprocessed_stats                    false
% 0.67/1.02  
% 0.67/1.02  ------ Abstraction refinement Options
% 0.67/1.02  
% 0.67/1.02  --abstr_ref                             []
% 0.67/1.02  --abstr_ref_prep                        false
% 0.67/1.02  --abstr_ref_until_sat                   false
% 0.67/1.02  --abstr_ref_sig_restrict                funpre
% 0.67/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 0.67/1.02  --abstr_ref_under                       []
% 0.67/1.02  
% 0.67/1.02  ------ SAT Options
% 0.67/1.02  
% 0.67/1.02  --sat_mode                              false
% 0.67/1.02  --sat_fm_restart_options                ""
% 0.67/1.02  --sat_gr_def                            false
% 0.67/1.02  --sat_epr_types                         true
% 0.67/1.02  --sat_non_cyclic_types                  false
% 0.67/1.02  --sat_finite_models                     false
% 0.67/1.02  --sat_fm_lemmas                         false
% 0.67/1.02  --sat_fm_prep                           false
% 0.67/1.02  --sat_fm_uc_incr                        true
% 0.67/1.02  --sat_out_model                         small
% 0.67/1.02  --sat_out_clauses                       false
% 0.67/1.02  
% 0.67/1.02  ------ QBF Options
% 0.67/1.02  
% 0.67/1.02  --qbf_mode                              false
% 0.67/1.02  --qbf_elim_univ                         false
% 0.67/1.02  --qbf_dom_inst                          none
% 0.67/1.02  --qbf_dom_pre_inst                      false
% 0.67/1.02  --qbf_sk_in                             false
% 0.67/1.02  --qbf_pred_elim                         true
% 0.67/1.02  --qbf_split                             512
% 0.67/1.02  
% 0.67/1.02  ------ BMC1 Options
% 0.67/1.02  
% 0.67/1.02  --bmc1_incremental                      false
% 0.67/1.02  --bmc1_axioms                           reachable_all
% 0.67/1.02  --bmc1_min_bound                        0
% 0.67/1.02  --bmc1_max_bound                        -1
% 0.67/1.02  --bmc1_max_bound_default                -1
% 0.67/1.02  --bmc1_symbol_reachability              true
% 0.67/1.02  --bmc1_property_lemmas                  false
% 0.67/1.02  --bmc1_k_induction                      false
% 0.67/1.02  --bmc1_non_equiv_states                 false
% 0.67/1.02  --bmc1_deadlock                         false
% 0.67/1.02  --bmc1_ucm                              false
% 0.67/1.02  --bmc1_add_unsat_core                   none
% 0.67/1.02  --bmc1_unsat_core_children              false
% 0.67/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 0.67/1.02  --bmc1_out_stat                         full
% 0.67/1.02  --bmc1_ground_init                      false
% 0.67/1.02  --bmc1_pre_inst_next_state              false
% 0.67/1.02  --bmc1_pre_inst_state                   false
% 0.67/1.02  --bmc1_pre_inst_reach_state             false
% 0.67/1.02  --bmc1_out_unsat_core                   false
% 0.67/1.02  --bmc1_aig_witness_out                  false
% 0.67/1.02  --bmc1_verbose                          false
% 0.67/1.02  --bmc1_dump_clauses_tptp                false
% 0.67/1.02  --bmc1_dump_unsat_core_tptp             false
% 0.67/1.02  --bmc1_dump_file                        -
% 0.67/1.02  --bmc1_ucm_expand_uc_limit              128
% 0.67/1.02  --bmc1_ucm_n_expand_iterations          6
% 0.67/1.02  --bmc1_ucm_extend_mode                  1
% 0.67/1.02  --bmc1_ucm_init_mode                    2
% 0.67/1.02  --bmc1_ucm_cone_mode                    none
% 0.67/1.02  --bmc1_ucm_reduced_relation_type        0
% 0.67/1.02  --bmc1_ucm_relax_model                  4
% 0.67/1.02  --bmc1_ucm_full_tr_after_sat            true
% 0.67/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 0.67/1.02  --bmc1_ucm_layered_model                none
% 0.67/1.02  --bmc1_ucm_max_lemma_size               10
% 0.67/1.02  
% 0.67/1.02  ------ AIG Options
% 0.67/1.02  
% 0.67/1.02  --aig_mode                              false
% 0.67/1.02  
% 0.67/1.02  ------ Instantiation Options
% 0.67/1.02  
% 0.67/1.02  --instantiation_flag                    true
% 0.67/1.02  --inst_sos_flag                         false
% 0.67/1.02  --inst_sos_phase                        true
% 0.67/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.67/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.67/1.02  --inst_lit_sel_side                     none
% 0.67/1.02  --inst_solver_per_active                1400
% 0.67/1.02  --inst_solver_calls_frac                1.
% 0.67/1.02  --inst_passive_queue_type               priority_queues
% 0.67/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.67/1.02  --inst_passive_queues_freq              [25;2]
% 0.67/1.02  --inst_dismatching                      true
% 0.67/1.02  --inst_eager_unprocessed_to_passive     true
% 0.67/1.02  --inst_prop_sim_given                   true
% 0.67/1.02  --inst_prop_sim_new                     false
% 0.67/1.02  --inst_subs_new                         false
% 0.67/1.02  --inst_eq_res_simp                      false
% 0.67/1.02  --inst_subs_given                       false
% 0.67/1.02  --inst_orphan_elimination               true
% 0.67/1.02  --inst_learning_loop_flag               true
% 0.67/1.02  --inst_learning_start                   3000
% 0.67/1.02  --inst_learning_factor                  2
% 0.67/1.02  --inst_start_prop_sim_after_learn       3
% 0.67/1.02  --inst_sel_renew                        solver
% 0.67/1.02  --inst_lit_activity_flag                true
% 0.67/1.02  --inst_restr_to_given                   false
% 0.67/1.02  --inst_activity_threshold               500
% 0.67/1.02  --inst_out_proof                        true
% 0.67/1.02  
% 0.67/1.02  ------ Resolution Options
% 0.67/1.02  
% 0.67/1.02  --resolution_flag                       false
% 0.67/1.02  --res_lit_sel                           adaptive
% 0.67/1.02  --res_lit_sel_side                      none
% 0.67/1.02  --res_ordering                          kbo
% 0.67/1.02  --res_to_prop_solver                    active
% 0.67/1.02  --res_prop_simpl_new                    false
% 0.67/1.02  --res_prop_simpl_given                  true
% 0.67/1.02  --res_passive_queue_type                priority_queues
% 0.67/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.67/1.02  --res_passive_queues_freq               [15;5]
% 0.67/1.02  --res_forward_subs                      full
% 0.67/1.02  --res_backward_subs                     full
% 0.67/1.02  --res_forward_subs_resolution           true
% 0.67/1.02  --res_backward_subs_resolution          true
% 0.67/1.02  --res_orphan_elimination                true
% 0.67/1.02  --res_time_limit                        2.
% 0.67/1.02  --res_out_proof                         true
% 0.67/1.02  
% 0.67/1.02  ------ Superposition Options
% 0.67/1.02  
% 0.67/1.02  --superposition_flag                    true
% 0.67/1.02  --sup_passive_queue_type                priority_queues
% 0.67/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.67/1.02  --sup_passive_queues_freq               [8;1;4]
% 0.67/1.02  --demod_completeness_check              fast
% 0.67/1.02  --demod_use_ground                      true
% 0.67/1.02  --sup_to_prop_solver                    passive
% 0.67/1.02  --sup_prop_simpl_new                    true
% 0.67/1.02  --sup_prop_simpl_given                  true
% 0.67/1.02  --sup_fun_splitting                     false
% 0.67/1.02  --sup_smt_interval                      50000
% 0.67/1.02  
% 0.67/1.02  ------ Superposition Simplification Setup
% 0.67/1.02  
% 0.67/1.02  --sup_indices_passive                   []
% 0.67/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.67/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.67/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.67/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 0.67/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.67/1.02  --sup_full_bw                           [BwDemod]
% 0.67/1.02  --sup_immed_triv                        [TrivRules]
% 0.67/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.67/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.67/1.02  --sup_immed_bw_main                     []
% 0.67/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.67/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 0.67/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.67/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.67/1.02  
% 0.67/1.02  ------ Combination Options
% 0.67/1.02  
% 0.67/1.02  --comb_res_mult                         3
% 0.67/1.02  --comb_sup_mult                         2
% 0.67/1.02  --comb_inst_mult                        10
% 0.67/1.02  
% 0.67/1.02  ------ Debug Options
% 0.67/1.02  
% 0.67/1.02  --dbg_backtrace                         false
% 0.67/1.02  --dbg_dump_prop_clauses                 false
% 0.67/1.02  --dbg_dump_prop_clauses_file            -
% 0.67/1.02  --dbg_out_stat                          false
% 0.67/1.02  
% 0.67/1.02  
% 0.67/1.02  
% 0.67/1.02  
% 0.67/1.02  ------ Proving...
% 0.67/1.02  
% 0.67/1.02  
% 0.67/1.02  % SZS status Theorem for theBenchmark.p
% 0.67/1.02  
% 0.67/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 0.67/1.02  
% 0.67/1.02  fof(f8,axiom,(
% 0.67/1.02    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 0.67/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.67/1.02  
% 0.67/1.02  fof(f19,plain,(
% 0.67/1.02    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.67/1.02    inference(ennf_transformation,[],[f8])).
% 0.67/1.02  
% 0.67/1.02  fof(f35,plain,(
% 0.67/1.02    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.67/1.02    inference(cnf_transformation,[],[f19])).
% 0.67/1.02  
% 0.67/1.02  fof(f12,conjecture,(
% 0.67/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)))),
% 0.67/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.67/1.02  
% 0.67/1.02  fof(f13,negated_conjecture,(
% 0.67/1.02    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)))),
% 0.67/1.02    inference(negated_conjecture,[],[f12])).
% 0.67/1.02  
% 0.67/1.02  fof(f24,plain,(
% 0.67/1.02    ? [X0,X1,X2] : ((k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 0.67/1.02    inference(ennf_transformation,[],[f13])).
% 0.67/1.02  
% 0.67/1.02  fof(f25,plain,(
% 0.67/1.02    ? [X0,X1,X2] : (k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 0.67/1.02    inference(flattening,[],[f24])).
% 0.67/1.02  
% 0.67/1.02  fof(f26,plain,(
% 0.67/1.02    ? [X0,X1,X2] : (k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_tarski(k1_funct_1(sK2,sK0)) != k2_relset_1(k1_tarski(sK0),sK1,sK2) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2))),
% 0.67/1.02    introduced(choice_axiom,[])).
% 0.67/1.02  
% 0.67/1.02  fof(f27,plain,(
% 0.67/1.02    k1_tarski(k1_funct_1(sK2,sK0)) != k2_relset_1(k1_tarski(sK0),sK1,sK2) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_2(sK2,k1_tarski(sK0),sK1) & v1_funct_1(sK2)),
% 0.67/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f26])).
% 0.67/1.02  
% 0.67/1.02  fof(f44,plain,(
% 0.67/1.02    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 0.67/1.02    inference(cnf_transformation,[],[f27])).
% 0.67/1.02  
% 0.67/1.02  fof(f1,axiom,(
% 0.67/1.02    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.67/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.67/1.02  
% 0.67/1.02  fof(f28,plain,(
% 0.67/1.02    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.67/1.02    inference(cnf_transformation,[],[f1])).
% 0.67/1.02  
% 0.67/1.02  fof(f2,axiom,(
% 0.67/1.02    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.67/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.67/1.02  
% 0.67/1.02  fof(f29,plain,(
% 0.67/1.02    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.67/1.02    inference(cnf_transformation,[],[f2])).
% 0.67/1.02  
% 0.67/1.02  fof(f3,axiom,(
% 0.67/1.02    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.67/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.67/1.02  
% 0.67/1.02  fof(f30,plain,(
% 0.67/1.02    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.67/1.02    inference(cnf_transformation,[],[f3])).
% 0.67/1.02  
% 0.67/1.02  fof(f47,plain,(
% 0.67/1.02    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.67/1.02    inference(definition_unfolding,[],[f29,f30])).
% 0.67/1.02  
% 0.67/1.02  fof(f48,plain,(
% 0.67/1.02    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.67/1.02    inference(definition_unfolding,[],[f28,f47])).
% 0.67/1.02  
% 0.67/1.02  fof(f51,plain,(
% 0.67/1.02    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 0.67/1.02    inference(definition_unfolding,[],[f44,f48])).
% 0.67/1.02  
% 0.67/1.02  fof(f11,axiom,(
% 0.67/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,X1) = X0))),
% 0.67/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.67/1.02  
% 0.67/1.02  fof(f22,plain,(
% 0.67/1.02    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.67/1.02    inference(ennf_transformation,[],[f11])).
% 0.67/1.02  
% 0.67/1.02  fof(f23,plain,(
% 0.67/1.02    ! [X0,X1,X2] : (k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.67/1.02    inference(flattening,[],[f22])).
% 0.67/1.02  
% 0.67/1.02  fof(f40,plain,(
% 0.67/1.02    ( ! [X2,X0,X1] : (k8_relset_1(X0,X1,X2,X1) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.67/1.02    inference(cnf_transformation,[],[f23])).
% 0.67/1.02  
% 0.67/1.02  fof(f43,plain,(
% 0.67/1.02    v1_funct_2(sK2,k1_tarski(sK0),sK1)),
% 0.67/1.02    inference(cnf_transformation,[],[f27])).
% 0.67/1.02  
% 0.67/1.02  fof(f52,plain,(
% 0.67/1.02    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 0.67/1.02    inference(definition_unfolding,[],[f43,f48])).
% 0.67/1.02  
% 0.67/1.02  fof(f42,plain,(
% 0.67/1.02    v1_funct_1(sK2)),
% 0.67/1.02    inference(cnf_transformation,[],[f27])).
% 0.67/1.02  
% 0.67/1.02  fof(f45,plain,(
% 0.67/1.02    k1_xboole_0 != sK1),
% 0.67/1.02    inference(cnf_transformation,[],[f27])).
% 0.67/1.02  
% 0.67/1.02  fof(f10,axiom,(
% 0.67/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0))))),
% 0.67/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.67/1.02  
% 0.67/1.02  fof(f21,plain,(
% 0.67/1.02    ! [X0,X1,X2] : ((k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.67/1.02    inference(ennf_transformation,[],[f10])).
% 0.67/1.02  
% 0.67/1.02  fof(f39,plain,(
% 0.67/1.02    ( ! [X2,X0,X1] : (k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 0.67/1.02    inference(cnf_transformation,[],[f21])).
% 0.67/1.02  
% 0.67/1.02  fof(f9,axiom,(
% 0.67/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 0.67/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.67/1.02  
% 0.67/1.02  fof(f20,plain,(
% 0.67/1.02    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.67/1.02    inference(ennf_transformation,[],[f9])).
% 0.67/1.02  
% 0.67/1.02  fof(f37,plain,(
% 0.67/1.02    ( ! [X2,X0,X1] : (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.67/1.02    inference(cnf_transformation,[],[f20])).
% 0.67/1.02  
% 0.67/1.02  fof(f36,plain,(
% 0.67/1.02    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.67/1.02    inference(cnf_transformation,[],[f20])).
% 0.67/1.02  
% 0.67/1.02  fof(f7,axiom,(
% 0.67/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 0.67/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.67/1.02  
% 0.67/1.02  fof(f18,plain,(
% 0.67/1.02    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.67/1.02    inference(ennf_transformation,[],[f7])).
% 0.67/1.02  
% 0.67/1.02  fof(f34,plain,(
% 0.67/1.02    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.67/1.02    inference(cnf_transformation,[],[f18])).
% 0.67/1.02  
% 0.67/1.02  fof(f6,axiom,(
% 0.67/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.67/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.67/1.02  
% 0.67/1.02  fof(f17,plain,(
% 0.67/1.02    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.67/1.02    inference(ennf_transformation,[],[f6])).
% 0.67/1.02  
% 0.67/1.02  fof(f33,plain,(
% 0.67/1.02    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.67/1.02    inference(cnf_transformation,[],[f17])).
% 0.67/1.02  
% 0.67/1.02  fof(f4,axiom,(
% 0.67/1.02    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 0.67/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.67/1.02  
% 0.67/1.02  fof(f14,plain,(
% 0.67/1.02    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.67/1.02    inference(ennf_transformation,[],[f4])).
% 0.67/1.02  
% 0.67/1.02  fof(f31,plain,(
% 0.67/1.02    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.67/1.02    inference(cnf_transformation,[],[f14])).
% 0.67/1.02  
% 0.67/1.02  fof(f5,axiom,(
% 0.67/1.02    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 0.67/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.67/1.02  
% 0.67/1.02  fof(f15,plain,(
% 0.67/1.02    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.67/1.02    inference(ennf_transformation,[],[f5])).
% 0.67/1.02  
% 0.67/1.02  fof(f16,plain,(
% 0.67/1.02    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.67/1.02    inference(flattening,[],[f15])).
% 0.67/1.02  
% 0.67/1.02  fof(f32,plain,(
% 0.67/1.02    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.67/1.02    inference(cnf_transformation,[],[f16])).
% 0.67/1.02  
% 0.67/1.02  fof(f49,plain,(
% 0.67/1.02    ( ! [X0,X1] : (k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1) | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.67/1.02    inference(definition_unfolding,[],[f32,f48,f48])).
% 0.67/1.02  
% 0.67/1.02  fof(f46,plain,(
% 0.67/1.02    k1_tarski(k1_funct_1(sK2,sK0)) != k2_relset_1(k1_tarski(sK0),sK1,sK2)),
% 0.67/1.02    inference(cnf_transformation,[],[f27])).
% 0.67/1.02  
% 0.67/1.02  fof(f50,plain,(
% 0.67/1.02    k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)),
% 0.67/1.02    inference(definition_unfolding,[],[f46,f48,f48])).
% 0.67/1.02  
% 0.67/1.02  cnf(c_4,plain,
% 0.67/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.67/1.02      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 0.67/1.02      inference(cnf_transformation,[],[f35]) ).
% 0.67/1.02  
% 0.67/1.02  cnf(c_13,negated_conjecture,
% 0.67/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
% 0.67/1.02      inference(cnf_transformation,[],[f51]) ).
% 0.67/1.02  
% 0.67/1.02  cnf(c_320,plain,
% 0.67/1.02      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 0.67/1.02      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 0.67/1.02      | sK2 != X2 ),
% 0.67/1.02      inference(resolution_lifted,[status(thm)],[c_4,c_13]) ).
% 0.67/1.02  
% 0.67/1.02  cnf(c_321,plain,
% 0.67/1.02      ( k8_relset_1(X0,X1,sK2,X2) = k10_relat_1(sK2,X2)
% 0.67/1.02      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 0.67/1.02      inference(unflattening,[status(thm)],[c_320]) ).
% 0.67/1.02  
% 0.67/1.02  cnf(c_469,plain,
% 0.67/1.02      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))
% 0.67/1.02      | k8_relset_1(X0_47,X1_47,sK2,X2_47) = k10_relat_1(sK2,X2_47) ),
% 0.67/1.02      inference(subtyping,[status(esa)],[c_321]) ).
% 0.67/1.02  
% 0.67/1.02  cnf(c_642,plain,
% 0.67/1.02      ( k8_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2,X0_47) = k10_relat_1(sK2,X0_47) ),
% 0.67/1.02      inference(equality_resolution,[status(thm)],[c_469]) ).
% 0.67/1.02  
% 0.67/1.02  cnf(c_10,plain,
% 0.67/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 0.67/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.67/1.02      | ~ v1_funct_1(X0)
% 0.67/1.02      | k8_relset_1(X1,X2,X0,X2) = X1
% 0.67/1.02      | k1_xboole_0 = X2 ),
% 0.67/1.02      inference(cnf_transformation,[],[f40]) ).
% 0.67/1.02  
% 0.67/1.02  cnf(c_14,negated_conjecture,
% 0.67/1.02      ( v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
% 0.67/1.02      inference(cnf_transformation,[],[f52]) ).
% 0.67/1.02  
% 0.67/1.02  cnf(c_223,plain,
% 0.67/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.67/1.02      | ~ v1_funct_1(X0)
% 0.67/1.02      | k8_relset_1(X1,X2,X0,X2) = X1
% 0.67/1.02      | k2_enumset1(sK0,sK0,sK0,sK0) != X1
% 0.67/1.02      | sK1 != X2
% 0.67/1.02      | sK2 != X0
% 0.67/1.02      | k1_xboole_0 = X2 ),
% 0.67/1.02      inference(resolution_lifted,[status(thm)],[c_10,c_14]) ).
% 0.67/1.02  
% 0.67/1.02  cnf(c_224,plain,
% 0.67/1.02      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
% 0.67/1.02      | ~ v1_funct_1(sK2)
% 0.67/1.02      | k8_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2,sK1) = k2_enumset1(sK0,sK0,sK0,sK0)
% 0.67/1.02      | k1_xboole_0 = sK1 ),
% 0.67/1.02      inference(unflattening,[status(thm)],[c_223]) ).
% 0.67/1.02  
% 0.67/1.02  cnf(c_15,negated_conjecture,
% 0.67/1.02      ( v1_funct_1(sK2) ),
% 0.67/1.02      inference(cnf_transformation,[],[f42]) ).
% 0.67/1.02  
% 0.67/1.02  cnf(c_12,negated_conjecture,
% 0.67/1.02      ( k1_xboole_0 != sK1 ),
% 0.67/1.02      inference(cnf_transformation,[],[f45]) ).
% 0.67/1.02  
% 0.67/1.02  cnf(c_226,plain,
% 0.67/1.02      ( k8_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2,sK1) = k2_enumset1(sK0,sK0,sK0,sK0) ),
% 0.67/1.02      inference(global_propositional_subsumption,
% 0.67/1.02                [status(thm)],
% 0.67/1.02                [c_224,c_15,c_13,c_12]) ).
% 0.67/1.02  
% 0.67/1.02  cnf(c_475,plain,
% 0.67/1.02      ( k8_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2,sK1) = k2_enumset1(sK0,sK0,sK0,sK0) ),
% 0.67/1.02      inference(subtyping,[status(esa)],[c_226]) ).
% 0.67/1.02  
% 0.67/1.02  cnf(c_795,plain,
% 0.67/1.02      ( k2_enumset1(sK0,sK0,sK0,sK0) = k10_relat_1(sK2,sK1) ),
% 0.67/1.02      inference(demodulation,[status(thm)],[c_642,c_475]) ).
% 0.67/1.02  
% 0.67/1.02  cnf(c_842,plain,
% 0.67/1.02      ( k8_relset_1(k10_relat_1(sK2,sK1),sK1,sK2,X0_47) = k10_relat_1(sK2,X0_47) ),
% 0.67/1.02      inference(demodulation,[status(thm)],[c_795,c_642]) ).
% 0.67/1.02  
% 0.67/1.02  cnf(c_7,plain,
% 0.67/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.67/1.02      | k8_relset_1(X1,X2,X0,k7_relset_1(X1,X2,X0,X1)) = k1_relset_1(X1,X2,X0) ),
% 0.67/1.02      inference(cnf_transformation,[],[f39]) ).
% 0.67/1.02  
% 0.67/1.02  cnf(c_293,plain,
% 0.67/1.02      ( k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = k1_relset_1(X0,X1,X2)
% 0.67/1.02      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 0.67/1.02      | sK2 != X2 ),
% 0.67/1.02      inference(resolution_lifted,[status(thm)],[c_7,c_13]) ).
% 0.67/1.02  
% 0.67/1.02  cnf(c_294,plain,
% 0.67/1.02      ( k8_relset_1(X0,X1,sK2,k7_relset_1(X0,X1,sK2,X0)) = k1_relset_1(X0,X1,sK2)
% 0.67/1.02      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 0.67/1.02      inference(unflattening,[status(thm)],[c_293]) ).
% 0.67/1.02  
% 0.67/1.02  cnf(c_472,plain,
% 0.67/1.02      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))
% 0.67/1.02      | k8_relset_1(X0_47,X1_47,sK2,k7_relset_1(X0_47,X1_47,sK2,X0_47)) = k1_relset_1(X0_47,X1_47,sK2) ),
% 0.67/1.02      inference(subtyping,[status(esa)],[c_294]) ).
% 0.67/1.02  
% 0.67/1.02  cnf(c_846,plain,
% 0.67/1.02      ( k1_zfmisc_1(k2_zfmisc_1(k10_relat_1(sK2,sK1),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))
% 0.67/1.02      | k8_relset_1(X0_47,X1_47,sK2,k7_relset_1(X0_47,X1_47,sK2,X0_47)) = k1_relset_1(X0_47,X1_47,sK2) ),
% 0.67/1.02      inference(demodulation,[status(thm)],[c_795,c_472]) ).
% 0.67/1.02  
% 0.67/1.02  cnf(c_1199,plain,
% 0.67/1.02      ( k8_relset_1(k10_relat_1(sK2,sK1),sK1,sK2,k7_relset_1(k10_relat_1(sK2,sK1),sK1,sK2,k10_relat_1(sK2,sK1))) = k1_relset_1(k10_relat_1(sK2,sK1),sK1,sK2) ),
% 0.67/1.02      inference(equality_resolution,[status(thm)],[c_846]) ).
% 0.67/1.02  
% 0.67/1.02  cnf(c_5,plain,
% 0.67/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.67/1.02      | k8_relset_1(X1,X2,X0,X2) = k1_relset_1(X1,X2,X0) ),
% 0.67/1.02      inference(cnf_transformation,[],[f37]) ).
% 0.67/1.02  
% 0.67/1.02  cnf(c_311,plain,
% 0.67/1.02      ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
% 0.67/1.02      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 0.67/1.02      | sK2 != X2 ),
% 0.67/1.02      inference(resolution_lifted,[status(thm)],[c_5,c_13]) ).
% 0.67/1.02  
% 0.67/1.02  cnf(c_312,plain,
% 0.67/1.02      ( k8_relset_1(X0,X1,sK2,X1) = k1_relset_1(X0,X1,sK2)
% 0.67/1.02      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 0.67/1.02      inference(unflattening,[status(thm)],[c_311]) ).
% 0.67/1.02  
% 0.67/1.02  cnf(c_470,plain,
% 0.67/1.02      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))
% 0.67/1.02      | k8_relset_1(X0_47,X1_47,sK2,X1_47) = k1_relset_1(X0_47,X1_47,sK2) ),
% 0.67/1.02      inference(subtyping,[status(esa)],[c_312]) ).
% 0.67/1.02  
% 0.67/1.02  cnf(c_646,plain,
% 0.67/1.02      ( k8_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2,sK1) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) ),
% 0.67/1.02      inference(equality_resolution,[status(thm)],[c_470]) ).
% 0.67/1.02  
% 0.67/1.02  cnf(c_647,plain,
% 0.67/1.02      ( k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_enumset1(sK0,sK0,sK0,sK0) ),
% 0.67/1.02      inference(light_normalisation,[status(thm)],[c_646,c_475]) ).
% 0.67/1.02  
% 0.67/1.02  cnf(c_892,plain,
% 0.67/1.02      ( k1_relset_1(k10_relat_1(sK2,sK1),sK1,sK2) = k10_relat_1(sK2,sK1) ),
% 0.67/1.02      inference(light_normalisation,[status(thm)],[c_647,c_795]) ).
% 0.67/1.02  
% 0.67/1.02  cnf(c_6,plain,
% 0.67/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.67/1.02      | k7_relset_1(X1,X2,X0,X1) = k2_relset_1(X1,X2,X0) ),
% 0.67/1.02      inference(cnf_transformation,[],[f36]) ).
% 0.67/1.02  
% 0.67/1.02  cnf(c_302,plain,
% 0.67/1.02      ( k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)
% 0.67/1.02      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 0.67/1.02      | sK2 != X2 ),
% 0.67/1.02      inference(resolution_lifted,[status(thm)],[c_6,c_13]) ).
% 0.67/1.02  
% 0.67/1.02  cnf(c_303,plain,
% 0.67/1.02      ( k7_relset_1(X0,X1,sK2,X0) = k2_relset_1(X0,X1,sK2)
% 0.67/1.02      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 0.67/1.02      inference(unflattening,[status(thm)],[c_302]) ).
% 0.67/1.02  
% 0.67/1.02  cnf(c_471,plain,
% 0.67/1.02      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))
% 0.67/1.02      | k7_relset_1(X0_47,X1_47,sK2,X0_47) = k2_relset_1(X0_47,X1_47,sK2) ),
% 0.67/1.02      inference(subtyping,[status(esa)],[c_303]) ).
% 0.67/1.02  
% 0.67/1.02  cnf(c_669,plain,
% 0.67/1.02      ( k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2,k2_enumset1(sK0,sK0,sK0,sK0)) = k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) ),
% 0.67/1.02      inference(equality_resolution,[status(thm)],[c_471]) ).
% 0.67/1.02  
% 0.67/1.02  cnf(c_984,plain,
% 0.67/1.02      ( k7_relset_1(k10_relat_1(sK2,sK1),sK1,sK2,k10_relat_1(sK2,sK1)) = k2_relset_1(k10_relat_1(sK2,sK1),sK1,sK2) ),
% 0.67/1.02      inference(light_normalisation,[status(thm)],[c_669,c_795]) ).
% 0.67/1.02  
% 0.67/1.02  cnf(c_1200,plain,
% 0.67/1.02      ( k8_relset_1(k10_relat_1(sK2,sK1),sK1,sK2,k2_relset_1(k10_relat_1(sK2,sK1),sK1,sK2)) = k10_relat_1(sK2,sK1) ),
% 0.67/1.02      inference(light_normalisation,[status(thm)],[c_1199,c_892,c_984]) ).
% 0.67/1.02  
% 0.67/1.02  cnf(c_3,plain,
% 0.67/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.67/1.02      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 0.67/1.02      inference(cnf_transformation,[],[f34]) ).
% 0.67/1.02  
% 0.67/1.02  cnf(c_329,plain,
% 0.67/1.02      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 0.67/1.02      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 0.67/1.02      | sK2 != X2 ),
% 0.67/1.02      inference(resolution_lifted,[status(thm)],[c_3,c_13]) ).
% 0.67/1.02  
% 0.67/1.02  cnf(c_330,plain,
% 0.67/1.02      ( k2_relset_1(X0,X1,sK2) = k2_relat_1(sK2)
% 0.67/1.02      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 0.67/1.02      inference(unflattening,[status(thm)],[c_329]) ).
% 0.67/1.02  
% 0.67/1.02  cnf(c_468,plain,
% 0.67/1.02      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))
% 0.67/1.02      | k2_relset_1(X0_47,X1_47,sK2) = k2_relat_1(sK2) ),
% 0.67/1.02      inference(subtyping,[status(esa)],[c_330]) ).
% 0.67/1.02  
% 0.67/1.02  cnf(c_624,plain,
% 0.67/1.02      ( k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_relat_1(sK2) ),
% 0.67/1.02      inference(equality_resolution,[status(thm)],[c_468]) ).
% 0.67/1.02  
% 0.67/1.02  cnf(c_843,plain,
% 0.67/1.02      ( k2_relset_1(k10_relat_1(sK2,sK1),sK1,sK2) = k2_relat_1(sK2) ),
% 0.67/1.02      inference(demodulation,[status(thm)],[c_795,c_624]) ).
% 0.67/1.02  
% 0.67/1.02  cnf(c_1272,plain,
% 0.67/1.02      ( k8_relset_1(k10_relat_1(sK2,sK1),sK1,sK2,k2_relat_1(sK2)) = k10_relat_1(sK2,sK1) ),
% 0.67/1.02      inference(light_normalisation,[status(thm)],[c_1200,c_843]) ).
% 0.67/1.02  
% 0.67/1.02  cnf(c_1274,plain,
% 0.67/1.02      ( k10_relat_1(sK2,k2_relat_1(sK2)) = k10_relat_1(sK2,sK1) ),
% 0.67/1.02      inference(superposition,[status(thm)],[c_842,c_1272]) ).
% 0.67/1.02  
% 0.67/1.02  cnf(c_2,plain,
% 0.67/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.67/1.02      | v1_relat_1(X0) ),
% 0.67/1.02      inference(cnf_transformation,[],[f33]) ).
% 0.67/1.02  
% 0.67/1.02  cnf(c_338,plain,
% 0.67/1.02      ( v1_relat_1(X0)
% 0.67/1.02      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 0.67/1.02      | sK2 != X0 ),
% 0.67/1.02      inference(resolution_lifted,[status(thm)],[c_2,c_13]) ).
% 0.67/1.02  
% 0.67/1.02  cnf(c_339,plain,
% 0.67/1.02      ( v1_relat_1(sK2)
% 0.67/1.02      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 0.67/1.02      inference(unflattening,[status(thm)],[c_338]) ).
% 0.67/1.02  
% 0.67/1.02  cnf(c_467,plain,
% 0.67/1.02      ( v1_relat_1(sK2)
% 0.67/1.02      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) ),
% 0.67/1.02      inference(subtyping,[status(esa)],[c_339]) ).
% 0.67/1.02  
% 0.67/1.02  cnf(c_542,plain,
% 0.67/1.02      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))
% 0.67/1.02      | v1_relat_1(sK2) = iProver_top ),
% 0.67/1.02      inference(predicate_to_equality,[status(thm)],[c_467]) ).
% 0.67/1.02  
% 0.67/1.02  cnf(c_480,plain,( X0_50 = X0_50 ),theory(equality) ).
% 0.67/1.02  
% 0.67/1.02  cnf(c_601,plain,
% 0.67/1.02      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) = k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
% 0.67/1.02      inference(instantiation,[status(thm)],[c_480]) ).
% 0.67/1.02  
% 0.67/1.02  cnf(c_608,plain,
% 0.67/1.02      ( v1_relat_1(sK2)
% 0.67/1.02      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
% 0.67/1.02      inference(instantiation,[status(thm)],[c_467]) ).
% 0.67/1.02  
% 0.67/1.02  cnf(c_609,plain,
% 0.67/1.02      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
% 0.67/1.02      | v1_relat_1(sK2) = iProver_top ),
% 0.67/1.02      inference(predicate_to_equality,[status(thm)],[c_608]) ).
% 0.67/1.02  
% 0.67/1.02  cnf(c_924,plain,
% 0.67/1.02      ( v1_relat_1(sK2) = iProver_top ),
% 0.67/1.02      inference(global_propositional_subsumption,
% 0.67/1.02                [status(thm)],
% 0.67/1.02                [c_542,c_601,c_609]) ).
% 0.67/1.02  
% 0.67/1.02  cnf(c_0,plain,
% 0.67/1.02      ( ~ v1_relat_1(X0)
% 0.67/1.02      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 0.67/1.02      inference(cnf_transformation,[],[f31]) ).
% 0.67/1.02  
% 0.67/1.02  cnf(c_478,plain,
% 0.67/1.02      ( ~ v1_relat_1(X0_48)
% 0.67/1.02      | k10_relat_1(X0_48,k2_relat_1(X0_48)) = k1_relat_1(X0_48) ),
% 0.67/1.02      inference(subtyping,[status(esa)],[c_0]) ).
% 0.67/1.02  
% 0.67/1.02  cnf(c_540,plain,
% 0.67/1.02      ( k10_relat_1(X0_48,k2_relat_1(X0_48)) = k1_relat_1(X0_48)
% 0.67/1.02      | v1_relat_1(X0_48) != iProver_top ),
% 0.67/1.02      inference(predicate_to_equality,[status(thm)],[c_478]) ).
% 0.67/1.02  
% 0.67/1.02  cnf(c_929,plain,
% 0.67/1.02      ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
% 0.67/1.02      inference(superposition,[status(thm)],[c_924,c_540]) ).
% 0.67/1.02  
% 0.67/1.02  cnf(c_1276,plain,
% 0.67/1.02      ( k10_relat_1(sK2,sK1) = k1_relat_1(sK2) ),
% 0.67/1.02      inference(light_normalisation,[status(thm)],[c_1274,c_929]) ).
% 0.67/1.02  
% 0.67/1.02  cnf(c_1,plain,
% 0.67/1.02      ( ~ v1_funct_1(X0)
% 0.67/1.02      | ~ v1_relat_1(X0)
% 0.67/1.02      | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
% 0.67/1.02      | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
% 0.67/1.02      inference(cnf_transformation,[],[f49]) ).
% 0.67/1.02  
% 0.67/1.02  cnf(c_236,plain,
% 0.67/1.02      ( ~ v1_relat_1(X0)
% 0.67/1.02      | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
% 0.67/1.02      | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
% 0.67/1.02      | sK2 != X0 ),
% 0.67/1.02      inference(resolution_lifted,[status(thm)],[c_1,c_15]) ).
% 0.67/1.02  
% 0.67/1.02  cnf(c_237,plain,
% 0.67/1.02      ( ~ v1_relat_1(sK2)
% 0.67/1.02      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK2)
% 0.67/1.02      | k2_enumset1(k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0),k1_funct_1(sK2,X0)) = k2_relat_1(sK2) ),
% 0.67/1.02      inference(unflattening,[status(thm)],[c_236]) ).
% 0.67/1.02  
% 0.67/1.02  cnf(c_474,plain,
% 0.67/1.02      ( ~ v1_relat_1(sK2)
% 0.67/1.02      | k2_enumset1(X0_49,X0_49,X0_49,X0_49) != k1_relat_1(sK2)
% 0.67/1.02      | k2_enumset1(k1_funct_1(sK2,X0_49),k1_funct_1(sK2,X0_49),k1_funct_1(sK2,X0_49),k1_funct_1(sK2,X0_49)) = k2_relat_1(sK2) ),
% 0.67/1.02      inference(subtyping,[status(esa)],[c_237]) ).
% 0.67/1.02  
% 0.67/1.02  cnf(c_541,plain,
% 0.67/1.02      ( k2_enumset1(X0_49,X0_49,X0_49,X0_49) != k1_relat_1(sK2)
% 0.67/1.02      | k2_enumset1(k1_funct_1(sK2,X0_49),k1_funct_1(sK2,X0_49),k1_funct_1(sK2,X0_49),k1_funct_1(sK2,X0_49)) = k2_relat_1(sK2)
% 0.67/1.02      | v1_relat_1(sK2) != iProver_top ),
% 0.67/1.02      inference(predicate_to_equality,[status(thm)],[c_474]) ).
% 0.67/1.02  
% 0.67/1.02  cnf(c_1023,plain,
% 0.67/1.02      ( k2_enumset1(k1_funct_1(sK2,X0_49),k1_funct_1(sK2,X0_49),k1_funct_1(sK2,X0_49),k1_funct_1(sK2,X0_49)) = k2_relat_1(sK2)
% 0.67/1.02      | k2_enumset1(X0_49,X0_49,X0_49,X0_49) != k1_relat_1(sK2) ),
% 0.67/1.02      inference(global_propositional_subsumption,
% 0.67/1.02                [status(thm)],
% 0.67/1.02                [c_541,c_474,c_601,c_608]) ).
% 0.67/1.02  
% 0.67/1.02  cnf(c_1024,plain,
% 0.67/1.02      ( k2_enumset1(X0_49,X0_49,X0_49,X0_49) != k1_relat_1(sK2)
% 0.67/1.02      | k2_enumset1(k1_funct_1(sK2,X0_49),k1_funct_1(sK2,X0_49),k1_funct_1(sK2,X0_49),k1_funct_1(sK2,X0_49)) = k2_relat_1(sK2) ),
% 0.67/1.02      inference(renaming,[status(thm)],[c_1023]) ).
% 0.67/1.02  
% 0.67/1.02  cnf(c_1028,plain,
% 0.67/1.02      ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relat_1(sK2)
% 0.67/1.02      | k10_relat_1(sK2,sK1) != k1_relat_1(sK2) ),
% 0.67/1.02      inference(superposition,[status(thm)],[c_795,c_1024]) ).
% 0.67/1.02  
% 0.67/1.02  cnf(c_482,plain,
% 0.67/1.02      ( X0_47 != X1_47 | X2_47 != X1_47 | X2_47 = X0_47 ),
% 0.67/1.02      theory(equality) ).
% 0.67/1.02  
% 0.67/1.02  cnf(c_617,plain,
% 0.67/1.02      ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != X0_47
% 0.67/1.02      | k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)
% 0.67/1.02      | k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != X0_47 ),
% 0.67/1.02      inference(instantiation,[status(thm)],[c_482]) ).
% 0.67/1.02  
% 0.67/1.02  cnf(c_648,plain,
% 0.67/1.02      ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) = k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)
% 0.67/1.02      | k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relat_1(sK2)
% 0.67/1.02      | k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) != k2_relat_1(sK2) ),
% 0.67/1.02      inference(instantiation,[status(thm)],[c_617]) ).
% 0.67/1.02  
% 0.67/1.02  cnf(c_607,plain,
% 0.67/1.02      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
% 0.67/1.02      | k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) = k2_relat_1(sK2) ),
% 0.67/1.02      inference(instantiation,[status(thm)],[c_468]) ).
% 0.67/1.02  
% 0.67/1.02  cnf(c_11,negated_conjecture,
% 0.67/1.02      ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) ),
% 0.67/1.02      inference(cnf_transformation,[],[f50]) ).
% 0.67/1.02  
% 0.67/1.02  cnf(c_477,negated_conjecture,
% 0.67/1.02      ( k2_enumset1(k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0),k1_funct_1(sK2,sK0)) != k2_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) ),
% 0.67/1.02      inference(subtyping,[status(esa)],[c_11]) ).
% 0.67/1.02  
% 0.67/1.02  cnf(contradiction,plain,
% 0.67/1.02      ( $false ),
% 0.67/1.02      inference(minisat,
% 0.67/1.02                [status(thm)],
% 0.67/1.02                [c_1276,c_1028,c_648,c_607,c_601,c_477]) ).
% 0.67/1.02  
% 0.67/1.02  
% 0.67/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 0.67/1.02  
% 0.67/1.02  ------                               Statistics
% 0.67/1.02  
% 0.67/1.02  ------ General
% 0.67/1.02  
% 0.67/1.02  abstr_ref_over_cycles:                  0
% 0.67/1.02  abstr_ref_under_cycles:                 0
% 0.67/1.02  gc_basic_clause_elim:                   0
% 0.67/1.02  forced_gc_time:                         0
% 0.67/1.02  parsing_time:                           0.029
% 0.67/1.02  unif_index_cands_time:                  0.
% 0.67/1.02  unif_index_add_time:                    0.
% 0.67/1.02  orderings_time:                         0.
% 0.67/1.02  out_proof_time:                         0.009
% 0.67/1.02  total_time:                             0.109
% 0.67/1.02  num_of_symbols:                         52
% 0.67/1.02  num_of_terms:                           1414
% 0.67/1.02  
% 0.67/1.02  ------ Preprocessing
% 0.67/1.02  
% 0.67/1.02  num_of_splits:                          0
% 0.67/1.02  num_of_split_atoms:                     0
% 0.67/1.02  num_of_reused_defs:                     0
% 0.67/1.02  num_eq_ax_congr_red:                    34
% 0.67/1.02  num_of_sem_filtered_clauses:            0
% 0.67/1.02  num_of_subtypes:                        5
% 0.67/1.02  monotx_restored_types:                  0
% 0.67/1.02  sat_num_of_epr_types:                   0
% 0.67/1.02  sat_num_of_non_cyclic_types:            0
% 0.67/1.02  sat_guarded_non_collapsed_types:        0
% 0.67/1.02  num_pure_diseq_elim:                    0
% 0.67/1.02  simp_replaced_by:                       0
% 0.67/1.02  res_preprocessed:                       53
% 0.67/1.02  prep_upred:                             0
% 0.67/1.02  prep_unflattend:                        16
% 0.67/1.02  smt_new_axioms:                         0
% 0.67/1.02  pred_elim_cands:                        1
% 0.67/1.02  pred_elim:                              3
% 0.67/1.02  pred_elim_cl:                           3
% 0.67/1.02  pred_elim_cycles:                       7
% 0.67/1.02  merged_defs:                            0
% 0.67/1.02  merged_defs_ncl:                        0
% 0.67/1.02  bin_hyper_res:                          0
% 0.67/1.02  prep_cycles:                            3
% 0.67/1.02  pred_elim_time:                         0.008
% 0.67/1.02  splitting_time:                         0.
% 0.67/1.02  sem_filter_time:                        0.
% 0.67/1.02  monotx_time:                            0.
% 0.67/1.02  subtype_inf_time:                       0.
% 0.67/1.02  
% 0.67/1.02  ------ Problem properties
% 0.67/1.02  
% 0.67/1.02  clauses:                                13
% 0.67/1.02  conjectures:                            2
% 0.67/1.02  epr:                                    1
% 0.67/1.02  horn:                                   13
% 0.67/1.02  ground:                                 4
% 0.67/1.02  unary:                                  3
% 0.67/1.02  binary:                                 8
% 0.67/1.02  lits:                                   25
% 0.67/1.02  lits_eq:                                22
% 0.67/1.02  fd_pure:                                0
% 0.67/1.02  fd_pseudo:                              0
% 0.67/1.02  fd_cond:                                0
% 0.67/1.02  fd_pseudo_cond:                         0
% 0.67/1.02  ac_symbols:                             0
% 0.67/1.02  
% 0.67/1.02  ------ Propositional Solver
% 0.67/1.02  
% 0.67/1.02  prop_solver_calls:                      26
% 0.67/1.02  prop_fast_solver_calls:                 335
% 0.67/1.02  smt_solver_calls:                       0
% 0.67/1.02  smt_fast_solver_calls:                  0
% 0.67/1.02  prop_num_of_clauses:                    447
% 0.67/1.02  prop_preprocess_simplified:             1668
% 0.67/1.02  prop_fo_subsumed:                       7
% 0.67/1.02  prop_solver_time:                       0.
% 0.67/1.02  smt_solver_time:                        0.
% 0.67/1.02  smt_fast_solver_time:                   0.
% 0.67/1.02  prop_fast_solver_time:                  0.
% 0.67/1.02  prop_unsat_core_time:                   0.
% 0.67/1.02  
% 0.67/1.02  ------ QBF
% 0.67/1.02  
% 0.67/1.02  qbf_q_res:                              0
% 0.67/1.02  qbf_num_tautologies:                    0
% 0.67/1.02  qbf_prep_cycles:                        0
% 0.67/1.02  
% 0.67/1.02  ------ BMC1
% 0.67/1.02  
% 0.67/1.02  bmc1_current_bound:                     -1
% 0.67/1.02  bmc1_last_solved_bound:                 -1
% 0.67/1.02  bmc1_unsat_core_size:                   -1
% 0.67/1.02  bmc1_unsat_core_parents_size:           -1
% 0.67/1.02  bmc1_merge_next_fun:                    0
% 0.67/1.02  bmc1_unsat_core_clauses_time:           0.
% 0.67/1.02  
% 0.67/1.02  ------ Instantiation
% 0.67/1.02  
% 0.67/1.02  inst_num_of_clauses:                    215
% 0.67/1.02  inst_num_in_passive:                    57
% 0.67/1.02  inst_num_in_active:                     153
% 0.67/1.02  inst_num_in_unprocessed:                5
% 0.67/1.02  inst_num_of_loops:                      160
% 0.67/1.02  inst_num_of_learning_restarts:          0
% 0.67/1.02  inst_num_moves_active_passive:          2
% 0.67/1.02  inst_lit_activity:                      0
% 0.67/1.02  inst_lit_activity_moves:                0
% 0.67/1.02  inst_num_tautologies:                   0
% 0.67/1.02  inst_num_prop_implied:                  0
% 0.67/1.02  inst_num_existing_simplified:           0
% 0.67/1.02  inst_num_eq_res_simplified:             0
% 0.67/1.02  inst_num_child_elim:                    0
% 0.67/1.02  inst_num_of_dismatching_blockings:      21
% 0.67/1.02  inst_num_of_non_proper_insts:           205
% 0.67/1.02  inst_num_of_duplicates:                 0
% 0.67/1.02  inst_inst_num_from_inst_to_res:         0
% 0.67/1.02  inst_dismatching_checking_time:         0.
% 0.67/1.02  
% 0.67/1.02  ------ Resolution
% 0.67/1.02  
% 0.67/1.02  res_num_of_clauses:                     0
% 0.67/1.02  res_num_in_passive:                     0
% 0.67/1.02  res_num_in_active:                      0
% 0.67/1.02  res_num_of_loops:                       56
% 0.67/1.02  res_forward_subset_subsumed:            60
% 0.67/1.02  res_backward_subset_subsumed:           0
% 0.67/1.02  res_forward_subsumed:                   0
% 0.67/1.02  res_backward_subsumed:                  0
% 0.67/1.02  res_forward_subsumption_resolution:     0
% 0.67/1.02  res_backward_subsumption_resolution:    0
% 0.67/1.02  res_clause_to_clause_subsumption:       38
% 0.67/1.02  res_orphan_elimination:                 0
% 0.67/1.02  res_tautology_del:                      44
% 0.67/1.02  res_num_eq_res_simplified:              1
% 0.67/1.02  res_num_sel_changes:                    0
% 0.67/1.02  res_moves_from_active_to_pass:          0
% 0.67/1.02  
% 0.67/1.02  ------ Superposition
% 0.67/1.02  
% 0.67/1.02  sup_time_total:                         0.
% 0.67/1.02  sup_time_generating:                    0.
% 0.67/1.02  sup_time_sim_full:                      0.
% 0.67/1.02  sup_time_sim_immed:                     0.
% 0.67/1.02  
% 0.67/1.02  sup_num_of_clauses:                     24
% 0.67/1.02  sup_num_in_active:                      20
% 0.67/1.02  sup_num_in_passive:                     4
% 0.67/1.02  sup_num_of_loops:                       31
% 0.67/1.02  sup_fw_superposition:                   2
% 0.67/1.02  sup_bw_superposition:                   2
% 0.67/1.02  sup_immediate_simplified:               4
% 0.67/1.02  sup_given_eliminated:                   0
% 0.67/1.02  comparisons_done:                       0
% 0.67/1.02  comparisons_avoided:                    0
% 0.67/1.02  
% 0.67/1.02  ------ Simplifications
% 0.67/1.02  
% 0.67/1.02  
% 0.67/1.02  sim_fw_subset_subsumed:                 0
% 0.67/1.02  sim_bw_subset_subsumed:                 0
% 0.67/1.02  sim_fw_subsumed:                        1
% 0.67/1.02  sim_bw_subsumed:                        0
% 0.67/1.02  sim_fw_subsumption_res:                 0
% 0.67/1.02  sim_bw_subsumption_res:                 0
% 0.67/1.02  sim_tautology_del:                      0
% 0.67/1.02  sim_eq_tautology_del:                   0
% 0.67/1.02  sim_eq_res_simp:                        0
% 0.67/1.02  sim_fw_demodulated:                     1
% 0.67/1.02  sim_bw_demodulated:                     12
% 0.67/1.02  sim_light_normalised:                   10
% 0.67/1.02  sim_joinable_taut:                      0
% 0.67/1.02  sim_joinable_simp:                      0
% 0.67/1.02  sim_ac_normalised:                      0
% 0.67/1.02  sim_smt_subsumption:                    0
% 0.67/1.02  
%------------------------------------------------------------------------------
