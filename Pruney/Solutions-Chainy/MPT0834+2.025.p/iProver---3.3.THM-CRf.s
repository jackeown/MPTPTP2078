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
% DateTime   : Thu Dec  3 11:56:04 EST 2020

% Result     : Theorem 2.26s
% Output     : CNFRefutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 381 expanded)
%              Number of clauses        :   84 ( 175 expanded)
%              Number of leaves         :   17 (  66 expanded)
%              Depth                    :   15
%              Number of atoms          :  290 ( 857 expanded)
%              Number of equality atoms :  156 ( 432 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
          & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f35,plain,(
    ? [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1)
        | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f36,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1)
          | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ( k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1)
        | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ( k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1)
      | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f35,f36])).

fof(f53,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f37])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k4_xboole_0(k2_relat_1(X1),k4_xboole_0(k2_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f43,f38])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k2_relat_1(X1),X0) = k2_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k2_relat_1(X1),X0) = k2_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k2_relat_1(X1),X0) = k2_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_relat_1(X1),k4_xboole_0(k2_relat_1(X1),X0)) = k2_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f40,f38])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f44,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f54,plain,
    ( k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1)
    | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_498,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_800,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_498])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_503,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
    | k1_relset_1(X1_47,X2_47,X0_47) = k1_relat_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_796,plain,
    ( k1_relset_1(X0_47,X1_47,X2_47) = k1_relat_1(X2_47)
    | m1_subset_1(X2_47,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_503])).

cnf(c_1030,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_800,c_796])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_505,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
    | m1_subset_1(k1_relset_1(X1_47,X2_47,X0_47),k1_zfmisc_1(X1_47)) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_794,plain,
    ( m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47))) != iProver_top
    | m1_subset_1(k1_relset_1(X1_47,X2_47,X0_47),k1_zfmisc_1(X1_47)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_505])).

cnf(c_1175,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1030,c_794])).

cnf(c_16,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1356,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1175,c_16])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_6,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_205,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X2)
    | X3 != X1
    | k7_relat_1(X2,X3) = X2
    | k1_relat_1(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_6])).

cnf(c_206,plain,
    ( ~ m1_subset_1(k1_relat_1(X0),k1_zfmisc_1(X1))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(unflattening,[status(thm)],[c_205])).

cnf(c_496,plain,
    ( ~ m1_subset_1(k1_relat_1(X0_47),k1_zfmisc_1(X1_47))
    | ~ v1_relat_1(X0_47)
    | k7_relat_1(X0_47,X1_47) = X0_47 ),
    inference(subtyping,[status(esa)],[c_206])).

cnf(c_802,plain,
    ( k7_relat_1(X0_47,X1_47) = X0_47
    | m1_subset_1(k1_relat_1(X0_47),k1_zfmisc_1(X1_47)) != iProver_top
    | v1_relat_1(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_496])).

cnf(c_2750,plain,
    ( k7_relat_1(sK2,sK0) = sK2
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1356,c_802])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_506,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
    | v1_relat_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_894,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_506])).

cnf(c_895,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_894])).

cnf(c_939,plain,
    ( ~ m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(X0_47))
    | ~ v1_relat_1(sK2)
    | k7_relat_1(sK2,X0_47) = sK2 ),
    inference(instantiation,[status(thm)],[c_496])).

cnf(c_948,plain,
    ( k7_relat_1(sK2,X0_47) = sK2
    | m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(X0_47)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_939])).

cnf(c_950,plain,
    ( k7_relat_1(sK2,sK0) = sK2
    | m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_948])).

cnf(c_3121,plain,
    ( k7_relat_1(sK2,sK0) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2750,c_16,c_895,c_950,c_1175])).

cnf(c_793,plain,
    ( m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47))) != iProver_top
    | v1_relat_1(X0_47) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_506])).

cnf(c_967,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_800,c_793])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_509,plain,
    ( ~ v1_relat_1(X0_47)
    | k2_relat_1(k7_relat_1(X0_47,X1_47)) = k9_relat_1(X0_47,X1_47) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_790,plain,
    ( k2_relat_1(k7_relat_1(X0_47,X1_47)) = k9_relat_1(X0_47,X1_47)
    | v1_relat_1(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_509])).

cnf(c_971,plain,
    ( k2_relat_1(k7_relat_1(sK2,X0_47)) = k9_relat_1(sK2,X0_47) ),
    inference(superposition,[status(thm)],[c_967,c_790])).

cnf(c_3124,plain,
    ( k9_relat_1(sK2,sK0) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_3121,c_971])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_502,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
    | k2_relset_1(X1_47,X2_47,X0_47) = k2_relat_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_797,plain,
    ( k2_relset_1(X0_47,X1_47,X2_47) = k2_relat_1(X2_47)
    | m1_subset_1(X2_47,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_502])).

cnf(c_1111,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_800,c_797])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_504,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
    | m1_subset_1(k2_relset_1(X1_47,X2_47,X0_47),k1_zfmisc_1(X2_47)) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_795,plain,
    ( m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47))) != iProver_top
    | m1_subset_1(k2_relset_1(X1_47,X2_47,X0_47),k1_zfmisc_1(X2_47)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_504])).

cnf(c_1413,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1111,c_795])).

cnf(c_1629,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1413,c_16])).

cnf(c_2,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k8_relat_1(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_190,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X2)
    | X3 != X1
    | k8_relat_1(X3,X2) = X2
    | k2_relat_1(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_2])).

cnf(c_191,plain,
    ( ~ m1_subset_1(k2_relat_1(X0),k1_zfmisc_1(X1))
    | ~ v1_relat_1(X0)
    | k8_relat_1(X1,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_190])).

cnf(c_497,plain,
    ( ~ m1_subset_1(k2_relat_1(X0_47),k1_zfmisc_1(X1_47))
    | ~ v1_relat_1(X0_47)
    | k8_relat_1(X1_47,X0_47) = X0_47 ),
    inference(subtyping,[status(esa)],[c_191])).

cnf(c_801,plain,
    ( k8_relat_1(X0_47,X1_47) = X1_47
    | m1_subset_1(k2_relat_1(X1_47),k1_zfmisc_1(X0_47)) != iProver_top
    | v1_relat_1(X1_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_497])).

cnf(c_2046,plain,
    ( k8_relat_1(sK1,sK2) = sK2
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1629,c_801])).

cnf(c_1433,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1413])).

cnf(c_938,plain,
    ( ~ m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(X0_47))
    | ~ v1_relat_1(sK2)
    | k8_relat_1(X0_47,sK2) = sK2 ),
    inference(instantiation,[status(thm)],[c_497])).

cnf(c_1765,plain,
    ( ~ m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ v1_relat_1(sK2)
    | k8_relat_1(sK1,sK2) = sK2 ),
    inference(instantiation,[status(thm)],[c_938])).

cnf(c_2316,plain,
    ( k8_relat_1(sK1,sK2) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2046,c_15,c_894,c_1433,c_1765])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k4_xboole_0(k2_relat_1(X0),k4_xboole_0(k2_relat_1(X0),X1))) = k10_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_508,plain,
    ( ~ v1_relat_1(X0_47)
    | k10_relat_1(X0_47,k4_xboole_0(k2_relat_1(X0_47),k4_xboole_0(k2_relat_1(X0_47),X1_47))) = k10_relat_1(X0_47,X1_47) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_791,plain,
    ( k10_relat_1(X0_47,k4_xboole_0(k2_relat_1(X0_47),k4_xboole_0(k2_relat_1(X0_47),X1_47))) = k10_relat_1(X0_47,X1_47)
    | v1_relat_1(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_508])).

cnf(c_1171,plain,
    ( k10_relat_1(sK2,k4_xboole_0(k2_relat_1(sK2),k4_xboole_0(k2_relat_1(sK2),X0_47))) = k10_relat_1(sK2,X0_47) ),
    inference(superposition,[status(thm)],[c_967,c_791])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | k4_xboole_0(k2_relat_1(X0),k4_xboole_0(k2_relat_1(X0),X1)) = k2_relat_1(k8_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_510,plain,
    ( ~ v1_relat_1(X0_47)
    | k4_xboole_0(k2_relat_1(X0_47),k4_xboole_0(k2_relat_1(X0_47),X1_47)) = k2_relat_1(k8_relat_1(X1_47,X0_47)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_789,plain,
    ( k4_xboole_0(k2_relat_1(X0_47),k4_xboole_0(k2_relat_1(X0_47),X1_47)) = k2_relat_1(k8_relat_1(X1_47,X0_47))
    | v1_relat_1(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_510])).

cnf(c_1125,plain,
    ( k4_xboole_0(k2_relat_1(sK2),k4_xboole_0(k2_relat_1(sK2),X0_47)) = k2_relat_1(k8_relat_1(X0_47,sK2)) ),
    inference(superposition,[status(thm)],[c_967,c_789])).

cnf(c_1352,plain,
    ( k10_relat_1(sK2,k2_relat_1(k8_relat_1(X0_47,sK2))) = k10_relat_1(sK2,X0_47) ),
    inference(light_normalisation,[status(thm)],[c_1171,c_1125])).

cnf(c_2323,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k10_relat_1(sK2,sK1) ),
    inference(superposition,[status(thm)],[c_2316,c_1352])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_507,plain,
    ( ~ v1_relat_1(X0_47)
    | k10_relat_1(X0_47,k2_relat_1(X0_47)) = k1_relat_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_792,plain,
    ( k10_relat_1(X0_47,k2_relat_1(X0_47)) = k1_relat_1(X0_47)
    | v1_relat_1(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_507])).

cnf(c_972,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_967,c_792])).

cnf(c_2325,plain,
    ( k10_relat_1(sK2,sK1) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_2323,c_972])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_501,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
    | k7_relset_1(X1_47,X2_47,X0_47,X3_47) = k9_relat_1(X0_47,X3_47) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_798,plain,
    ( k7_relset_1(X0_47,X1_47,X2_47,X3_47) = k9_relat_1(X2_47,X3_47)
    | m1_subset_1(X2_47,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_501])).

cnf(c_1481,plain,
    ( k7_relset_1(sK0,sK1,sK2,X0_47) = k9_relat_1(sK2,X0_47) ),
    inference(superposition,[status(thm)],[c_800,c_798])).

cnf(c_14,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)
    | k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_499,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)
    | k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1174,plain,
    ( k8_relset_1(sK0,sK1,sK2,sK1) != k1_relat_1(sK2)
    | k7_relset_1(sK0,sK1,sK2,sK0) != k2_relset_1(sK0,sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_1030,c_499])).

cnf(c_1221,plain,
    ( k8_relset_1(sK0,sK1,sK2,sK1) != k1_relat_1(sK2)
    | k7_relset_1(sK0,sK1,sK2,sK0) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1111,c_1174])).

cnf(c_1568,plain,
    ( k8_relset_1(sK0,sK1,sK2,sK1) != k1_relat_1(sK2)
    | k9_relat_1(sK2,sK0) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1481,c_1221])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_500,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
    | k8_relset_1(X1_47,X2_47,X0_47,X3_47) = k10_relat_1(X0_47,X3_47) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_799,plain,
    ( k8_relset_1(X0_47,X1_47,X2_47,X3_47) = k10_relat_1(X2_47,X3_47)
    | m1_subset_1(X2_47,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_500])).

cnf(c_1504,plain,
    ( k8_relset_1(sK0,sK1,sK2,X0_47) = k10_relat_1(sK2,X0_47) ),
    inference(superposition,[status(thm)],[c_800,c_799])).

cnf(c_1634,plain,
    ( k10_relat_1(sK2,sK1) != k1_relat_1(sK2)
    | k9_relat_1(sK2,sK0) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1568,c_1504])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3124,c_2325,c_1634])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:32:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.26/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.26/0.99  
% 2.26/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.26/0.99  
% 2.26/0.99  ------  iProver source info
% 2.26/0.99  
% 2.26/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.26/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.26/0.99  git: non_committed_changes: false
% 2.26/0.99  git: last_make_outside_of_git: false
% 2.26/0.99  
% 2.26/0.99  ------ 
% 2.26/0.99  
% 2.26/0.99  ------ Input Options
% 2.26/0.99  
% 2.26/0.99  --out_options                           all
% 2.26/0.99  --tptp_safe_out                         true
% 2.26/0.99  --problem_path                          ""
% 2.26/0.99  --include_path                          ""
% 2.26/0.99  --clausifier                            res/vclausify_rel
% 2.26/0.99  --clausifier_options                    --mode clausify
% 2.26/0.99  --stdin                                 false
% 2.26/0.99  --stats_out                             all
% 2.26/0.99  
% 2.26/0.99  ------ General Options
% 2.26/0.99  
% 2.26/0.99  --fof                                   false
% 2.26/0.99  --time_out_real                         305.
% 2.26/0.99  --time_out_virtual                      -1.
% 2.26/0.99  --symbol_type_check                     false
% 2.26/0.99  --clausify_out                          false
% 2.26/0.99  --sig_cnt_out                           false
% 2.26/0.99  --trig_cnt_out                          false
% 2.26/0.99  --trig_cnt_out_tolerance                1.
% 2.26/0.99  --trig_cnt_out_sk_spl                   false
% 2.26/0.99  --abstr_cl_out                          false
% 2.26/0.99  
% 2.26/0.99  ------ Global Options
% 2.26/0.99  
% 2.26/0.99  --schedule                              default
% 2.26/0.99  --add_important_lit                     false
% 2.26/0.99  --prop_solver_per_cl                    1000
% 2.26/0.99  --min_unsat_core                        false
% 2.26/0.99  --soft_assumptions                      false
% 2.26/0.99  --soft_lemma_size                       3
% 2.26/0.99  --prop_impl_unit_size                   0
% 2.26/0.99  --prop_impl_unit                        []
% 2.26/0.99  --share_sel_clauses                     true
% 2.26/0.99  --reset_solvers                         false
% 2.26/0.99  --bc_imp_inh                            [conj_cone]
% 2.26/0.99  --conj_cone_tolerance                   3.
% 2.26/0.99  --extra_neg_conj                        none
% 2.26/0.99  --large_theory_mode                     true
% 2.26/0.99  --prolific_symb_bound                   200
% 2.26/0.99  --lt_threshold                          2000
% 2.26/0.99  --clause_weak_htbl                      true
% 2.26/0.99  --gc_record_bc_elim                     false
% 2.26/0.99  
% 2.26/0.99  ------ Preprocessing Options
% 2.26/0.99  
% 2.26/0.99  --preprocessing_flag                    true
% 2.26/0.99  --time_out_prep_mult                    0.1
% 2.26/0.99  --splitting_mode                        input
% 2.26/0.99  --splitting_grd                         true
% 2.26/0.99  --splitting_cvd                         false
% 2.26/0.99  --splitting_cvd_svl                     false
% 2.26/0.99  --splitting_nvd                         32
% 2.26/0.99  --sub_typing                            true
% 2.26/0.99  --prep_gs_sim                           true
% 2.26/0.99  --prep_unflatten                        true
% 2.26/0.99  --prep_res_sim                          true
% 2.26/0.99  --prep_upred                            true
% 2.26/0.99  --prep_sem_filter                       exhaustive
% 2.26/0.99  --prep_sem_filter_out                   false
% 2.26/0.99  --pred_elim                             true
% 2.26/0.99  --res_sim_input                         true
% 2.26/0.99  --eq_ax_congr_red                       true
% 2.26/0.99  --pure_diseq_elim                       true
% 2.26/0.99  --brand_transform                       false
% 2.26/0.99  --non_eq_to_eq                          false
% 2.26/0.99  --prep_def_merge                        true
% 2.26/0.99  --prep_def_merge_prop_impl              false
% 2.26/0.99  --prep_def_merge_mbd                    true
% 2.26/0.99  --prep_def_merge_tr_red                 false
% 2.26/0.99  --prep_def_merge_tr_cl                  false
% 2.26/0.99  --smt_preprocessing                     true
% 2.26/0.99  --smt_ac_axioms                         fast
% 2.26/0.99  --preprocessed_out                      false
% 2.26/0.99  --preprocessed_stats                    false
% 2.26/0.99  
% 2.26/0.99  ------ Abstraction refinement Options
% 2.26/0.99  
% 2.26/0.99  --abstr_ref                             []
% 2.26/0.99  --abstr_ref_prep                        false
% 2.26/0.99  --abstr_ref_until_sat                   false
% 2.26/0.99  --abstr_ref_sig_restrict                funpre
% 2.26/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.26/0.99  --abstr_ref_under                       []
% 2.26/0.99  
% 2.26/0.99  ------ SAT Options
% 2.26/0.99  
% 2.26/0.99  --sat_mode                              false
% 2.26/0.99  --sat_fm_restart_options                ""
% 2.26/0.99  --sat_gr_def                            false
% 2.26/0.99  --sat_epr_types                         true
% 2.26/0.99  --sat_non_cyclic_types                  false
% 2.26/0.99  --sat_finite_models                     false
% 2.26/0.99  --sat_fm_lemmas                         false
% 2.26/0.99  --sat_fm_prep                           false
% 2.26/0.99  --sat_fm_uc_incr                        true
% 2.26/0.99  --sat_out_model                         small
% 2.26/0.99  --sat_out_clauses                       false
% 2.26/0.99  
% 2.26/0.99  ------ QBF Options
% 2.26/0.99  
% 2.26/0.99  --qbf_mode                              false
% 2.26/0.99  --qbf_elim_univ                         false
% 2.26/0.99  --qbf_dom_inst                          none
% 2.26/0.99  --qbf_dom_pre_inst                      false
% 2.26/0.99  --qbf_sk_in                             false
% 2.26/0.99  --qbf_pred_elim                         true
% 2.26/0.99  --qbf_split                             512
% 2.26/0.99  
% 2.26/0.99  ------ BMC1 Options
% 2.26/0.99  
% 2.26/0.99  --bmc1_incremental                      false
% 2.26/0.99  --bmc1_axioms                           reachable_all
% 2.26/0.99  --bmc1_min_bound                        0
% 2.26/0.99  --bmc1_max_bound                        -1
% 2.26/0.99  --bmc1_max_bound_default                -1
% 2.26/0.99  --bmc1_symbol_reachability              true
% 2.26/0.99  --bmc1_property_lemmas                  false
% 2.26/0.99  --bmc1_k_induction                      false
% 2.26/0.99  --bmc1_non_equiv_states                 false
% 2.26/0.99  --bmc1_deadlock                         false
% 2.26/0.99  --bmc1_ucm                              false
% 2.26/0.99  --bmc1_add_unsat_core                   none
% 2.26/0.99  --bmc1_unsat_core_children              false
% 2.26/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.26/0.99  --bmc1_out_stat                         full
% 2.26/0.99  --bmc1_ground_init                      false
% 2.26/0.99  --bmc1_pre_inst_next_state              false
% 2.26/0.99  --bmc1_pre_inst_state                   false
% 2.26/0.99  --bmc1_pre_inst_reach_state             false
% 2.26/0.99  --bmc1_out_unsat_core                   false
% 2.26/0.99  --bmc1_aig_witness_out                  false
% 2.26/0.99  --bmc1_verbose                          false
% 2.26/0.99  --bmc1_dump_clauses_tptp                false
% 2.26/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.26/0.99  --bmc1_dump_file                        -
% 2.26/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.26/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.26/0.99  --bmc1_ucm_extend_mode                  1
% 2.26/0.99  --bmc1_ucm_init_mode                    2
% 2.26/0.99  --bmc1_ucm_cone_mode                    none
% 2.26/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.26/0.99  --bmc1_ucm_relax_model                  4
% 2.26/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.26/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.26/0.99  --bmc1_ucm_layered_model                none
% 2.26/0.99  --bmc1_ucm_max_lemma_size               10
% 2.26/0.99  
% 2.26/0.99  ------ AIG Options
% 2.26/0.99  
% 2.26/0.99  --aig_mode                              false
% 2.26/0.99  
% 2.26/0.99  ------ Instantiation Options
% 2.26/0.99  
% 2.26/0.99  --instantiation_flag                    true
% 2.26/0.99  --inst_sos_flag                         false
% 2.26/0.99  --inst_sos_phase                        true
% 2.26/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.26/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.26/0.99  --inst_lit_sel_side                     num_symb
% 2.26/0.99  --inst_solver_per_active                1400
% 2.26/0.99  --inst_solver_calls_frac                1.
% 2.26/0.99  --inst_passive_queue_type               priority_queues
% 2.26/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.26/0.99  --inst_passive_queues_freq              [25;2]
% 2.26/0.99  --inst_dismatching                      true
% 2.26/0.99  --inst_eager_unprocessed_to_passive     true
% 2.26/0.99  --inst_prop_sim_given                   true
% 2.26/0.99  --inst_prop_sim_new                     false
% 2.26/0.99  --inst_subs_new                         false
% 2.26/0.99  --inst_eq_res_simp                      false
% 2.26/0.99  --inst_subs_given                       false
% 2.26/0.99  --inst_orphan_elimination               true
% 2.26/0.99  --inst_learning_loop_flag               true
% 2.26/0.99  --inst_learning_start                   3000
% 2.26/0.99  --inst_learning_factor                  2
% 2.26/0.99  --inst_start_prop_sim_after_learn       3
% 2.26/0.99  --inst_sel_renew                        solver
% 2.26/0.99  --inst_lit_activity_flag                true
% 2.26/0.99  --inst_restr_to_given                   false
% 2.26/0.99  --inst_activity_threshold               500
% 2.26/0.99  --inst_out_proof                        true
% 2.26/0.99  
% 2.26/0.99  ------ Resolution Options
% 2.26/0.99  
% 2.26/0.99  --resolution_flag                       true
% 2.26/0.99  --res_lit_sel                           adaptive
% 2.26/0.99  --res_lit_sel_side                      none
% 2.26/0.99  --res_ordering                          kbo
% 2.26/0.99  --res_to_prop_solver                    active
% 2.26/0.99  --res_prop_simpl_new                    false
% 2.26/0.99  --res_prop_simpl_given                  true
% 2.26/0.99  --res_passive_queue_type                priority_queues
% 2.26/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.26/0.99  --res_passive_queues_freq               [15;5]
% 2.26/0.99  --res_forward_subs                      full
% 2.26/0.99  --res_backward_subs                     full
% 2.26/0.99  --res_forward_subs_resolution           true
% 2.26/0.99  --res_backward_subs_resolution          true
% 2.26/0.99  --res_orphan_elimination                true
% 2.26/0.99  --res_time_limit                        2.
% 2.26/0.99  --res_out_proof                         true
% 2.26/0.99  
% 2.26/0.99  ------ Superposition Options
% 2.26/0.99  
% 2.26/0.99  --superposition_flag                    true
% 2.26/0.99  --sup_passive_queue_type                priority_queues
% 2.26/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.26/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.26/0.99  --demod_completeness_check              fast
% 2.26/0.99  --demod_use_ground                      true
% 2.26/0.99  --sup_to_prop_solver                    passive
% 2.26/0.99  --sup_prop_simpl_new                    true
% 2.26/0.99  --sup_prop_simpl_given                  true
% 2.26/0.99  --sup_fun_splitting                     false
% 2.26/0.99  --sup_smt_interval                      50000
% 2.26/0.99  
% 2.26/0.99  ------ Superposition Simplification Setup
% 2.26/0.99  
% 2.26/0.99  --sup_indices_passive                   []
% 2.26/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.26/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.26/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.26/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.26/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.26/0.99  --sup_full_bw                           [BwDemod]
% 2.26/0.99  --sup_immed_triv                        [TrivRules]
% 2.26/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.26/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.26/0.99  --sup_immed_bw_main                     []
% 2.26/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.26/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.26/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.26/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.26/0.99  
% 2.26/0.99  ------ Combination Options
% 2.26/0.99  
% 2.26/0.99  --comb_res_mult                         3
% 2.26/0.99  --comb_sup_mult                         2
% 2.26/0.99  --comb_inst_mult                        10
% 2.26/0.99  
% 2.26/0.99  ------ Debug Options
% 2.26/0.99  
% 2.26/0.99  --dbg_backtrace                         false
% 2.26/0.99  --dbg_dump_prop_clauses                 false
% 2.26/0.99  --dbg_dump_prop_clauses_file            -
% 2.26/0.99  --dbg_out_stat                          false
% 2.26/0.99  ------ Parsing...
% 2.26/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.26/0.99  
% 2.26/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.26/0.99  
% 2.26/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.26/0.99  
% 2.26/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.26/0.99  ------ Proving...
% 2.26/0.99  ------ Problem Properties 
% 2.26/0.99  
% 2.26/0.99  
% 2.26/0.99  clauses                                 15
% 2.26/0.99  conjectures                             2
% 2.26/0.99  EPR                                     0
% 2.26/0.99  Horn                                    15
% 2.26/0.99  unary                                   1
% 2.26/0.99  binary                                  12
% 2.26/0.99  lits                                    31
% 2.26/0.99  lits eq                                 12
% 2.26/0.99  fd_pure                                 0
% 2.26/0.99  fd_pseudo                               0
% 2.26/0.99  fd_cond                                 0
% 2.26/0.99  fd_pseudo_cond                          0
% 2.26/0.99  AC symbols                              0
% 2.26/0.99  
% 2.26/0.99  ------ Schedule dynamic 5 is on 
% 2.26/0.99  
% 2.26/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.26/0.99  
% 2.26/0.99  
% 2.26/0.99  ------ 
% 2.26/0.99  Current options:
% 2.26/0.99  ------ 
% 2.26/0.99  
% 2.26/0.99  ------ Input Options
% 2.26/0.99  
% 2.26/0.99  --out_options                           all
% 2.26/0.99  --tptp_safe_out                         true
% 2.26/0.99  --problem_path                          ""
% 2.26/0.99  --include_path                          ""
% 2.26/0.99  --clausifier                            res/vclausify_rel
% 2.26/0.99  --clausifier_options                    --mode clausify
% 2.26/0.99  --stdin                                 false
% 2.26/0.99  --stats_out                             all
% 2.26/0.99  
% 2.26/0.99  ------ General Options
% 2.26/0.99  
% 2.26/0.99  --fof                                   false
% 2.26/0.99  --time_out_real                         305.
% 2.26/0.99  --time_out_virtual                      -1.
% 2.26/0.99  --symbol_type_check                     false
% 2.26/0.99  --clausify_out                          false
% 2.26/0.99  --sig_cnt_out                           false
% 2.26/0.99  --trig_cnt_out                          false
% 2.26/0.99  --trig_cnt_out_tolerance                1.
% 2.26/0.99  --trig_cnt_out_sk_spl                   false
% 2.26/0.99  --abstr_cl_out                          false
% 2.26/0.99  
% 2.26/0.99  ------ Global Options
% 2.26/0.99  
% 2.26/0.99  --schedule                              default
% 2.26/0.99  --add_important_lit                     false
% 2.26/0.99  --prop_solver_per_cl                    1000
% 2.26/0.99  --min_unsat_core                        false
% 2.26/0.99  --soft_assumptions                      false
% 2.26/0.99  --soft_lemma_size                       3
% 2.26/0.99  --prop_impl_unit_size                   0
% 2.26/0.99  --prop_impl_unit                        []
% 2.26/0.99  --share_sel_clauses                     true
% 2.26/0.99  --reset_solvers                         false
% 2.26/0.99  --bc_imp_inh                            [conj_cone]
% 2.26/0.99  --conj_cone_tolerance                   3.
% 2.26/0.99  --extra_neg_conj                        none
% 2.26/0.99  --large_theory_mode                     true
% 2.26/0.99  --prolific_symb_bound                   200
% 2.26/0.99  --lt_threshold                          2000
% 2.26/0.99  --clause_weak_htbl                      true
% 2.26/0.99  --gc_record_bc_elim                     false
% 2.26/0.99  
% 2.26/0.99  ------ Preprocessing Options
% 2.26/0.99  
% 2.26/0.99  --preprocessing_flag                    true
% 2.26/0.99  --time_out_prep_mult                    0.1
% 2.26/0.99  --splitting_mode                        input
% 2.26/0.99  --splitting_grd                         true
% 2.26/0.99  --splitting_cvd                         false
% 2.26/0.99  --splitting_cvd_svl                     false
% 2.26/0.99  --splitting_nvd                         32
% 2.26/0.99  --sub_typing                            true
% 2.26/0.99  --prep_gs_sim                           true
% 2.26/0.99  --prep_unflatten                        true
% 2.26/0.99  --prep_res_sim                          true
% 2.26/0.99  --prep_upred                            true
% 2.26/0.99  --prep_sem_filter                       exhaustive
% 2.26/0.99  --prep_sem_filter_out                   false
% 2.26/0.99  --pred_elim                             true
% 2.26/0.99  --res_sim_input                         true
% 2.26/0.99  --eq_ax_congr_red                       true
% 2.26/0.99  --pure_diseq_elim                       true
% 2.26/0.99  --brand_transform                       false
% 2.26/0.99  --non_eq_to_eq                          false
% 2.26/0.99  --prep_def_merge                        true
% 2.26/0.99  --prep_def_merge_prop_impl              false
% 2.26/0.99  --prep_def_merge_mbd                    true
% 2.26/0.99  --prep_def_merge_tr_red                 false
% 2.26/0.99  --prep_def_merge_tr_cl                  false
% 2.26/0.99  --smt_preprocessing                     true
% 2.26/0.99  --smt_ac_axioms                         fast
% 2.26/0.99  --preprocessed_out                      false
% 2.26/0.99  --preprocessed_stats                    false
% 2.26/0.99  
% 2.26/0.99  ------ Abstraction refinement Options
% 2.26/0.99  
% 2.26/0.99  --abstr_ref                             []
% 2.26/0.99  --abstr_ref_prep                        false
% 2.26/0.99  --abstr_ref_until_sat                   false
% 2.26/0.99  --abstr_ref_sig_restrict                funpre
% 2.26/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.26/0.99  --abstr_ref_under                       []
% 2.26/0.99  
% 2.26/0.99  ------ SAT Options
% 2.26/0.99  
% 2.26/0.99  --sat_mode                              false
% 2.26/0.99  --sat_fm_restart_options                ""
% 2.26/0.99  --sat_gr_def                            false
% 2.26/0.99  --sat_epr_types                         true
% 2.26/0.99  --sat_non_cyclic_types                  false
% 2.26/0.99  --sat_finite_models                     false
% 2.26/0.99  --sat_fm_lemmas                         false
% 2.26/0.99  --sat_fm_prep                           false
% 2.26/0.99  --sat_fm_uc_incr                        true
% 2.26/0.99  --sat_out_model                         small
% 2.26/0.99  --sat_out_clauses                       false
% 2.26/0.99  
% 2.26/0.99  ------ QBF Options
% 2.26/0.99  
% 2.26/0.99  --qbf_mode                              false
% 2.26/0.99  --qbf_elim_univ                         false
% 2.26/0.99  --qbf_dom_inst                          none
% 2.26/0.99  --qbf_dom_pre_inst                      false
% 2.26/0.99  --qbf_sk_in                             false
% 2.26/0.99  --qbf_pred_elim                         true
% 2.26/0.99  --qbf_split                             512
% 2.26/0.99  
% 2.26/0.99  ------ BMC1 Options
% 2.26/0.99  
% 2.26/0.99  --bmc1_incremental                      false
% 2.26/0.99  --bmc1_axioms                           reachable_all
% 2.26/0.99  --bmc1_min_bound                        0
% 2.26/0.99  --bmc1_max_bound                        -1
% 2.26/0.99  --bmc1_max_bound_default                -1
% 2.26/0.99  --bmc1_symbol_reachability              true
% 2.26/0.99  --bmc1_property_lemmas                  false
% 2.26/0.99  --bmc1_k_induction                      false
% 2.26/0.99  --bmc1_non_equiv_states                 false
% 2.26/0.99  --bmc1_deadlock                         false
% 2.26/0.99  --bmc1_ucm                              false
% 2.26/0.99  --bmc1_add_unsat_core                   none
% 2.26/0.99  --bmc1_unsat_core_children              false
% 2.26/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.26/0.99  --bmc1_out_stat                         full
% 2.26/0.99  --bmc1_ground_init                      false
% 2.26/0.99  --bmc1_pre_inst_next_state              false
% 2.26/0.99  --bmc1_pre_inst_state                   false
% 2.26/0.99  --bmc1_pre_inst_reach_state             false
% 2.26/0.99  --bmc1_out_unsat_core                   false
% 2.26/0.99  --bmc1_aig_witness_out                  false
% 2.26/0.99  --bmc1_verbose                          false
% 2.26/0.99  --bmc1_dump_clauses_tptp                false
% 2.26/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.26/0.99  --bmc1_dump_file                        -
% 2.26/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.26/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.26/0.99  --bmc1_ucm_extend_mode                  1
% 2.26/0.99  --bmc1_ucm_init_mode                    2
% 2.26/0.99  --bmc1_ucm_cone_mode                    none
% 2.26/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.26/0.99  --bmc1_ucm_relax_model                  4
% 2.26/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.26/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.26/0.99  --bmc1_ucm_layered_model                none
% 2.26/0.99  --bmc1_ucm_max_lemma_size               10
% 2.26/0.99  
% 2.26/0.99  ------ AIG Options
% 2.26/0.99  
% 2.26/0.99  --aig_mode                              false
% 2.26/0.99  
% 2.26/0.99  ------ Instantiation Options
% 2.26/0.99  
% 2.26/0.99  --instantiation_flag                    true
% 2.26/0.99  --inst_sos_flag                         false
% 2.26/0.99  --inst_sos_phase                        true
% 2.26/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.26/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.26/0.99  --inst_lit_sel_side                     none
% 2.26/0.99  --inst_solver_per_active                1400
% 2.26/0.99  --inst_solver_calls_frac                1.
% 2.26/0.99  --inst_passive_queue_type               priority_queues
% 2.26/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.26/0.99  --inst_passive_queues_freq              [25;2]
% 2.26/0.99  --inst_dismatching                      true
% 2.26/0.99  --inst_eager_unprocessed_to_passive     true
% 2.26/0.99  --inst_prop_sim_given                   true
% 2.26/0.99  --inst_prop_sim_new                     false
% 2.26/0.99  --inst_subs_new                         false
% 2.26/0.99  --inst_eq_res_simp                      false
% 2.26/0.99  --inst_subs_given                       false
% 2.26/0.99  --inst_orphan_elimination               true
% 2.26/0.99  --inst_learning_loop_flag               true
% 2.26/0.99  --inst_learning_start                   3000
% 2.26/0.99  --inst_learning_factor                  2
% 2.26/0.99  --inst_start_prop_sim_after_learn       3
% 2.26/0.99  --inst_sel_renew                        solver
% 2.26/0.99  --inst_lit_activity_flag                true
% 2.26/0.99  --inst_restr_to_given                   false
% 2.26/0.99  --inst_activity_threshold               500
% 2.26/0.99  --inst_out_proof                        true
% 2.26/0.99  
% 2.26/0.99  ------ Resolution Options
% 2.26/0.99  
% 2.26/0.99  --resolution_flag                       false
% 2.26/0.99  --res_lit_sel                           adaptive
% 2.26/0.99  --res_lit_sel_side                      none
% 2.26/0.99  --res_ordering                          kbo
% 2.26/0.99  --res_to_prop_solver                    active
% 2.26/0.99  --res_prop_simpl_new                    false
% 2.26/0.99  --res_prop_simpl_given                  true
% 2.26/0.99  --res_passive_queue_type                priority_queues
% 2.26/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.26/0.99  --res_passive_queues_freq               [15;5]
% 2.26/0.99  --res_forward_subs                      full
% 2.26/0.99  --res_backward_subs                     full
% 2.26/0.99  --res_forward_subs_resolution           true
% 2.26/0.99  --res_backward_subs_resolution          true
% 2.26/0.99  --res_orphan_elimination                true
% 2.26/0.99  --res_time_limit                        2.
% 2.26/0.99  --res_out_proof                         true
% 2.26/0.99  
% 2.26/0.99  ------ Superposition Options
% 2.26/0.99  
% 2.26/0.99  --superposition_flag                    true
% 2.26/0.99  --sup_passive_queue_type                priority_queues
% 2.26/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.26/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.26/0.99  --demod_completeness_check              fast
% 2.26/0.99  --demod_use_ground                      true
% 2.26/0.99  --sup_to_prop_solver                    passive
% 2.26/0.99  --sup_prop_simpl_new                    true
% 2.26/0.99  --sup_prop_simpl_given                  true
% 2.26/0.99  --sup_fun_splitting                     false
% 2.26/0.99  --sup_smt_interval                      50000
% 2.26/0.99  
% 2.26/0.99  ------ Superposition Simplification Setup
% 2.26/0.99  
% 2.26/0.99  --sup_indices_passive                   []
% 2.26/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.26/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.26/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.26/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.26/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.26/0.99  --sup_full_bw                           [BwDemod]
% 2.26/0.99  --sup_immed_triv                        [TrivRules]
% 2.26/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.26/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.26/0.99  --sup_immed_bw_main                     []
% 2.26/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.26/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.26/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.26/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.26/0.99  
% 2.26/0.99  ------ Combination Options
% 2.26/0.99  
% 2.26/0.99  --comb_res_mult                         3
% 2.26/0.99  --comb_sup_mult                         2
% 2.26/0.99  --comb_inst_mult                        10
% 2.26/0.99  
% 2.26/0.99  ------ Debug Options
% 2.26/0.99  
% 2.26/0.99  --dbg_backtrace                         false
% 2.26/0.99  --dbg_dump_prop_clauses                 false
% 2.26/0.99  --dbg_dump_prop_clauses_file            -
% 2.26/0.99  --dbg_out_stat                          false
% 2.26/0.99  
% 2.26/0.99  
% 2.26/0.99  
% 2.26/0.99  
% 2.26/0.99  ------ Proving...
% 2.26/0.99  
% 2.26/0.99  
% 2.26/0.99  % SZS status Theorem for theBenchmark.p
% 2.26/0.99  
% 2.26/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.26/0.99  
% 2.26/0.99  fof(f16,conjecture,(
% 2.26/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 2.26/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.26/0.99  
% 2.26/0.99  fof(f17,negated_conjecture,(
% 2.26/0.99    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 2.26/0.99    inference(negated_conjecture,[],[f16])).
% 2.26/0.99  
% 2.26/0.99  fof(f35,plain,(
% 2.26/0.99    ? [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1) | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.26/0.99    inference(ennf_transformation,[],[f17])).
% 2.26/0.99  
% 2.26/0.99  fof(f36,plain,(
% 2.26/0.99    ? [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) != k8_relset_1(X0,X1,X2,X1) | k2_relset_1(X0,X1,X2) != k7_relset_1(X0,X1,X2,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => ((k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 2.26/0.99    introduced(choice_axiom,[])).
% 2.26/0.99  
% 2.26/0.99  fof(f37,plain,(
% 2.26/0.99    (k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.26/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f35,f36])).
% 2.26/0.99  
% 2.26/0.99  fof(f53,plain,(
% 2.26/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.26/0.99    inference(cnf_transformation,[],[f37])).
% 2.26/0.99  
% 2.26/0.99  fof(f12,axiom,(
% 2.26/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.26/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.26/0.99  
% 2.26/0.99  fof(f31,plain,(
% 2.26/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.26/0.99    inference(ennf_transformation,[],[f12])).
% 2.26/0.99  
% 2.26/0.99  fof(f49,plain,(
% 2.26/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.26/0.99    inference(cnf_transformation,[],[f31])).
% 2.26/0.99  
% 2.26/0.99  fof(f10,axiom,(
% 2.26/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 2.26/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.26/0.99  
% 2.26/0.99  fof(f29,plain,(
% 2.26/0.99    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.26/0.99    inference(ennf_transformation,[],[f10])).
% 2.26/0.99  
% 2.26/0.99  fof(f47,plain,(
% 2.26/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.26/0.99    inference(cnf_transformation,[],[f29])).
% 2.26/0.99  
% 2.26/0.99  fof(f2,axiom,(
% 2.26/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.26/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.26/0.99  
% 2.26/0.99  fof(f18,plain,(
% 2.26/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 2.26/0.99    inference(unused_predicate_definition_removal,[],[f2])).
% 2.26/0.99  
% 2.26/0.99  fof(f19,plain,(
% 2.26/0.99    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 2.26/0.99    inference(ennf_transformation,[],[f18])).
% 2.26/0.99  
% 2.26/0.99  fof(f39,plain,(
% 2.26/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.26/0.99    inference(cnf_transformation,[],[f19])).
% 2.26/0.99  
% 2.26/0.99  fof(f8,axiom,(
% 2.26/0.99    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 2.26/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.26/0.99  
% 2.26/0.99  fof(f26,plain,(
% 2.26/0.99    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.26/0.99    inference(ennf_transformation,[],[f8])).
% 2.26/0.99  
% 2.26/0.99  fof(f27,plain,(
% 2.26/0.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 2.26/0.99    inference(flattening,[],[f26])).
% 2.26/0.99  
% 2.26/0.99  fof(f45,plain,(
% 2.26/0.99    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.26/0.99    inference(cnf_transformation,[],[f27])).
% 2.26/0.99  
% 2.26/0.99  fof(f9,axiom,(
% 2.26/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.26/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.26/0.99  
% 2.26/0.99  fof(f28,plain,(
% 2.26/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.26/0.99    inference(ennf_transformation,[],[f9])).
% 2.26/0.99  
% 2.26/0.99  fof(f46,plain,(
% 2.26/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.26/0.99    inference(cnf_transformation,[],[f28])).
% 2.26/0.99  
% 2.26/0.99  fof(f5,axiom,(
% 2.26/0.99    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 2.26/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.26/0.99  
% 2.26/0.99  fof(f23,plain,(
% 2.26/0.99    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.26/0.99    inference(ennf_transformation,[],[f5])).
% 2.26/0.99  
% 2.26/0.99  fof(f42,plain,(
% 2.26/0.99    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.26/0.99    inference(cnf_transformation,[],[f23])).
% 2.26/0.99  
% 2.26/0.99  fof(f13,axiom,(
% 2.26/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.26/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.26/0.99  
% 2.26/0.99  fof(f32,plain,(
% 2.26/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.26/0.99    inference(ennf_transformation,[],[f13])).
% 2.26/0.99  
% 2.26/0.99  fof(f50,plain,(
% 2.26/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.26/0.99    inference(cnf_transformation,[],[f32])).
% 2.26/0.99  
% 2.26/0.99  fof(f11,axiom,(
% 2.26/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 2.26/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.26/0.99  
% 2.26/0.99  fof(f30,plain,(
% 2.26/0.99    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.26/0.99    inference(ennf_transformation,[],[f11])).
% 2.26/0.99  
% 2.26/0.99  fof(f48,plain,(
% 2.26/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.26/0.99    inference(cnf_transformation,[],[f30])).
% 2.26/0.99  
% 2.26/0.99  fof(f4,axiom,(
% 2.26/0.99    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 2.26/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.26/0.99  
% 2.26/0.99  fof(f21,plain,(
% 2.26/0.99    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.26/0.99    inference(ennf_transformation,[],[f4])).
% 2.26/0.99  
% 2.26/0.99  fof(f22,plain,(
% 2.26/0.99    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 2.26/0.99    inference(flattening,[],[f21])).
% 2.26/0.99  
% 2.26/0.99  fof(f41,plain,(
% 2.26/0.99    ( ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.26/0.99    inference(cnf_transformation,[],[f22])).
% 2.26/0.99  
% 2.26/0.99  fof(f6,axiom,(
% 2.26/0.99    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 2.26/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.26/0.99  
% 2.26/0.99  fof(f24,plain,(
% 2.26/0.99    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.26/0.99    inference(ennf_transformation,[],[f6])).
% 2.26/0.99  
% 2.26/0.99  fof(f43,plain,(
% 2.26/0.99    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 2.26/0.99    inference(cnf_transformation,[],[f24])).
% 2.26/0.99  
% 2.26/0.99  fof(f1,axiom,(
% 2.26/0.99    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 2.26/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.26/0.99  
% 2.26/0.99  fof(f38,plain,(
% 2.26/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 2.26/0.99    inference(cnf_transformation,[],[f1])).
% 2.26/0.99  
% 2.26/0.99  fof(f56,plain,(
% 2.26/0.99    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k4_xboole_0(k2_relat_1(X1),k4_xboole_0(k2_relat_1(X1),X0))) | ~v1_relat_1(X1)) )),
% 2.26/0.99    inference(definition_unfolding,[],[f43,f38])).
% 2.26/0.99  
% 2.26/0.99  fof(f3,axiom,(
% 2.26/0.99    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k2_relat_1(X1),X0) = k2_relat_1(k8_relat_1(X0,X1)))),
% 2.26/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.26/0.99  
% 2.26/0.99  fof(f20,plain,(
% 2.26/0.99    ! [X0,X1] : (k3_xboole_0(k2_relat_1(X1),X0) = k2_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 2.26/0.99    inference(ennf_transformation,[],[f3])).
% 2.26/0.99  
% 2.26/0.99  fof(f40,plain,(
% 2.26/0.99    ( ! [X0,X1] : (k3_xboole_0(k2_relat_1(X1),X0) = k2_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 2.26/0.99    inference(cnf_transformation,[],[f20])).
% 2.26/0.99  
% 2.26/0.99  fof(f55,plain,(
% 2.26/0.99    ( ! [X0,X1] : (k4_xboole_0(k2_relat_1(X1),k4_xboole_0(k2_relat_1(X1),X0)) = k2_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 2.26/0.99    inference(definition_unfolding,[],[f40,f38])).
% 2.26/0.99  
% 2.26/0.99  fof(f7,axiom,(
% 2.26/0.99    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 2.26/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.26/0.99  
% 2.26/0.99  fof(f25,plain,(
% 2.26/0.99    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 2.26/0.99    inference(ennf_transformation,[],[f7])).
% 2.26/0.99  
% 2.26/0.99  fof(f44,plain,(
% 2.26/0.99    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.26/0.99    inference(cnf_transformation,[],[f25])).
% 2.26/0.99  
% 2.26/0.99  fof(f14,axiom,(
% 2.26/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 2.26/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.26/0.99  
% 2.26/0.99  fof(f33,plain,(
% 2.26/0.99    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.26/0.99    inference(ennf_transformation,[],[f14])).
% 2.26/0.99  
% 2.26/0.99  fof(f51,plain,(
% 2.26/0.99    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.26/0.99    inference(cnf_transformation,[],[f33])).
% 2.26/0.99  
% 2.26/0.99  fof(f54,plain,(
% 2.26/0.99    k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) | k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)),
% 2.26/0.99    inference(cnf_transformation,[],[f37])).
% 2.26/0.99  
% 2.26/0.99  fof(f15,axiom,(
% 2.26/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 2.26/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.26/0.99  
% 2.26/0.99  fof(f34,plain,(
% 2.26/0.99    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.26/0.99    inference(ennf_transformation,[],[f15])).
% 2.26/0.99  
% 2.26/0.99  fof(f52,plain,(
% 2.26/0.99    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.26/0.99    inference(cnf_transformation,[],[f34])).
% 2.26/0.99  
% 2.26/0.99  cnf(c_15,negated_conjecture,
% 2.26/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.26/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_498,negated_conjecture,
% 2.26/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.26/0.99      inference(subtyping,[status(esa)],[c_15]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_800,plain,
% 2.26/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.26/0.99      inference(predicate_to_equality,[status(thm)],[c_498]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_10,plain,
% 2.26/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.26/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.26/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_503,plain,
% 2.26/0.99      ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
% 2.26/0.99      | k1_relset_1(X1_47,X2_47,X0_47) = k1_relat_1(X0_47) ),
% 2.26/0.99      inference(subtyping,[status(esa)],[c_10]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_796,plain,
% 2.26/0.99      ( k1_relset_1(X0_47,X1_47,X2_47) = k1_relat_1(X2_47)
% 2.26/0.99      | m1_subset_1(X2_47,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top ),
% 2.26/0.99      inference(predicate_to_equality,[status(thm)],[c_503]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_1030,plain,
% 2.26/0.99      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 2.26/0.99      inference(superposition,[status(thm)],[c_800,c_796]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_8,plain,
% 2.26/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.26/0.99      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 2.26/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_505,plain,
% 2.26/0.99      ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
% 2.26/0.99      | m1_subset_1(k1_relset_1(X1_47,X2_47,X0_47),k1_zfmisc_1(X1_47)) ),
% 2.26/0.99      inference(subtyping,[status(esa)],[c_8]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_794,plain,
% 2.26/0.99      ( m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47))) != iProver_top
% 2.26/0.99      | m1_subset_1(k1_relset_1(X1_47,X2_47,X0_47),k1_zfmisc_1(X1_47)) = iProver_top ),
% 2.26/0.99      inference(predicate_to_equality,[status(thm)],[c_505]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_1175,plain,
% 2.26/0.99      ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) = iProver_top
% 2.26/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 2.26/0.99      inference(superposition,[status(thm)],[c_1030,c_794]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_16,plain,
% 2.26/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.26/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_1356,plain,
% 2.26/0.99      ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) = iProver_top ),
% 2.26/0.99      inference(global_propositional_subsumption,
% 2.26/0.99                [status(thm)],
% 2.26/0.99                [c_1175,c_16]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_0,plain,
% 2.26/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.26/0.99      inference(cnf_transformation,[],[f39]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_6,plain,
% 2.26/0.99      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 2.26/0.99      | ~ v1_relat_1(X0)
% 2.26/0.99      | k7_relat_1(X0,X1) = X0 ),
% 2.26/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_205,plain,
% 2.26/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.26/0.99      | ~ v1_relat_1(X2)
% 2.26/0.99      | X3 != X1
% 2.26/0.99      | k7_relat_1(X2,X3) = X2
% 2.26/0.99      | k1_relat_1(X2) != X0 ),
% 2.26/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_6]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_206,plain,
% 2.26/0.99      ( ~ m1_subset_1(k1_relat_1(X0),k1_zfmisc_1(X1))
% 2.26/0.99      | ~ v1_relat_1(X0)
% 2.26/0.99      | k7_relat_1(X0,X1) = X0 ),
% 2.26/0.99      inference(unflattening,[status(thm)],[c_205]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_496,plain,
% 2.26/0.99      ( ~ m1_subset_1(k1_relat_1(X0_47),k1_zfmisc_1(X1_47))
% 2.26/0.99      | ~ v1_relat_1(X0_47)
% 2.26/0.99      | k7_relat_1(X0_47,X1_47) = X0_47 ),
% 2.26/0.99      inference(subtyping,[status(esa)],[c_206]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_802,plain,
% 2.26/0.99      ( k7_relat_1(X0_47,X1_47) = X0_47
% 2.26/0.99      | m1_subset_1(k1_relat_1(X0_47),k1_zfmisc_1(X1_47)) != iProver_top
% 2.26/0.99      | v1_relat_1(X0_47) != iProver_top ),
% 2.26/0.99      inference(predicate_to_equality,[status(thm)],[c_496]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_2750,plain,
% 2.26/0.99      ( k7_relat_1(sK2,sK0) = sK2 | v1_relat_1(sK2) != iProver_top ),
% 2.26/0.99      inference(superposition,[status(thm)],[c_1356,c_802]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_7,plain,
% 2.26/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.26/0.99      | v1_relat_1(X0) ),
% 2.26/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_506,plain,
% 2.26/0.99      ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
% 2.26/0.99      | v1_relat_1(X0_47) ),
% 2.26/0.99      inference(subtyping,[status(esa)],[c_7]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_894,plain,
% 2.26/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.26/0.99      | v1_relat_1(sK2) ),
% 2.26/0.99      inference(instantiation,[status(thm)],[c_506]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_895,plain,
% 2.26/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.26/0.99      | v1_relat_1(sK2) = iProver_top ),
% 2.26/0.99      inference(predicate_to_equality,[status(thm)],[c_894]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_939,plain,
% 2.26/0.99      ( ~ m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(X0_47))
% 2.26/0.99      | ~ v1_relat_1(sK2)
% 2.26/0.99      | k7_relat_1(sK2,X0_47) = sK2 ),
% 2.26/0.99      inference(instantiation,[status(thm)],[c_496]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_948,plain,
% 2.26/0.99      ( k7_relat_1(sK2,X0_47) = sK2
% 2.26/0.99      | m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(X0_47)) != iProver_top
% 2.26/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.26/0.99      inference(predicate_to_equality,[status(thm)],[c_939]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_950,plain,
% 2.26/0.99      ( k7_relat_1(sK2,sK0) = sK2
% 2.26/0.99      | m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) != iProver_top
% 2.26/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.26/0.99      inference(instantiation,[status(thm)],[c_948]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_3121,plain,
% 2.26/0.99      ( k7_relat_1(sK2,sK0) = sK2 ),
% 2.26/0.99      inference(global_propositional_subsumption,
% 2.26/0.99                [status(thm)],
% 2.26/0.99                [c_2750,c_16,c_895,c_950,c_1175]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_793,plain,
% 2.26/0.99      ( m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47))) != iProver_top
% 2.26/0.99      | v1_relat_1(X0_47) = iProver_top ),
% 2.26/0.99      inference(predicate_to_equality,[status(thm)],[c_506]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_967,plain,
% 2.26/0.99      ( v1_relat_1(sK2) = iProver_top ),
% 2.26/0.99      inference(superposition,[status(thm)],[c_800,c_793]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_3,plain,
% 2.26/0.99      ( ~ v1_relat_1(X0)
% 2.26/0.99      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 2.26/0.99      inference(cnf_transformation,[],[f42]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_509,plain,
% 2.26/0.99      ( ~ v1_relat_1(X0_47)
% 2.26/0.99      | k2_relat_1(k7_relat_1(X0_47,X1_47)) = k9_relat_1(X0_47,X1_47) ),
% 2.26/0.99      inference(subtyping,[status(esa)],[c_3]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_790,plain,
% 2.26/0.99      ( k2_relat_1(k7_relat_1(X0_47,X1_47)) = k9_relat_1(X0_47,X1_47)
% 2.26/0.99      | v1_relat_1(X0_47) != iProver_top ),
% 2.26/0.99      inference(predicate_to_equality,[status(thm)],[c_509]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_971,plain,
% 2.26/0.99      ( k2_relat_1(k7_relat_1(sK2,X0_47)) = k9_relat_1(sK2,X0_47) ),
% 2.26/0.99      inference(superposition,[status(thm)],[c_967,c_790]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_3124,plain,
% 2.26/0.99      ( k9_relat_1(sK2,sK0) = k2_relat_1(sK2) ),
% 2.26/0.99      inference(superposition,[status(thm)],[c_3121,c_971]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_11,plain,
% 2.26/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.26/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.26/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_502,plain,
% 2.26/0.99      ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
% 2.26/0.99      | k2_relset_1(X1_47,X2_47,X0_47) = k2_relat_1(X0_47) ),
% 2.26/0.99      inference(subtyping,[status(esa)],[c_11]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_797,plain,
% 2.26/0.99      ( k2_relset_1(X0_47,X1_47,X2_47) = k2_relat_1(X2_47)
% 2.26/0.99      | m1_subset_1(X2_47,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top ),
% 2.26/0.99      inference(predicate_to_equality,[status(thm)],[c_502]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_1111,plain,
% 2.26/0.99      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 2.26/0.99      inference(superposition,[status(thm)],[c_800,c_797]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_9,plain,
% 2.26/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.26/0.99      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 2.26/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_504,plain,
% 2.26/0.99      ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
% 2.26/0.99      | m1_subset_1(k2_relset_1(X1_47,X2_47,X0_47),k1_zfmisc_1(X2_47)) ),
% 2.26/0.99      inference(subtyping,[status(esa)],[c_9]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_795,plain,
% 2.26/0.99      ( m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47))) != iProver_top
% 2.26/0.99      | m1_subset_1(k2_relset_1(X1_47,X2_47,X0_47),k1_zfmisc_1(X2_47)) = iProver_top ),
% 2.26/0.99      inference(predicate_to_equality,[status(thm)],[c_504]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_1413,plain,
% 2.26/0.99      ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) = iProver_top
% 2.26/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 2.26/0.99      inference(superposition,[status(thm)],[c_1111,c_795]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_1629,plain,
% 2.26/0.99      ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) = iProver_top ),
% 2.26/0.99      inference(global_propositional_subsumption,
% 2.26/0.99                [status(thm)],
% 2.26/0.99                [c_1413,c_16]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_2,plain,
% 2.26/0.99      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 2.26/0.99      | ~ v1_relat_1(X0)
% 2.26/0.99      | k8_relat_1(X1,X0) = X0 ),
% 2.26/0.99      inference(cnf_transformation,[],[f41]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_190,plain,
% 2.26/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.26/0.99      | ~ v1_relat_1(X2)
% 2.26/0.99      | X3 != X1
% 2.26/0.99      | k8_relat_1(X3,X2) = X2
% 2.26/0.99      | k2_relat_1(X2) != X0 ),
% 2.26/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_2]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_191,plain,
% 2.26/0.99      ( ~ m1_subset_1(k2_relat_1(X0),k1_zfmisc_1(X1))
% 2.26/0.99      | ~ v1_relat_1(X0)
% 2.26/0.99      | k8_relat_1(X1,X0) = X0 ),
% 2.26/0.99      inference(unflattening,[status(thm)],[c_190]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_497,plain,
% 2.26/0.99      ( ~ m1_subset_1(k2_relat_1(X0_47),k1_zfmisc_1(X1_47))
% 2.26/0.99      | ~ v1_relat_1(X0_47)
% 2.26/0.99      | k8_relat_1(X1_47,X0_47) = X0_47 ),
% 2.26/0.99      inference(subtyping,[status(esa)],[c_191]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_801,plain,
% 2.26/0.99      ( k8_relat_1(X0_47,X1_47) = X1_47
% 2.26/0.99      | m1_subset_1(k2_relat_1(X1_47),k1_zfmisc_1(X0_47)) != iProver_top
% 2.26/0.99      | v1_relat_1(X1_47) != iProver_top ),
% 2.26/0.99      inference(predicate_to_equality,[status(thm)],[c_497]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_2046,plain,
% 2.26/0.99      ( k8_relat_1(sK1,sK2) = sK2 | v1_relat_1(sK2) != iProver_top ),
% 2.26/0.99      inference(superposition,[status(thm)],[c_1629,c_801]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_1433,plain,
% 2.26/0.99      ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))
% 2.26/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.26/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_1413]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_938,plain,
% 2.26/0.99      ( ~ m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(X0_47))
% 2.26/0.99      | ~ v1_relat_1(sK2)
% 2.26/0.99      | k8_relat_1(X0_47,sK2) = sK2 ),
% 2.26/0.99      inference(instantiation,[status(thm)],[c_497]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_1765,plain,
% 2.26/0.99      ( ~ m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))
% 2.26/0.99      | ~ v1_relat_1(sK2)
% 2.26/0.99      | k8_relat_1(sK1,sK2) = sK2 ),
% 2.26/0.99      inference(instantiation,[status(thm)],[c_938]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_2316,plain,
% 2.26/0.99      ( k8_relat_1(sK1,sK2) = sK2 ),
% 2.26/0.99      inference(global_propositional_subsumption,
% 2.26/0.99                [status(thm)],
% 2.26/0.99                [c_2046,c_15,c_894,c_1433,c_1765]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_4,plain,
% 2.26/0.99      ( ~ v1_relat_1(X0)
% 2.26/0.99      | k10_relat_1(X0,k4_xboole_0(k2_relat_1(X0),k4_xboole_0(k2_relat_1(X0),X1))) = k10_relat_1(X0,X1) ),
% 2.26/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_508,plain,
% 2.26/0.99      ( ~ v1_relat_1(X0_47)
% 2.26/0.99      | k10_relat_1(X0_47,k4_xboole_0(k2_relat_1(X0_47),k4_xboole_0(k2_relat_1(X0_47),X1_47))) = k10_relat_1(X0_47,X1_47) ),
% 2.26/0.99      inference(subtyping,[status(esa)],[c_4]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_791,plain,
% 2.26/0.99      ( k10_relat_1(X0_47,k4_xboole_0(k2_relat_1(X0_47),k4_xboole_0(k2_relat_1(X0_47),X1_47))) = k10_relat_1(X0_47,X1_47)
% 2.26/0.99      | v1_relat_1(X0_47) != iProver_top ),
% 2.26/0.99      inference(predicate_to_equality,[status(thm)],[c_508]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_1171,plain,
% 2.26/0.99      ( k10_relat_1(sK2,k4_xboole_0(k2_relat_1(sK2),k4_xboole_0(k2_relat_1(sK2),X0_47))) = k10_relat_1(sK2,X0_47) ),
% 2.26/0.99      inference(superposition,[status(thm)],[c_967,c_791]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_1,plain,
% 2.26/0.99      ( ~ v1_relat_1(X0)
% 2.26/0.99      | k4_xboole_0(k2_relat_1(X0),k4_xboole_0(k2_relat_1(X0),X1)) = k2_relat_1(k8_relat_1(X1,X0)) ),
% 2.26/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_510,plain,
% 2.26/0.99      ( ~ v1_relat_1(X0_47)
% 2.26/0.99      | k4_xboole_0(k2_relat_1(X0_47),k4_xboole_0(k2_relat_1(X0_47),X1_47)) = k2_relat_1(k8_relat_1(X1_47,X0_47)) ),
% 2.26/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_789,plain,
% 2.26/0.99      ( k4_xboole_0(k2_relat_1(X0_47),k4_xboole_0(k2_relat_1(X0_47),X1_47)) = k2_relat_1(k8_relat_1(X1_47,X0_47))
% 2.26/0.99      | v1_relat_1(X0_47) != iProver_top ),
% 2.26/0.99      inference(predicate_to_equality,[status(thm)],[c_510]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_1125,plain,
% 2.26/0.99      ( k4_xboole_0(k2_relat_1(sK2),k4_xboole_0(k2_relat_1(sK2),X0_47)) = k2_relat_1(k8_relat_1(X0_47,sK2)) ),
% 2.26/0.99      inference(superposition,[status(thm)],[c_967,c_789]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_1352,plain,
% 2.26/0.99      ( k10_relat_1(sK2,k2_relat_1(k8_relat_1(X0_47,sK2))) = k10_relat_1(sK2,X0_47) ),
% 2.26/0.99      inference(light_normalisation,[status(thm)],[c_1171,c_1125]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_2323,plain,
% 2.26/0.99      ( k10_relat_1(sK2,k2_relat_1(sK2)) = k10_relat_1(sK2,sK1) ),
% 2.26/0.99      inference(superposition,[status(thm)],[c_2316,c_1352]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_5,plain,
% 2.26/0.99      ( ~ v1_relat_1(X0)
% 2.26/0.99      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 2.26/0.99      inference(cnf_transformation,[],[f44]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_507,plain,
% 2.26/0.99      ( ~ v1_relat_1(X0_47)
% 2.26/0.99      | k10_relat_1(X0_47,k2_relat_1(X0_47)) = k1_relat_1(X0_47) ),
% 2.26/0.99      inference(subtyping,[status(esa)],[c_5]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_792,plain,
% 2.26/0.99      ( k10_relat_1(X0_47,k2_relat_1(X0_47)) = k1_relat_1(X0_47)
% 2.26/0.99      | v1_relat_1(X0_47) != iProver_top ),
% 2.26/0.99      inference(predicate_to_equality,[status(thm)],[c_507]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_972,plain,
% 2.26/0.99      ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
% 2.26/0.99      inference(superposition,[status(thm)],[c_967,c_792]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_2325,plain,
% 2.26/0.99      ( k10_relat_1(sK2,sK1) = k1_relat_1(sK2) ),
% 2.26/0.99      inference(light_normalisation,[status(thm)],[c_2323,c_972]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_12,plain,
% 2.26/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.26/0.99      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 2.26/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_501,plain,
% 2.26/0.99      ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
% 2.26/0.99      | k7_relset_1(X1_47,X2_47,X0_47,X3_47) = k9_relat_1(X0_47,X3_47) ),
% 2.26/0.99      inference(subtyping,[status(esa)],[c_12]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_798,plain,
% 2.26/0.99      ( k7_relset_1(X0_47,X1_47,X2_47,X3_47) = k9_relat_1(X2_47,X3_47)
% 2.26/0.99      | m1_subset_1(X2_47,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top ),
% 2.26/0.99      inference(predicate_to_equality,[status(thm)],[c_501]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_1481,plain,
% 2.26/0.99      ( k7_relset_1(sK0,sK1,sK2,X0_47) = k9_relat_1(sK2,X0_47) ),
% 2.26/0.99      inference(superposition,[status(thm)],[c_800,c_798]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_14,negated_conjecture,
% 2.26/0.99      ( k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)
% 2.26/0.99      | k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) ),
% 2.26/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_499,negated_conjecture,
% 2.26/0.99      ( k2_relset_1(sK0,sK1,sK2) != k7_relset_1(sK0,sK1,sK2,sK0)
% 2.26/0.99      | k1_relset_1(sK0,sK1,sK2) != k8_relset_1(sK0,sK1,sK2,sK1) ),
% 2.26/0.99      inference(subtyping,[status(esa)],[c_14]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_1174,plain,
% 2.26/0.99      ( k8_relset_1(sK0,sK1,sK2,sK1) != k1_relat_1(sK2)
% 2.26/0.99      | k7_relset_1(sK0,sK1,sK2,sK0) != k2_relset_1(sK0,sK1,sK2) ),
% 2.26/0.99      inference(demodulation,[status(thm)],[c_1030,c_499]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_1221,plain,
% 2.26/0.99      ( k8_relset_1(sK0,sK1,sK2,sK1) != k1_relat_1(sK2)
% 2.26/0.99      | k7_relset_1(sK0,sK1,sK2,sK0) != k2_relat_1(sK2) ),
% 2.26/0.99      inference(demodulation,[status(thm)],[c_1111,c_1174]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_1568,plain,
% 2.26/0.99      ( k8_relset_1(sK0,sK1,sK2,sK1) != k1_relat_1(sK2)
% 2.26/0.99      | k9_relat_1(sK2,sK0) != k2_relat_1(sK2) ),
% 2.26/0.99      inference(demodulation,[status(thm)],[c_1481,c_1221]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_13,plain,
% 2.26/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.26/0.99      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 2.26/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_500,plain,
% 2.26/0.99      ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X1_47,X2_47)))
% 2.26/0.99      | k8_relset_1(X1_47,X2_47,X0_47,X3_47) = k10_relat_1(X0_47,X3_47) ),
% 2.26/0.99      inference(subtyping,[status(esa)],[c_13]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_799,plain,
% 2.26/0.99      ( k8_relset_1(X0_47,X1_47,X2_47,X3_47) = k10_relat_1(X2_47,X3_47)
% 2.26/0.99      | m1_subset_1(X2_47,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top ),
% 2.26/0.99      inference(predicate_to_equality,[status(thm)],[c_500]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_1504,plain,
% 2.26/0.99      ( k8_relset_1(sK0,sK1,sK2,X0_47) = k10_relat_1(sK2,X0_47) ),
% 2.26/0.99      inference(superposition,[status(thm)],[c_800,c_799]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(c_1634,plain,
% 2.26/0.99      ( k10_relat_1(sK2,sK1) != k1_relat_1(sK2)
% 2.26/0.99      | k9_relat_1(sK2,sK0) != k2_relat_1(sK2) ),
% 2.26/0.99      inference(demodulation,[status(thm)],[c_1568,c_1504]) ).
% 2.26/0.99  
% 2.26/0.99  cnf(contradiction,plain,
% 2.26/0.99      ( $false ),
% 2.26/0.99      inference(minisat,[status(thm)],[c_3124,c_2325,c_1634]) ).
% 2.26/0.99  
% 2.26/0.99  
% 2.26/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.26/0.99  
% 2.26/0.99  ------                               Statistics
% 2.26/0.99  
% 2.26/0.99  ------ General
% 2.26/0.99  
% 2.26/0.99  abstr_ref_over_cycles:                  0
% 2.26/0.99  abstr_ref_under_cycles:                 0
% 2.26/0.99  gc_basic_clause_elim:                   0
% 2.26/0.99  forced_gc_time:                         0
% 2.26/0.99  parsing_time:                           0.008
% 2.26/0.99  unif_index_cands_time:                  0.
% 2.26/0.99  unif_index_add_time:                    0.
% 2.26/0.99  orderings_time:                         0.
% 2.26/0.99  out_proof_time:                         0.012
% 2.26/0.99  total_time:                             0.135
% 2.26/0.99  num_of_symbols:                         52
% 2.26/0.99  num_of_terms:                           3265
% 2.26/0.99  
% 2.26/0.99  ------ Preprocessing
% 2.26/0.99  
% 2.26/0.99  num_of_splits:                          0
% 2.26/0.99  num_of_split_atoms:                     0
% 2.26/0.99  num_of_reused_defs:                     0
% 2.26/0.99  num_eq_ax_congr_red:                    28
% 2.26/0.99  num_of_sem_filtered_clauses:            1
% 2.26/0.99  num_of_subtypes:                        2
% 2.26/0.99  monotx_restored_types:                  1
% 2.26/0.99  sat_num_of_epr_types:                   0
% 2.26/0.99  sat_num_of_non_cyclic_types:            0
% 2.26/0.99  sat_guarded_non_collapsed_types:        0
% 2.26/0.99  num_pure_diseq_elim:                    0
% 2.26/0.99  simp_replaced_by:                       0
% 2.26/0.99  res_preprocessed:                       88
% 2.26/0.99  prep_upred:                             0
% 2.26/0.99  prep_unflattend:                        4
% 2.26/0.99  smt_new_axioms:                         0
% 2.26/0.99  pred_elim_cands:                        2
% 2.26/0.99  pred_elim:                              1
% 2.26/0.99  pred_elim_cl:                           1
% 2.26/0.99  pred_elim_cycles:                       3
% 2.26/0.99  merged_defs:                            0
% 2.26/0.99  merged_defs_ncl:                        0
% 2.26/0.99  bin_hyper_res:                          0
% 2.26/0.99  prep_cycles:                            4
% 2.26/0.99  pred_elim_time:                         0.003
% 2.26/0.99  splitting_time:                         0.
% 2.26/0.99  sem_filter_time:                        0.
% 2.26/0.99  monotx_time:                            0.001
% 2.26/0.99  subtype_inf_time:                       0.001
% 2.26/0.99  
% 2.26/0.99  ------ Problem properties
% 2.26/0.99  
% 2.26/0.99  clauses:                                15
% 2.26/0.99  conjectures:                            2
% 2.26/0.99  epr:                                    0
% 2.26/0.99  horn:                                   15
% 2.26/0.99  ground:                                 2
% 2.26/0.99  unary:                                  1
% 2.26/0.99  binary:                                 12
% 2.26/0.99  lits:                                   31
% 2.26/0.99  lits_eq:                                12
% 2.26/0.99  fd_pure:                                0
% 2.26/0.99  fd_pseudo:                              0
% 2.26/0.99  fd_cond:                                0
% 2.26/0.99  fd_pseudo_cond:                         0
% 2.26/0.99  ac_symbols:                             0
% 2.26/0.99  
% 2.26/0.99  ------ Propositional Solver
% 2.26/0.99  
% 2.26/0.99  prop_solver_calls:                      32
% 2.26/0.99  prop_fast_solver_calls:                 539
% 2.26/0.99  smt_solver_calls:                       0
% 2.26/0.99  smt_fast_solver_calls:                  0
% 2.26/0.99  prop_num_of_clauses:                    1113
% 2.26/0.99  prop_preprocess_simplified:             3746
% 2.26/0.99  prop_fo_subsumed:                       4
% 2.26/0.99  prop_solver_time:                       0.
% 2.26/0.99  smt_solver_time:                        0.
% 2.26/0.99  smt_fast_solver_time:                   0.
% 2.26/0.99  prop_fast_solver_time:                  0.
% 2.26/0.99  prop_unsat_core_time:                   0.
% 2.26/0.99  
% 2.26/0.99  ------ QBF
% 2.26/0.99  
% 2.26/0.99  qbf_q_res:                              0
% 2.26/0.99  qbf_num_tautologies:                    0
% 2.26/0.99  qbf_prep_cycles:                        0
% 2.26/0.99  
% 2.26/0.99  ------ BMC1
% 2.26/0.99  
% 2.26/0.99  bmc1_current_bound:                     -1
% 2.26/0.99  bmc1_last_solved_bound:                 -1
% 2.26/0.99  bmc1_unsat_core_size:                   -1
% 2.26/0.99  bmc1_unsat_core_parents_size:           -1
% 2.26/0.99  bmc1_merge_next_fun:                    0
% 2.26/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.26/0.99  
% 2.26/0.99  ------ Instantiation
% 2.26/0.99  
% 2.26/0.99  inst_num_of_clauses:                    413
% 2.26/0.99  inst_num_in_passive:                    116
% 2.26/0.99  inst_num_in_active:                     258
% 2.26/0.99  inst_num_in_unprocessed:                39
% 2.26/0.99  inst_num_of_loops:                      270
% 2.26/0.99  inst_num_of_learning_restarts:          0
% 2.26/0.99  inst_num_moves_active_passive:          3
% 2.26/0.99  inst_lit_activity:                      0
% 2.26/0.99  inst_lit_activity_moves:                0
% 2.26/0.99  inst_num_tautologies:                   0
% 2.26/0.99  inst_num_prop_implied:                  0
% 2.26/0.99  inst_num_existing_simplified:           0
% 2.26/0.99  inst_num_eq_res_simplified:             0
% 2.26/0.99  inst_num_child_elim:                    0
% 2.26/0.99  inst_num_of_dismatching_blockings:      77
% 2.26/0.99  inst_num_of_non_proper_insts:           390
% 2.26/0.99  inst_num_of_duplicates:                 0
% 2.26/0.99  inst_inst_num_from_inst_to_res:         0
% 2.26/0.99  inst_dismatching_checking_time:         0.
% 2.26/0.99  
% 2.26/0.99  ------ Resolution
% 2.26/0.99  
% 2.26/0.99  res_num_of_clauses:                     0
% 2.26/0.99  res_num_in_passive:                     0
% 2.26/0.99  res_num_in_active:                      0
% 2.26/0.99  res_num_of_loops:                       92
% 2.26/0.99  res_forward_subset_subsumed:            81
% 2.26/0.99  res_backward_subset_subsumed:           4
% 2.26/0.99  res_forward_subsumed:                   0
% 2.26/0.99  res_backward_subsumed:                  0
% 2.26/0.99  res_forward_subsumption_resolution:     0
% 2.26/0.99  res_backward_subsumption_resolution:    0
% 2.26/0.99  res_clause_to_clause_subsumption:       143
% 2.26/0.99  res_orphan_elimination:                 0
% 2.26/0.99  res_tautology_del:                      89
% 2.26/0.99  res_num_eq_res_simplified:              0
% 2.26/0.99  res_num_sel_changes:                    0
% 2.26/0.99  res_moves_from_active_to_pass:          0
% 2.26/0.99  
% 2.26/0.99  ------ Superposition
% 2.26/0.99  
% 2.26/0.99  sup_time_total:                         0.
% 2.26/0.99  sup_time_generating:                    0.
% 2.26/0.99  sup_time_sim_full:                      0.
% 2.26/0.99  sup_time_sim_immed:                     0.
% 2.26/0.99  
% 2.26/0.99  sup_num_of_clauses:                     81
% 2.26/0.99  sup_num_in_active:                      49
% 2.26/0.99  sup_num_in_passive:                     32
% 2.26/0.99  sup_num_of_loops:                       52
% 2.26/0.99  sup_fw_superposition:                   71
% 2.26/0.99  sup_bw_superposition:                   71
% 2.26/0.99  sup_immediate_simplified:               31
% 2.26/0.99  sup_given_eliminated:                   0
% 2.26/0.99  comparisons_done:                       0
% 2.26/0.99  comparisons_avoided:                    0
% 2.26/0.99  
% 2.26/0.99  ------ Simplifications
% 2.26/0.99  
% 2.26/0.99  
% 2.26/0.99  sim_fw_subset_subsumed:                 0
% 2.26/0.99  sim_bw_subset_subsumed:                 0
% 2.26/0.99  sim_fw_subsumed:                        7
% 2.26/0.99  sim_bw_subsumed:                        0
% 2.26/0.99  sim_fw_subsumption_res:                 0
% 2.26/0.99  sim_bw_subsumption_res:                 0
% 2.26/0.99  sim_tautology_del:                      0
% 2.26/0.99  sim_eq_tautology_del:                   20
% 2.26/0.99  sim_eq_res_simp:                        1
% 2.26/0.99  sim_fw_demodulated:                     5
% 2.26/0.99  sim_bw_demodulated:                     4
% 2.26/0.99  sim_light_normalised:                   29
% 2.26/0.99  sim_joinable_taut:                      0
% 2.26/0.99  sim_joinable_simp:                      0
% 2.26/0.99  sim_ac_normalised:                      0
% 2.26/0.99  sim_smt_subsumption:                    0
% 2.26/0.99  
%------------------------------------------------------------------------------
