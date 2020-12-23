%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:55:00 EST 2020

% Result     : Theorem 11.69s
% Output     : CNFRefutation 11.69s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 517 expanded)
%              Number of clauses        :   78 ( 176 expanded)
%              Number of leaves         :   18 ( 114 expanded)
%              Depth                    :   21
%              Number of atoms          :  270 ( 941 expanded)
%              Number of equality atoms :  115 ( 306 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f33,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1))
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f35,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ~ r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ~ r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f33,f35])).

fof(f54,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f36])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f56,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f43,f42])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f37,f56])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k3_tarski(k1_enumset1(X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f39,f56])).

fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f11,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f47,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f62,plain,(
    ! [X0] :
      ( k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f47,f56])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f41,f56])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f60,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f40,f56])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k3_tarski(k1_enumset1(X0,X0,X1)),X2) ) ),
    inference(definition_unfolding,[],[f38,f56])).

fof(f55,plain,(
    ~ r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f36])).

fof(f63,plain,(
    ~ r1_tarski(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f55,f56])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_815,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_817,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1533,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_815,c_817])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_818,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2132,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1533,c_818])).

cnf(c_17,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3712,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2132,c_17])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_822,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3716,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3712,c_822])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_828,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_tarski(k1_enumset1(X0,X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_826,plain,
    ( k3_tarski(k1_enumset1(X0,X0,X1)) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1650,plain,
    ( k3_tarski(k1_enumset1(X0,X0,k3_tarski(k1_enumset1(X1,X1,X2)))) = k3_tarski(k1_enumset1(X1,X1,X2))
    | r1_tarski(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_828,c_826])).

cnf(c_3975,plain,
    ( k3_tarski(k1_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),k3_tarski(k1_enumset1(X0,X0,sK1)))) = k3_tarski(k1_enumset1(X0,X0,sK1)) ),
    inference(superposition,[status(thm)],[c_3716,c_1650])).

cnf(c_1172,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_815,c_822])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_5,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_140,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_5])).

cnf(c_141,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_140])).

cnf(c_168,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_7,c_141])).

cnf(c_814,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_168])).

cnf(c_2130,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1172,c_814])).

cnf(c_966,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[status(thm)],[c_6,c_16])).

cnf(c_1035,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(resolution,[status(thm)],[c_168,c_966])).

cnf(c_9,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1040,plain,
    ( v1_relat_1(sK2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1035,c_9])).

cnf(c_1041,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1040])).

cnf(c_12601,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2130,c_1041])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_821,plain,
    ( k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_12606,plain,
    ( k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k2_relat_1(sK2))) = k3_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_12601,c_821])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_824,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_12946,plain,
    ( r1_tarski(k3_relat_1(sK2),X0) = iProver_top
    | r1_tarski(k2_relat_1(sK2),X0) != iProver_top
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_12606,c_824])).

cnf(c_14326,plain,
    ( r1_tarski(k3_relat_1(sK2),k3_tarski(k1_enumset1(X0,X0,X1))) = iProver_top
    | r1_tarski(k2_relat_1(sK2),k3_tarski(k1_enumset1(X0,X0,X1))) != iProver_top
    | r1_tarski(k1_relat_1(sK2),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_828,c_12946])).

cnf(c_27922,plain,
    ( r1_tarski(k3_relat_1(sK2),k3_tarski(k1_enumset1(X0,X0,X1))) = iProver_top
    | r1_tarski(k2_relat_1(sK2),X1) != iProver_top
    | r1_tarski(k1_relat_1(sK2),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_828,c_14326])).

cnf(c_34836,plain,
    ( r1_tarski(k3_relat_1(sK2),k3_tarski(k1_enumset1(X0,X0,sK1))) = iProver_top
    | r1_tarski(k2_relat_1(sK2),k3_tarski(k1_enumset1(X0,X0,sK1))) != iProver_top
    | r1_tarski(k1_relat_1(sK2),k3_tarski(k1_enumset1(X0,X0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3975,c_27922])).

cnf(c_34918,plain,
    ( r1_tarski(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1))) = iProver_top
    | r1_tarski(k2_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1))) != iProver_top
    | r1_tarski(k1_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_34836])).

cnf(c_3,plain,
    ( r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_825,plain,
    ( r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_12,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_10,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_232,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_12,c_10])).

cnf(c_813,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_232])).

cnf(c_956,plain,
    ( k7_relat_1(sK2,sK0) = sK2
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_815,c_813])).

cnf(c_957,plain,
    ( ~ v1_relat_1(sK2)
    | k7_relat_1(sK2,sK0) = sK2 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_956])).

cnf(c_2405,plain,
    ( k7_relat_1(sK2,sK0) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_956,c_957,c_1040])).

cnf(c_11,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_819,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2407,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2405,c_819])).

cnf(c_2853,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2407,c_1041])).

cnf(c_2857,plain,
    ( k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),sK0)) = sK0 ),
    inference(superposition,[status(thm)],[c_2853,c_826])).

cnf(c_1,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_827,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2862,plain,
    ( r1_tarski(k1_relat_1(sK2),X0) = iProver_top
    | r1_tarski(sK0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2857,c_827])).

cnf(c_3008,plain,
    ( k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),X0)) = X0
    | r1_tarski(sK0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2862,c_826])).

cnf(c_3478,plain,
    ( k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,X0)))) = k3_tarski(k1_enumset1(sK0,sK0,X0)) ),
    inference(superposition,[status(thm)],[c_825,c_3008])).

cnf(c_5231,plain,
    ( r1_tarski(k1_relat_1(sK2),X0) = iProver_top
    | r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,X1)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3478,c_827])).

cnf(c_5948,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_relat_1(sK2),X1) = iProver_top
    | r1_tarski(sK0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_824,c_5231])).

cnf(c_8986,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_relat_1(sK2),k3_tarski(k1_enumset1(X2,X2,X1))) = iProver_top
    | r1_tarski(sK0,k3_tarski(k1_enumset1(X2,X2,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_828,c_5948])).

cnf(c_22187,plain,
    ( r1_tarski(k1_relat_1(sK2),k3_tarski(k1_enumset1(X0,X0,sK1))) = iProver_top
    | r1_tarski(sK0,k3_tarski(k1_enumset1(X0,X0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3716,c_8986])).

cnf(c_22206,plain,
    ( r1_tarski(k1_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1))) = iProver_top
    | r1_tarski(sK0,k3_tarski(k1_enumset1(sK0,sK0,sK1))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_22187])).

cnf(c_3962,plain,
    ( k3_tarski(k1_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_3716,c_826])).

cnf(c_3968,plain,
    ( k3_tarski(k1_enumset1(X0,X0,k3_tarski(k1_enumset1(X1,X1,k3_tarski(k1_enumset1(X0,X0,X2)))))) = k3_tarski(k1_enumset1(X1,X1,k3_tarski(k1_enumset1(X0,X0,X2)))) ),
    inference(superposition,[status(thm)],[c_825,c_1650])).

cnf(c_17116,plain,
    ( r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,k3_tarski(k1_enumset1(X0,X0,X2))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3968,c_825])).

cnf(c_17219,plain,
    ( r1_tarski(k2_relat_1(sK2),k3_tarski(k1_enumset1(X0,X0,sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3962,c_17116])).

cnf(c_17273,plain,
    ( r1_tarski(k2_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_17219])).

cnf(c_3525,plain,
    ( r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,sK1))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3526,plain,
    ( r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3525])).

cnf(c_3528,plain,
    ( r1_tarski(sK0,k3_tarski(k1_enumset1(sK0,sK0,sK1))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3526])).

cnf(c_15,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_18,plain,
    ( r1_tarski(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_34918,c_22206,c_17273,c_3528,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 12:35:29 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.69/1.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.69/1.98  
% 11.69/1.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.69/1.98  
% 11.69/1.98  ------  iProver source info
% 11.69/1.98  
% 11.69/1.98  git: date: 2020-06-30 10:37:57 +0100
% 11.69/1.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.69/1.98  git: non_committed_changes: false
% 11.69/1.98  git: last_make_outside_of_git: false
% 11.69/1.98  
% 11.69/1.98  ------ 
% 11.69/1.98  ------ Parsing...
% 11.69/1.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.69/1.98  
% 11.69/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 11.69/1.98  
% 11.69/1.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.69/1.98  
% 11.69/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.69/1.98  ------ Proving...
% 11.69/1.98  ------ Problem Properties 
% 11.69/1.98  
% 11.69/1.98  
% 11.69/1.98  clauses                                 16
% 11.69/1.98  conjectures                             2
% 11.69/1.98  EPR                                     1
% 11.69/1.98  Horn                                    16
% 11.69/1.98  unary                                   4
% 11.69/1.98  binary                                  9
% 11.69/1.98  lits                                    31
% 11.69/1.98  lits eq                                 4
% 11.69/1.98  fd_pure                                 0
% 11.69/1.98  fd_pseudo                               0
% 11.69/1.98  fd_cond                                 0
% 11.69/1.98  fd_pseudo_cond                          0
% 11.69/1.98  AC symbols                              0
% 11.69/1.98  
% 11.69/1.98  ------ Input Options Time Limit: Unbounded
% 11.69/1.98  
% 11.69/1.98  
% 11.69/1.98  ------ 
% 11.69/1.98  Current options:
% 11.69/1.98  ------ 
% 11.69/1.98  
% 11.69/1.98  
% 11.69/1.98  
% 11.69/1.98  
% 11.69/1.98  ------ Proving...
% 11.69/1.98  
% 11.69/1.98  
% 11.69/1.98  % SZS status Theorem for theBenchmark.p
% 11.69/1.98  
% 11.69/1.98  % SZS output start CNFRefutation for theBenchmark.p
% 11.69/1.98  
% 11.69/1.98  fof(f17,conjecture,(
% 11.69/1.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)))),
% 11.69/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.69/1.98  
% 11.69/1.98  fof(f18,negated_conjecture,(
% 11.69/1.98    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)))),
% 11.69/1.98    inference(negated_conjecture,[],[f17])).
% 11.69/1.98  
% 11.69/1.98  fof(f33,plain,(
% 11.69/1.98    ? [X0,X1,X2] : (~r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.69/1.98    inference(ennf_transformation,[],[f18])).
% 11.69/1.98  
% 11.69/1.98  fof(f35,plain,(
% 11.69/1.98    ? [X0,X1,X2] : (~r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (~r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 11.69/1.98    introduced(choice_axiom,[])).
% 11.69/1.98  
% 11.69/1.98  fof(f36,plain,(
% 11.69/1.98    ~r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 11.69/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f33,f35])).
% 11.69/1.98  
% 11.69/1.98  fof(f54,plain,(
% 11.69/1.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 11.69/1.98    inference(cnf_transformation,[],[f36])).
% 11.69/1.98  
% 11.69/1.98  fof(f16,axiom,(
% 11.69/1.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 11.69/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.69/1.98  
% 11.69/1.98  fof(f32,plain,(
% 11.69/1.98    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.69/1.98    inference(ennf_transformation,[],[f16])).
% 11.69/1.98  
% 11.69/1.98  fof(f53,plain,(
% 11.69/1.98    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.69/1.98    inference(cnf_transformation,[],[f32])).
% 11.69/1.98  
% 11.69/1.98  fof(f15,axiom,(
% 11.69/1.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 11.69/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.69/1.98  
% 11.69/1.98  fof(f31,plain,(
% 11.69/1.98    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.69/1.98    inference(ennf_transformation,[],[f15])).
% 11.69/1.98  
% 11.69/1.98  fof(f52,plain,(
% 11.69/1.98    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.69/1.98    inference(cnf_transformation,[],[f31])).
% 11.69/1.98  
% 11.69/1.98  fof(f8,axiom,(
% 11.69/1.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 11.69/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.69/1.98  
% 11.69/1.98  fof(f34,plain,(
% 11.69/1.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 11.69/1.98    inference(nnf_transformation,[],[f8])).
% 11.69/1.98  
% 11.69/1.98  fof(f44,plain,(
% 11.69/1.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 11.69/1.98    inference(cnf_transformation,[],[f34])).
% 11.69/1.98  
% 11.69/1.98  fof(f1,axiom,(
% 11.69/1.98    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 11.69/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.69/1.98  
% 11.69/1.98  fof(f20,plain,(
% 11.69/1.98    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 11.69/1.98    inference(ennf_transformation,[],[f1])).
% 11.69/1.98  
% 11.69/1.98  fof(f37,plain,(
% 11.69/1.98    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 11.69/1.98    inference(cnf_transformation,[],[f20])).
% 11.69/1.98  
% 11.69/1.98  fof(f7,axiom,(
% 11.69/1.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 11.69/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.69/1.98  
% 11.69/1.98  fof(f43,plain,(
% 11.69/1.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 11.69/1.98    inference(cnf_transformation,[],[f7])).
% 11.69/1.98  
% 11.69/1.98  fof(f6,axiom,(
% 11.69/1.98    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 11.69/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.69/1.98  
% 11.69/1.98  fof(f42,plain,(
% 11.69/1.98    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 11.69/1.98    inference(cnf_transformation,[],[f6])).
% 11.69/1.98  
% 11.69/1.98  fof(f56,plain,(
% 11.69/1.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 11.69/1.98    inference(definition_unfolding,[],[f43,f42])).
% 11.69/1.98  
% 11.69/1.98  fof(f57,plain,(
% 11.69/1.98    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1))) | ~r1_tarski(X0,X1)) )),
% 11.69/1.98    inference(definition_unfolding,[],[f37,f56])).
% 11.69/1.98  
% 11.69/1.98  fof(f3,axiom,(
% 11.69/1.98    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 11.69/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.69/1.98  
% 11.69/1.98  fof(f22,plain,(
% 11.69/1.98    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 11.69/1.98    inference(ennf_transformation,[],[f3])).
% 11.69/1.98  
% 11.69/1.98  fof(f39,plain,(
% 11.69/1.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 11.69/1.98    inference(cnf_transformation,[],[f22])).
% 11.69/1.98  
% 11.69/1.98  fof(f59,plain,(
% 11.69/1.98    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 11.69/1.98    inference(definition_unfolding,[],[f39,f56])).
% 11.69/1.98  
% 11.69/1.98  fof(f9,axiom,(
% 11.69/1.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 11.69/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.69/1.98  
% 11.69/1.98  fof(f25,plain,(
% 11.69/1.98    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 11.69/1.98    inference(ennf_transformation,[],[f9])).
% 11.69/1.98  
% 11.69/1.98  fof(f46,plain,(
% 11.69/1.98    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 11.69/1.98    inference(cnf_transformation,[],[f25])).
% 11.69/1.98  
% 11.69/1.98  fof(f45,plain,(
% 11.69/1.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 11.69/1.98    inference(cnf_transformation,[],[f34])).
% 11.69/1.98  
% 11.69/1.98  fof(f11,axiom,(
% 11.69/1.98    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 11.69/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.69/1.98  
% 11.69/1.98  fof(f48,plain,(
% 11.69/1.98    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 11.69/1.98    inference(cnf_transformation,[],[f11])).
% 11.69/1.98  
% 11.69/1.98  fof(f10,axiom,(
% 11.69/1.98    ! [X0] : (v1_relat_1(X0) => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0))),
% 11.69/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.69/1.98  
% 11.69/1.98  fof(f26,plain,(
% 11.69/1.98    ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0))),
% 11.69/1.98    inference(ennf_transformation,[],[f10])).
% 11.69/1.98  
% 11.69/1.98  fof(f47,plain,(
% 11.69/1.98    ( ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 11.69/1.98    inference(cnf_transformation,[],[f26])).
% 11.69/1.98  
% 11.69/1.98  fof(f62,plain,(
% 11.69/1.98    ( ! [X0] : (k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 11.69/1.98    inference(definition_unfolding,[],[f47,f56])).
% 11.69/1.98  
% 11.69/1.98  fof(f5,axiom,(
% 11.69/1.98    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 11.69/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.69/1.98  
% 11.69/1.98  fof(f23,plain,(
% 11.69/1.98    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 11.69/1.98    inference(ennf_transformation,[],[f5])).
% 11.69/1.98  
% 11.69/1.98  fof(f24,plain,(
% 11.69/1.98    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 11.69/1.98    inference(flattening,[],[f23])).
% 11.69/1.98  
% 11.69/1.98  fof(f41,plain,(
% 11.69/1.98    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 11.69/1.98    inference(cnf_transformation,[],[f24])).
% 11.69/1.98  
% 11.69/1.98  fof(f61,plain,(
% 11.69/1.98    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 11.69/1.98    inference(definition_unfolding,[],[f41,f56])).
% 11.69/1.98  
% 11.69/1.98  fof(f4,axiom,(
% 11.69/1.98    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 11.69/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.69/1.98  
% 11.69/1.98  fof(f40,plain,(
% 11.69/1.98    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 11.69/1.98    inference(cnf_transformation,[],[f4])).
% 11.69/1.98  
% 11.69/1.98  fof(f60,plain,(
% 11.69/1.98    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1)))) )),
% 11.69/1.98    inference(definition_unfolding,[],[f40,f56])).
% 11.69/1.98  
% 11.69/1.98  fof(f14,axiom,(
% 11.69/1.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 11.69/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.69/1.98  
% 11.69/1.98  fof(f19,plain,(
% 11.69/1.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 11.69/1.98    inference(pure_predicate_removal,[],[f14])).
% 11.69/1.98  
% 11.69/1.98  fof(f30,plain,(
% 11.69/1.98    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.69/1.98    inference(ennf_transformation,[],[f19])).
% 11.69/1.98  
% 11.69/1.98  fof(f51,plain,(
% 11.69/1.98    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.69/1.98    inference(cnf_transformation,[],[f30])).
% 11.69/1.98  
% 11.69/1.98  fof(f12,axiom,(
% 11.69/1.98    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 11.69/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.69/1.98  
% 11.69/1.98  fof(f27,plain,(
% 11.69/1.98    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 11.69/1.98    inference(ennf_transformation,[],[f12])).
% 11.69/1.98  
% 11.69/1.98  fof(f28,plain,(
% 11.69/1.98    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 11.69/1.98    inference(flattening,[],[f27])).
% 11.69/1.98  
% 11.69/1.98  fof(f49,plain,(
% 11.69/1.98    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.69/1.98    inference(cnf_transformation,[],[f28])).
% 11.69/1.98  
% 11.69/1.98  fof(f13,axiom,(
% 11.69/1.98    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 11.69/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.69/1.98  
% 11.69/1.98  fof(f29,plain,(
% 11.69/1.98    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 11.69/1.98    inference(ennf_transformation,[],[f13])).
% 11.69/1.98  
% 11.69/1.98  fof(f50,plain,(
% 11.69/1.98    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 11.69/1.98    inference(cnf_transformation,[],[f29])).
% 11.69/1.98  
% 11.69/1.98  fof(f2,axiom,(
% 11.69/1.98    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 11.69/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.69/1.98  
% 11.69/1.98  fof(f21,plain,(
% 11.69/1.98    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 11.69/1.98    inference(ennf_transformation,[],[f2])).
% 11.69/1.98  
% 11.69/1.98  fof(f38,plain,(
% 11.69/1.98    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 11.69/1.98    inference(cnf_transformation,[],[f21])).
% 11.69/1.98  
% 11.69/1.98  fof(f58,plain,(
% 11.69/1.98    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k3_tarski(k1_enumset1(X0,X0,X1)),X2)) )),
% 11.69/1.98    inference(definition_unfolding,[],[f38,f56])).
% 11.69/1.98  
% 11.69/1.98  fof(f55,plain,(
% 11.69/1.98    ~r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))),
% 11.69/1.98    inference(cnf_transformation,[],[f36])).
% 11.69/1.98  
% 11.69/1.98  fof(f63,plain,(
% 11.69/1.98    ~r1_tarski(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1)))),
% 11.69/1.98    inference(definition_unfolding,[],[f55,f56])).
% 11.69/1.98  
% 11.69/1.98  cnf(c_16,negated_conjecture,
% 11.69/1.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 11.69/1.98      inference(cnf_transformation,[],[f54]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_815,plain,
% 11.69/1.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 11.69/1.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_14,plain,
% 11.69/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.69/1.98      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 11.69/1.98      inference(cnf_transformation,[],[f53]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_817,plain,
% 11.69/1.98      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 11.69/1.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.69/1.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_1533,plain,
% 11.69/1.98      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 11.69/1.98      inference(superposition,[status(thm)],[c_815,c_817]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_13,plain,
% 11.69/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.69/1.98      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 11.69/1.98      inference(cnf_transformation,[],[f52]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_818,plain,
% 11.69/1.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.69/1.98      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
% 11.69/1.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_2132,plain,
% 11.69/1.98      ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) = iProver_top
% 11.69/1.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 11.69/1.98      inference(superposition,[status(thm)],[c_1533,c_818]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_17,plain,
% 11.69/1.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 11.69/1.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_3712,plain,
% 11.69/1.98      ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) = iProver_top ),
% 11.69/1.98      inference(global_propositional_subsumption,
% 11.69/1.98                [status(thm)],
% 11.69/1.98                [c_2132,c_17]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_6,plain,
% 11.69/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 11.69/1.98      inference(cnf_transformation,[],[f44]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_822,plain,
% 11.69/1.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 11.69/1.98      | r1_tarski(X0,X1) = iProver_top ),
% 11.69/1.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_3716,plain,
% 11.69/1.98      ( r1_tarski(k2_relat_1(sK2),sK1) = iProver_top ),
% 11.69/1.98      inference(superposition,[status(thm)],[c_3712,c_822]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_0,plain,
% 11.69/1.98      ( ~ r1_tarski(X0,X1)
% 11.69/1.98      | r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1))) ),
% 11.69/1.98      inference(cnf_transformation,[],[f57]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_828,plain,
% 11.69/1.98      ( r1_tarski(X0,X1) != iProver_top
% 11.69/1.98      | r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1))) = iProver_top ),
% 11.69/1.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_2,plain,
% 11.69/1.98      ( ~ r1_tarski(X0,X1) | k3_tarski(k1_enumset1(X0,X0,X1)) = X1 ),
% 11.69/1.98      inference(cnf_transformation,[],[f59]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_826,plain,
% 11.69/1.98      ( k3_tarski(k1_enumset1(X0,X0,X1)) = X1
% 11.69/1.98      | r1_tarski(X0,X1) != iProver_top ),
% 11.69/1.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_1650,plain,
% 11.69/1.98      ( k3_tarski(k1_enumset1(X0,X0,k3_tarski(k1_enumset1(X1,X1,X2)))) = k3_tarski(k1_enumset1(X1,X1,X2))
% 11.69/1.98      | r1_tarski(X0,X2) != iProver_top ),
% 11.69/1.98      inference(superposition,[status(thm)],[c_828,c_826]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_3975,plain,
% 11.69/1.98      ( k3_tarski(k1_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),k3_tarski(k1_enumset1(X0,X0,sK1)))) = k3_tarski(k1_enumset1(X0,X0,sK1)) ),
% 11.69/1.98      inference(superposition,[status(thm)],[c_3716,c_1650]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_1172,plain,
% 11.69/1.98      ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 11.69/1.98      inference(superposition,[status(thm)],[c_815,c_822]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_7,plain,
% 11.69/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.69/1.98      | ~ v1_relat_1(X1)
% 11.69/1.98      | v1_relat_1(X0) ),
% 11.69/1.98      inference(cnf_transformation,[],[f46]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_5,plain,
% 11.69/1.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.69/1.98      inference(cnf_transformation,[],[f45]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_140,plain,
% 11.69/1.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 11.69/1.98      inference(prop_impl,[status(thm)],[c_5]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_141,plain,
% 11.69/1.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.69/1.98      inference(renaming,[status(thm)],[c_140]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_168,plain,
% 11.69/1.98      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 11.69/1.98      inference(bin_hyper_res,[status(thm)],[c_7,c_141]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_814,plain,
% 11.69/1.98      ( r1_tarski(X0,X1) != iProver_top
% 11.69/1.98      | v1_relat_1(X1) != iProver_top
% 11.69/1.98      | v1_relat_1(X0) = iProver_top ),
% 11.69/1.98      inference(predicate_to_equality,[status(thm)],[c_168]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_2130,plain,
% 11.69/1.98      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 11.69/1.98      | v1_relat_1(sK2) = iProver_top ),
% 11.69/1.98      inference(superposition,[status(thm)],[c_1172,c_814]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_966,plain,
% 11.69/1.98      ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
% 11.69/1.98      inference(resolution,[status(thm)],[c_6,c_16]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_1035,plain,
% 11.69/1.98      ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK2) ),
% 11.69/1.98      inference(resolution,[status(thm)],[c_168,c_966]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_9,plain,
% 11.69/1.98      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 11.69/1.98      inference(cnf_transformation,[],[f48]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_1040,plain,
% 11.69/1.98      ( v1_relat_1(sK2) ),
% 11.69/1.98      inference(forward_subsumption_resolution,
% 11.69/1.98                [status(thm)],
% 11.69/1.98                [c_1035,c_9]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_1041,plain,
% 11.69/1.98      ( v1_relat_1(sK2) = iProver_top ),
% 11.69/1.98      inference(predicate_to_equality,[status(thm)],[c_1040]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_12601,plain,
% 11.69/1.98      ( v1_relat_1(sK2) = iProver_top ),
% 11.69/1.98      inference(global_propositional_subsumption,
% 11.69/1.98                [status(thm)],
% 11.69/1.98                [c_2130,c_1041]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_8,plain,
% 11.69/1.98      ( ~ v1_relat_1(X0)
% 11.69/1.98      | k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) ),
% 11.69/1.98      inference(cnf_transformation,[],[f62]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_821,plain,
% 11.69/1.98      ( k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
% 11.69/1.98      | v1_relat_1(X0) != iProver_top ),
% 11.69/1.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_12606,plain,
% 11.69/1.98      ( k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k2_relat_1(sK2))) = k3_relat_1(sK2) ),
% 11.69/1.98      inference(superposition,[status(thm)],[c_12601,c_821]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_4,plain,
% 11.69/1.98      ( ~ r1_tarski(X0,X1)
% 11.69/1.98      | ~ r1_tarski(X2,X1)
% 11.69/1.98      | r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) ),
% 11.69/1.98      inference(cnf_transformation,[],[f61]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_824,plain,
% 11.69/1.98      ( r1_tarski(X0,X1) != iProver_top
% 11.69/1.98      | r1_tarski(X2,X1) != iProver_top
% 11.69/1.98      | r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) = iProver_top ),
% 11.69/1.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_12946,plain,
% 11.69/1.98      ( r1_tarski(k3_relat_1(sK2),X0) = iProver_top
% 11.69/1.98      | r1_tarski(k2_relat_1(sK2),X0) != iProver_top
% 11.69/1.98      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
% 11.69/1.98      inference(superposition,[status(thm)],[c_12606,c_824]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_14326,plain,
% 11.69/1.98      ( r1_tarski(k3_relat_1(sK2),k3_tarski(k1_enumset1(X0,X0,X1))) = iProver_top
% 11.69/1.98      | r1_tarski(k2_relat_1(sK2),k3_tarski(k1_enumset1(X0,X0,X1))) != iProver_top
% 11.69/1.98      | r1_tarski(k1_relat_1(sK2),X1) != iProver_top ),
% 11.69/1.98      inference(superposition,[status(thm)],[c_828,c_12946]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_27922,plain,
% 11.69/1.98      ( r1_tarski(k3_relat_1(sK2),k3_tarski(k1_enumset1(X0,X0,X1))) = iProver_top
% 11.69/1.98      | r1_tarski(k2_relat_1(sK2),X1) != iProver_top
% 11.69/1.98      | r1_tarski(k1_relat_1(sK2),X1) != iProver_top ),
% 11.69/1.98      inference(superposition,[status(thm)],[c_828,c_14326]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_34836,plain,
% 11.69/1.98      ( r1_tarski(k3_relat_1(sK2),k3_tarski(k1_enumset1(X0,X0,sK1))) = iProver_top
% 11.69/1.98      | r1_tarski(k2_relat_1(sK2),k3_tarski(k1_enumset1(X0,X0,sK1))) != iProver_top
% 11.69/1.98      | r1_tarski(k1_relat_1(sK2),k3_tarski(k1_enumset1(X0,X0,sK1))) != iProver_top ),
% 11.69/1.98      inference(superposition,[status(thm)],[c_3975,c_27922]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_34918,plain,
% 11.69/1.98      ( r1_tarski(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1))) = iProver_top
% 11.69/1.98      | r1_tarski(k2_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1))) != iProver_top
% 11.69/1.98      | r1_tarski(k1_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1))) != iProver_top ),
% 11.69/1.98      inference(instantiation,[status(thm)],[c_34836]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_3,plain,
% 11.69/1.98      ( r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
% 11.69/1.98      inference(cnf_transformation,[],[f60]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_825,plain,
% 11.69/1.98      ( r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) = iProver_top ),
% 11.69/1.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_12,plain,
% 11.69/1.98      ( v4_relat_1(X0,X1)
% 11.69/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 11.69/1.98      inference(cnf_transformation,[],[f51]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_10,plain,
% 11.69/1.98      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 11.69/1.98      inference(cnf_transformation,[],[f49]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_232,plain,
% 11.69/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.69/1.98      | ~ v1_relat_1(X0)
% 11.69/1.98      | k7_relat_1(X0,X1) = X0 ),
% 11.69/1.98      inference(resolution,[status(thm)],[c_12,c_10]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_813,plain,
% 11.69/1.98      ( k7_relat_1(X0,X1) = X0
% 11.69/1.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.69/1.98      | v1_relat_1(X0) != iProver_top ),
% 11.69/1.98      inference(predicate_to_equality,[status(thm)],[c_232]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_956,plain,
% 11.69/1.98      ( k7_relat_1(sK2,sK0) = sK2 | v1_relat_1(sK2) != iProver_top ),
% 11.69/1.98      inference(superposition,[status(thm)],[c_815,c_813]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_957,plain,
% 11.69/1.98      ( ~ v1_relat_1(sK2) | k7_relat_1(sK2,sK0) = sK2 ),
% 11.69/1.98      inference(predicate_to_equality_rev,[status(thm)],[c_956]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_2405,plain,
% 11.69/1.98      ( k7_relat_1(sK2,sK0) = sK2 ),
% 11.69/1.98      inference(global_propositional_subsumption,
% 11.69/1.98                [status(thm)],
% 11.69/1.98                [c_956,c_957,c_1040]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_11,plain,
% 11.69/1.98      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 11.69/1.98      inference(cnf_transformation,[],[f50]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_819,plain,
% 11.69/1.98      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
% 11.69/1.98      | v1_relat_1(X0) != iProver_top ),
% 11.69/1.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_2407,plain,
% 11.69/1.98      ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top
% 11.69/1.98      | v1_relat_1(sK2) != iProver_top ),
% 11.69/1.98      inference(superposition,[status(thm)],[c_2405,c_819]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_2853,plain,
% 11.69/1.98      ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
% 11.69/1.98      inference(global_propositional_subsumption,
% 11.69/1.98                [status(thm)],
% 11.69/1.98                [c_2407,c_1041]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_2857,plain,
% 11.69/1.98      ( k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),sK0)) = sK0 ),
% 11.69/1.98      inference(superposition,[status(thm)],[c_2853,c_826]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_1,plain,
% 11.69/1.98      ( r1_tarski(X0,X1)
% 11.69/1.98      | ~ r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) ),
% 11.69/1.98      inference(cnf_transformation,[],[f58]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_827,plain,
% 11.69/1.98      ( r1_tarski(X0,X1) = iProver_top
% 11.69/1.98      | r1_tarski(k3_tarski(k1_enumset1(X0,X0,X2)),X1) != iProver_top ),
% 11.69/1.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_2862,plain,
% 11.69/1.98      ( r1_tarski(k1_relat_1(sK2),X0) = iProver_top
% 11.69/1.98      | r1_tarski(sK0,X0) != iProver_top ),
% 11.69/1.98      inference(superposition,[status(thm)],[c_2857,c_827]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_3008,plain,
% 11.69/1.98      ( k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),X0)) = X0
% 11.69/1.98      | r1_tarski(sK0,X0) != iProver_top ),
% 11.69/1.98      inference(superposition,[status(thm)],[c_2862,c_826]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_3478,plain,
% 11.69/1.98      ( k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,X0)))) = k3_tarski(k1_enumset1(sK0,sK0,X0)) ),
% 11.69/1.98      inference(superposition,[status(thm)],[c_825,c_3008]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_5231,plain,
% 11.69/1.98      ( r1_tarski(k1_relat_1(sK2),X0) = iProver_top
% 11.69/1.98      | r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,X1)),X0) != iProver_top ),
% 11.69/1.98      inference(superposition,[status(thm)],[c_3478,c_827]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_5948,plain,
% 11.69/1.98      ( r1_tarski(X0,X1) != iProver_top
% 11.69/1.98      | r1_tarski(k1_relat_1(sK2),X1) = iProver_top
% 11.69/1.98      | r1_tarski(sK0,X1) != iProver_top ),
% 11.69/1.98      inference(superposition,[status(thm)],[c_824,c_5231]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_8986,plain,
% 11.69/1.98      ( r1_tarski(X0,X1) != iProver_top
% 11.69/1.98      | r1_tarski(k1_relat_1(sK2),k3_tarski(k1_enumset1(X2,X2,X1))) = iProver_top
% 11.69/1.98      | r1_tarski(sK0,k3_tarski(k1_enumset1(X2,X2,X1))) != iProver_top ),
% 11.69/1.98      inference(superposition,[status(thm)],[c_828,c_5948]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_22187,plain,
% 11.69/1.98      ( r1_tarski(k1_relat_1(sK2),k3_tarski(k1_enumset1(X0,X0,sK1))) = iProver_top
% 11.69/1.98      | r1_tarski(sK0,k3_tarski(k1_enumset1(X0,X0,sK1))) != iProver_top ),
% 11.69/1.98      inference(superposition,[status(thm)],[c_3716,c_8986]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_22206,plain,
% 11.69/1.98      ( r1_tarski(k1_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1))) = iProver_top
% 11.69/1.98      | r1_tarski(sK0,k3_tarski(k1_enumset1(sK0,sK0,sK1))) != iProver_top ),
% 11.69/1.98      inference(instantiation,[status(thm)],[c_22187]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_3962,plain,
% 11.69/1.98      ( k3_tarski(k1_enumset1(k2_relat_1(sK2),k2_relat_1(sK2),sK1)) = sK1 ),
% 11.69/1.98      inference(superposition,[status(thm)],[c_3716,c_826]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_3968,plain,
% 11.69/1.98      ( k3_tarski(k1_enumset1(X0,X0,k3_tarski(k1_enumset1(X1,X1,k3_tarski(k1_enumset1(X0,X0,X2)))))) = k3_tarski(k1_enumset1(X1,X1,k3_tarski(k1_enumset1(X0,X0,X2)))) ),
% 11.69/1.98      inference(superposition,[status(thm)],[c_825,c_1650]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_17116,plain,
% 11.69/1.98      ( r1_tarski(X0,k3_tarski(k1_enumset1(X1,X1,k3_tarski(k1_enumset1(X0,X0,X2))))) = iProver_top ),
% 11.69/1.98      inference(superposition,[status(thm)],[c_3968,c_825]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_17219,plain,
% 11.69/1.98      ( r1_tarski(k2_relat_1(sK2),k3_tarski(k1_enumset1(X0,X0,sK1))) = iProver_top ),
% 11.69/1.98      inference(superposition,[status(thm)],[c_3962,c_17116]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_17273,plain,
% 11.69/1.98      ( r1_tarski(k2_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1))) = iProver_top ),
% 11.69/1.98      inference(instantiation,[status(thm)],[c_17219]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_3525,plain,
% 11.69/1.98      ( r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,sK1))) ),
% 11.69/1.98      inference(instantiation,[status(thm)],[c_3]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_3526,plain,
% 11.69/1.98      ( r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,sK1))) = iProver_top ),
% 11.69/1.98      inference(predicate_to_equality,[status(thm)],[c_3525]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_3528,plain,
% 11.69/1.98      ( r1_tarski(sK0,k3_tarski(k1_enumset1(sK0,sK0,sK1))) = iProver_top ),
% 11.69/1.98      inference(instantiation,[status(thm)],[c_3526]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_15,negated_conjecture,
% 11.69/1.98      ( ~ r1_tarski(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1))) ),
% 11.69/1.98      inference(cnf_transformation,[],[f63]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(c_18,plain,
% 11.69/1.98      ( r1_tarski(k3_relat_1(sK2),k3_tarski(k1_enumset1(sK0,sK0,sK1))) != iProver_top ),
% 11.69/1.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 11.69/1.98  
% 11.69/1.98  cnf(contradiction,plain,
% 11.69/1.98      ( $false ),
% 11.69/1.98      inference(minisat,
% 11.69/1.98                [status(thm)],
% 11.69/1.98                [c_34918,c_22206,c_17273,c_3528,c_18]) ).
% 11.69/1.98  
% 11.69/1.98  
% 11.69/1.98  % SZS output end CNFRefutation for theBenchmark.p
% 11.69/1.98  
% 11.69/1.98  ------                               Statistics
% 11.69/1.98  
% 11.69/1.98  ------ Selected
% 11.69/1.98  
% 11.69/1.98  total_time:                             1.287
% 11.69/1.98  
%------------------------------------------------------------------------------
