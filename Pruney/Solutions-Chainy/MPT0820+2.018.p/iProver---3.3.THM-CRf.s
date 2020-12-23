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
% DateTime   : Thu Dec  3 11:54:54 EST 2020

% Result     : Theorem 3.58s
% Output     : CNFRefutation 3.58s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 343 expanded)
%              Number of clauses        :   91 ( 152 expanded)
%              Number of leaves         :   18 (  65 expanded)
%              Depth                    :   22
%              Number of atoms          :  344 ( 683 expanded)
%              Number of equality atoms :  119 ( 169 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

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

fof(f31,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f35])).

fof(f58,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f36])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f15,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f54,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f60,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f40,f41])).

fof(f61,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f42,f60])).

fof(f65,plain,(
    ! [X0] :
      ( k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f54,f61])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k2_enumset1(X0,X0,X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f38,f61])).

fof(f59,plain,(
    ~ r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f36])).

fof(f66,plain,(
    ~ r1_tarski(k3_relat_1(sK2),k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f59,f61])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f64,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f39,f60,f60])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f62,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f37,f61])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v5_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v5_relat_1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v5_relat_1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_13,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_432,plain,
    ( ~ v5_relat_1(X0_43,X1_43)
    | r1_tarski(k2_relat_1(X0_43),X1_43)
    | ~ v1_relat_1(X0_43) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_953,plain,
    ( v5_relat_1(X0_43,X1_43) != iProver_top
    | r1_tarski(k2_relat_1(X0_43),X1_43) = iProver_top
    | v1_relat_1(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_432])).

cnf(c_11,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_434,plain,
    ( ~ v4_relat_1(X0_43,X1_43)
    | r1_tarski(k1_relat_1(X0_43),X1_43)
    | ~ v1_relat_1(X0_43) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_951,plain,
    ( v4_relat_1(X0_43,X1_43) != iProver_top
    | r1_tarski(k1_relat_1(X0_43),X1_43) = iProver_top
    | v1_relat_1(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_434])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_426,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_959,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_426])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_438,plain,
    ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X1_43))
    | r1_tarski(X0_43,X1_43) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_947,plain,
    ( m1_subset_1(X0_43,k1_zfmisc_1(X1_43)) != iProver_top
    | r1_tarski(X0_43,X1_43) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_438])).

cnf(c_1330,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_959,c_947])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_5,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_151,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_5])).

cnf(c_152,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_151])).

cnf(c_185,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_7,c_152])).

cnf(c_425,plain,
    ( ~ r1_tarski(X0_43,X1_43)
    | ~ v1_relat_1(X1_43)
    | v1_relat_1(X0_43) ),
    inference(subtyping,[status(esa)],[c_185])).

cnf(c_960,plain,
    ( r1_tarski(X0_43,X1_43) != iProver_top
    | v1_relat_1(X1_43) != iProver_top
    | v1_relat_1(X0_43) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_425])).

cnf(c_3878,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1330,c_960])).

cnf(c_1120,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[status(thm)],[c_438,c_426])).

cnf(c_1200,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(resolution,[status(thm)],[c_425,c_1120])).

cnf(c_15,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_430,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_43,X1_43)) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1232,plain,
    ( v1_relat_1(sK2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1200,c_430])).

cnf(c_1233,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1232])).

cnf(c_4141,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3878,c_1233])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_431,plain,
    ( ~ v1_relat_1(X0_43)
    | k3_tarski(k2_enumset1(k1_relat_1(X0_43),k1_relat_1(X0_43),k1_relat_1(X0_43),k2_relat_1(X0_43))) = k3_relat_1(X0_43) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_954,plain,
    ( k3_tarski(k2_enumset1(k1_relat_1(X0_43),k1_relat_1(X0_43),k1_relat_1(X0_43),k2_relat_1(X0_43))) = k3_relat_1(X0_43)
    | v1_relat_1(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_431])).

cnf(c_4343,plain,
    ( k3_tarski(k2_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),k2_relat_1(sK2))) = k3_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_4141,c_954])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k3_tarski(k2_enumset1(X2,X2,X2,X0)),X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_443,plain,
    ( ~ r1_tarski(X0_43,X1_43)
    | ~ r1_tarski(X2_43,X1_43)
    | r1_tarski(k3_tarski(k2_enumset1(X2_43,X2_43,X2_43,X0_43)),X1_43) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_943,plain,
    ( r1_tarski(X0_43,X1_43) != iProver_top
    | r1_tarski(X2_43,X1_43) != iProver_top
    | r1_tarski(k3_tarski(k2_enumset1(X2_43,X2_43,X2_43,X0_43)),X1_43) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_443])).

cnf(c_4485,plain,
    ( r1_tarski(k3_relat_1(sK2),X0_43) = iProver_top
    | r1_tarski(k2_relat_1(sK2),X0_43) != iProver_top
    | r1_tarski(k1_relat_1(sK2),X0_43) != iProver_top ),
    inference(superposition,[status(thm)],[c_4343,c_943])).

cnf(c_5805,plain,
    ( v4_relat_1(sK2,X0_43) != iProver_top
    | r1_tarski(k3_relat_1(sK2),X0_43) = iProver_top
    | r1_tarski(k2_relat_1(sK2),X0_43) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_951,c_4485])).

cnf(c_9890,plain,
    ( r1_tarski(k2_relat_1(sK2),X0_43) != iProver_top
    | r1_tarski(k3_relat_1(sK2),X0_43) = iProver_top
    | v4_relat_1(sK2,X0_43) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5805,c_1233])).

cnf(c_9891,plain,
    ( v4_relat_1(sK2,X0_43) != iProver_top
    | r1_tarski(k3_relat_1(sK2),X0_43) = iProver_top
    | r1_tarski(k2_relat_1(sK2),X0_43) != iProver_top ),
    inference(renaming,[status(thm)],[c_9890])).

cnf(c_9899,plain,
    ( v5_relat_1(sK2,X0_43) != iProver_top
    | v4_relat_1(sK2,X0_43) != iProver_top
    | r1_tarski(k3_relat_1(sK2),X0_43) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_953,c_9891])).

cnf(c_10505,plain,
    ( r1_tarski(k3_relat_1(sK2),X0_43) = iProver_top
    | v4_relat_1(sK2,X0_43) != iProver_top
    | v5_relat_1(sK2,X0_43) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9899,c_1233])).

cnf(c_10506,plain,
    ( v5_relat_1(sK2,X0_43) != iProver_top
    | v4_relat_1(sK2,X0_43) != iProver_top
    | r1_tarski(k3_relat_1(sK2),X0_43) = iProver_top ),
    inference(renaming,[status(thm)],[c_10505])).

cnf(c_18,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(sK2),k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_427,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(sK2),k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_958,plain,
    ( r1_tarski(k3_relat_1(sK2),k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_427])).

cnf(c_10514,plain,
    ( v5_relat_1(sK2,k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1))) != iProver_top
    | v4_relat_1(sK2,k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_10506,c_958])).

cnf(c_2,plain,
    ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_442,plain,
    ( k2_enumset1(X0_43,X0_43,X0_43,X1_43) = k2_enumset1(X1_43,X1_43,X1_43,X0_43) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_0,plain,
    ( r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_444,plain,
    ( r1_tarski(X0_43,k3_tarski(k2_enumset1(X0_43,X0_43,X0_43,X1_43))) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_942,plain,
    ( r1_tarski(X0_43,k3_tarski(k2_enumset1(X0_43,X0_43,X0_43,X1_43))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_444])).

cnf(c_1222,plain,
    ( r1_tarski(X0_43,k3_tarski(k2_enumset1(X1_43,X1_43,X1_43,X0_43))) = iProver_top ),
    inference(superposition,[status(thm)],[c_442,c_942])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_441,plain,
    ( ~ r1_tarski(X0_43,X1_43)
    | r1_tarski(k2_zfmisc_1(X2_43,X0_43),k2_zfmisc_1(X2_43,X1_43)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_944,plain,
    ( r1_tarski(X0_43,X1_43) != iProver_top
    | r1_tarski(k2_zfmisc_1(X2_43,X0_43),k2_zfmisc_1(X2_43,X1_43)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_441])).

cnf(c_439,plain,
    ( m1_subset_1(X0_43,k1_zfmisc_1(X1_43))
    | ~ r1_tarski(X0_43,X1_43) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_946,plain,
    ( m1_subset_1(X0_43,k1_zfmisc_1(X1_43)) = iProver_top
    | r1_tarski(X0_43,X1_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_439])).

cnf(c_16,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_429,plain,
    ( v5_relat_1(X0_43,X1_43)
    | ~ m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X2_43,X1_43))) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_956,plain,
    ( v5_relat_1(X0_43,X1_43) = iProver_top
    | m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X2_43,X1_43))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_429])).

cnf(c_1497,plain,
    ( v5_relat_1(X0_43,X1_43) = iProver_top
    | r1_tarski(X0_43,k2_zfmisc_1(X2_43,X1_43)) != iProver_top ),
    inference(superposition,[status(thm)],[c_946,c_956])).

cnf(c_2196,plain,
    ( v5_relat_1(k2_zfmisc_1(X0_43,X1_43),X2_43) = iProver_top
    | r1_tarski(X1_43,X2_43) != iProver_top ),
    inference(superposition,[status(thm)],[c_944,c_1497])).

cnf(c_9,plain,
    ( ~ v5_relat_1(X0,X1)
    | v5_relat_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_436,plain,
    ( ~ v5_relat_1(X0_43,X1_43)
    | v5_relat_1(X2_43,X1_43)
    | ~ m1_subset_1(X2_43,k1_zfmisc_1(X0_43))
    | ~ v1_relat_1(X0_43) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_949,plain,
    ( v5_relat_1(X0_43,X1_43) != iProver_top
    | v5_relat_1(X2_43,X1_43) = iProver_top
    | m1_subset_1(X2_43,k1_zfmisc_1(X0_43)) != iProver_top
    | v1_relat_1(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_436])).

cnf(c_4319,plain,
    ( v5_relat_1(k2_zfmisc_1(sK0,sK1),X0_43) != iProver_top
    | v5_relat_1(sK2,X0_43) = iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_959,c_949])).

cnf(c_1426,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_430])).

cnf(c_1427,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1426])).

cnf(c_4932,plain,
    ( v5_relat_1(sK2,X0_43) = iProver_top
    | v5_relat_1(k2_zfmisc_1(sK0,sK1),X0_43) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4319,c_1427])).

cnf(c_4933,plain,
    ( v5_relat_1(k2_zfmisc_1(sK0,sK1),X0_43) != iProver_top
    | v5_relat_1(sK2,X0_43) = iProver_top ),
    inference(renaming,[status(thm)],[c_4932])).

cnf(c_4941,plain,
    ( v5_relat_1(sK2,X0_43) = iProver_top
    | r1_tarski(sK1,X0_43) != iProver_top ),
    inference(superposition,[status(thm)],[c_2196,c_4933])).

cnf(c_5447,plain,
    ( v5_relat_1(sK2,k3_tarski(k2_enumset1(X0_43,X0_43,X0_43,sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1222,c_4941])).

cnf(c_5456,plain,
    ( v5_relat_1(sK2,k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_5447])).

cnf(c_10577,plain,
    ( v4_relat_1(sK2,k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10514,c_5456])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_440,plain,
    ( ~ r1_tarski(X0_43,X1_43)
    | r1_tarski(k2_zfmisc_1(X0_43,X2_43),k2_zfmisc_1(X1_43,X2_43)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_945,plain,
    ( r1_tarski(X0_43,X1_43) != iProver_top
    | r1_tarski(k2_zfmisc_1(X0_43,X2_43),k2_zfmisc_1(X1_43,X2_43)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_440])).

cnf(c_17,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_428,plain,
    ( v4_relat_1(X0_43,X1_43)
    | ~ m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X1_43,X2_43))) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_957,plain,
    ( v4_relat_1(X0_43,X1_43) = iProver_top
    | m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X1_43,X2_43))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_428])).

cnf(c_1629,plain,
    ( v4_relat_1(X0_43,X1_43) = iProver_top
    | r1_tarski(X0_43,k2_zfmisc_1(X1_43,X2_43)) != iProver_top ),
    inference(superposition,[status(thm)],[c_946,c_957])).

cnf(c_2223,plain,
    ( v4_relat_1(k2_zfmisc_1(X0_43,X1_43),X2_43) = iProver_top
    | r1_tarski(X0_43,X2_43) != iProver_top ),
    inference(superposition,[status(thm)],[c_945,c_1629])).

cnf(c_8,plain,
    ( ~ v4_relat_1(X0,X1)
    | v4_relat_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_437,plain,
    ( ~ v4_relat_1(X0_43,X1_43)
    | v4_relat_1(X2_43,X1_43)
    | ~ m1_subset_1(X2_43,k1_zfmisc_1(X0_43))
    | ~ v1_relat_1(X0_43) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_948,plain,
    ( v4_relat_1(X0_43,X1_43) != iProver_top
    | v4_relat_1(X2_43,X1_43) = iProver_top
    | m1_subset_1(X2_43,k1_zfmisc_1(X0_43)) != iProver_top
    | v1_relat_1(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_437])).

cnf(c_2709,plain,
    ( v4_relat_1(k2_zfmisc_1(sK0,sK1),X0_43) != iProver_top
    | v4_relat_1(sK2,X0_43) = iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_959,c_948])).

cnf(c_3550,plain,
    ( v4_relat_1(sK2,X0_43) = iProver_top
    | v4_relat_1(k2_zfmisc_1(sK0,sK1),X0_43) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2709,c_1427])).

cnf(c_3551,plain,
    ( v4_relat_1(k2_zfmisc_1(sK0,sK1),X0_43) != iProver_top
    | v4_relat_1(sK2,X0_43) = iProver_top ),
    inference(renaming,[status(thm)],[c_3550])).

cnf(c_3556,plain,
    ( v4_relat_1(sK2,X0_43) = iProver_top
    | r1_tarski(sK0,X0_43) != iProver_top ),
    inference(superposition,[status(thm)],[c_2223,c_3551])).

cnf(c_3561,plain,
    ( v4_relat_1(sK2,k3_tarski(k2_enumset1(sK0,sK0,sK0,X0_43))) = iProver_top ),
    inference(superposition,[status(thm)],[c_942,c_3556])).

cnf(c_10582,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_10577,c_3561])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:45:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.58/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.58/0.99  
% 3.58/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.58/0.99  
% 3.58/0.99  ------  iProver source info
% 3.58/0.99  
% 3.58/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.58/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.58/0.99  git: non_committed_changes: false
% 3.58/0.99  git: last_make_outside_of_git: false
% 3.58/0.99  
% 3.58/0.99  ------ 
% 3.58/0.99  ------ Parsing...
% 3.58/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.58/0.99  
% 3.58/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.58/0.99  
% 3.58/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.58/0.99  
% 3.58/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.58/0.99  ------ Proving...
% 3.58/0.99  ------ Problem Properties 
% 3.58/0.99  
% 3.58/0.99  
% 3.58/0.99  clauses                                 20
% 3.58/0.99  conjectures                             2
% 3.58/0.99  EPR                                     1
% 3.58/0.99  Horn                                    20
% 3.58/0.99  unary                                   5
% 3.58/0.99  binary                                  7
% 3.58/0.99  lits                                    45
% 3.58/0.99  lits eq                                 2
% 3.58/0.99  fd_pure                                 0
% 3.58/0.99  fd_pseudo                               0
% 3.58/0.99  fd_cond                                 0
% 3.58/0.99  fd_pseudo_cond                          0
% 3.58/0.99  AC symbols                              0
% 3.58/0.99  
% 3.58/0.99  ------ Input Options Time Limit: Unbounded
% 3.58/0.99  
% 3.58/0.99  
% 3.58/0.99  ------ 
% 3.58/0.99  Current options:
% 3.58/0.99  ------ 
% 3.58/0.99  
% 3.58/0.99  
% 3.58/0.99  
% 3.58/0.99  
% 3.58/0.99  ------ Proving...
% 3.58/0.99  
% 3.58/0.99  
% 3.58/0.99  % SZS status Theorem for theBenchmark.p
% 3.58/0.99  
% 3.58/0.99   Resolution empty clause
% 3.58/0.99  
% 3.58/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.58/0.99  
% 3.58/0.99  fof(f13,axiom,(
% 3.58/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f28,plain,(
% 3.58/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.58/0.99    inference(ennf_transformation,[],[f13])).
% 3.58/0.99  
% 3.58/0.99  fof(f34,plain,(
% 3.58/0.99    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.58/0.99    inference(nnf_transformation,[],[f28])).
% 3.58/0.99  
% 3.58/0.99  fof(f52,plain,(
% 3.58/0.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.58/0.99    inference(cnf_transformation,[],[f34])).
% 3.58/0.99  
% 3.58/0.99  fof(f12,axiom,(
% 3.58/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f27,plain,(
% 3.58/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.58/0.99    inference(ennf_transformation,[],[f12])).
% 3.58/0.99  
% 3.58/0.99  fof(f33,plain,(
% 3.58/0.99    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.58/0.99    inference(nnf_transformation,[],[f27])).
% 3.58/0.99  
% 3.58/0.99  fof(f50,plain,(
% 3.58/0.99    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.58/0.99    inference(cnf_transformation,[],[f33])).
% 3.58/0.99  
% 3.58/0.99  fof(f17,conjecture,(
% 3.58/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)))),
% 3.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f18,negated_conjecture,(
% 3.58/0.99    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)))),
% 3.58/0.99    inference(negated_conjecture,[],[f17])).
% 3.58/0.99  
% 3.58/0.99  fof(f31,plain,(
% 3.58/0.99    ? [X0,X1,X2] : (~r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.58/0.99    inference(ennf_transformation,[],[f18])).
% 3.58/0.99  
% 3.58/0.99  fof(f35,plain,(
% 3.58/0.99    ? [X0,X1,X2] : (~r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (~r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 3.58/0.99    introduced(choice_axiom,[])).
% 3.58/0.99  
% 3.58/0.99  fof(f36,plain,(
% 3.58/0.99    ~r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.58/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f35])).
% 3.58/0.99  
% 3.58/0.99  fof(f58,plain,(
% 3.58/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.58/0.99    inference(cnf_transformation,[],[f36])).
% 3.58/0.99  
% 3.58/0.99  fof(f8,axiom,(
% 3.58/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f32,plain,(
% 3.58/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.58/0.99    inference(nnf_transformation,[],[f8])).
% 3.58/0.99  
% 3.58/0.99  fof(f45,plain,(
% 3.58/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.58/0.99    inference(cnf_transformation,[],[f32])).
% 3.58/0.99  
% 3.58/0.99  fof(f9,axiom,(
% 3.58/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f22,plain,(
% 3.58/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.58/0.99    inference(ennf_transformation,[],[f9])).
% 3.58/0.99  
% 3.58/0.99  fof(f47,plain,(
% 3.58/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.58/0.99    inference(cnf_transformation,[],[f22])).
% 3.58/0.99  
% 3.58/0.99  fof(f46,plain,(
% 3.58/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.58/0.99    inference(cnf_transformation,[],[f32])).
% 3.58/0.99  
% 3.58/0.99  fof(f15,axiom,(
% 3.58/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f55,plain,(
% 3.58/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.58/0.99    inference(cnf_transformation,[],[f15])).
% 3.58/0.99  
% 3.58/0.99  fof(f14,axiom,(
% 3.58/0.99    ! [X0] : (v1_relat_1(X0) => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0))),
% 3.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f29,plain,(
% 3.58/0.99    ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0))),
% 3.58/0.99    inference(ennf_transformation,[],[f14])).
% 3.58/0.99  
% 3.58/0.99  fof(f54,plain,(
% 3.58/0.99    ( ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.58/0.99    inference(cnf_transformation,[],[f29])).
% 3.58/0.99  
% 3.58/0.99  fof(f6,axiom,(
% 3.58/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f42,plain,(
% 3.58/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.58/0.99    inference(cnf_transformation,[],[f6])).
% 3.58/0.99  
% 3.58/0.99  fof(f4,axiom,(
% 3.58/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f40,plain,(
% 3.58/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.58/0.99    inference(cnf_transformation,[],[f4])).
% 3.58/0.99  
% 3.58/0.99  fof(f5,axiom,(
% 3.58/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f41,plain,(
% 3.58/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.58/0.99    inference(cnf_transformation,[],[f5])).
% 3.58/0.99  
% 3.58/0.99  fof(f60,plain,(
% 3.58/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.58/0.99    inference(definition_unfolding,[],[f40,f41])).
% 3.58/0.99  
% 3.58/0.99  fof(f61,plain,(
% 3.58/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 3.58/0.99    inference(definition_unfolding,[],[f42,f60])).
% 3.58/0.99  
% 3.58/0.99  fof(f65,plain,(
% 3.58/0.99    ( ! [X0] : (k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.58/0.99    inference(definition_unfolding,[],[f54,f61])).
% 3.58/0.99  
% 3.58/0.99  fof(f2,axiom,(
% 3.58/0.99    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 3.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f19,plain,(
% 3.58/0.99    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 3.58/0.99    inference(ennf_transformation,[],[f2])).
% 3.58/0.99  
% 3.58/0.99  fof(f20,plain,(
% 3.58/0.99    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 3.58/0.99    inference(flattening,[],[f19])).
% 3.58/0.99  
% 3.58/0.99  fof(f38,plain,(
% 3.58/0.99    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 3.58/0.99    inference(cnf_transformation,[],[f20])).
% 3.58/0.99  
% 3.58/0.99  fof(f63,plain,(
% 3.58/0.99    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k2_enumset1(X0,X0,X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 3.58/0.99    inference(definition_unfolding,[],[f38,f61])).
% 3.58/0.99  
% 3.58/0.99  fof(f59,plain,(
% 3.58/0.99    ~r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))),
% 3.58/0.99    inference(cnf_transformation,[],[f36])).
% 3.58/0.99  
% 3.58/0.99  fof(f66,plain,(
% 3.58/0.99    ~r1_tarski(k3_relat_1(sK2),k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1)))),
% 3.58/0.99    inference(definition_unfolding,[],[f59,f61])).
% 3.58/0.99  
% 3.58/0.99  fof(f3,axiom,(
% 3.58/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f39,plain,(
% 3.58/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.58/0.99    inference(cnf_transformation,[],[f3])).
% 3.58/0.99  
% 3.58/0.99  fof(f64,plain,(
% 3.58/0.99    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 3.58/0.99    inference(definition_unfolding,[],[f39,f60,f60])).
% 3.58/0.99  
% 3.58/0.99  fof(f1,axiom,(
% 3.58/0.99    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f37,plain,(
% 3.58/0.99    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.58/0.99    inference(cnf_transformation,[],[f1])).
% 3.58/0.99  
% 3.58/0.99  fof(f62,plain,(
% 3.58/0.99    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1)))) )),
% 3.58/0.99    inference(definition_unfolding,[],[f37,f61])).
% 3.58/0.99  
% 3.58/0.99  fof(f7,axiom,(
% 3.58/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X1) => (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))))),
% 3.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f21,plain,(
% 3.58/0.99    ! [X0,X1,X2] : ((r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X1))),
% 3.58/0.99    inference(ennf_transformation,[],[f7])).
% 3.58/0.99  
% 3.58/0.99  fof(f44,plain,(
% 3.58/0.99    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 3.58/0.99    inference(cnf_transformation,[],[f21])).
% 3.58/0.99  
% 3.58/0.99  fof(f16,axiom,(
% 3.58/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f30,plain,(
% 3.58/0.99    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.58/0.99    inference(ennf_transformation,[],[f16])).
% 3.58/0.99  
% 3.58/0.99  fof(f57,plain,(
% 3.58/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.58/0.99    inference(cnf_transformation,[],[f30])).
% 3.58/0.99  
% 3.58/0.99  fof(f11,axiom,(
% 3.58/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X1)) => v5_relat_1(X2,X0)))),
% 3.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f25,plain,(
% 3.58/0.99    ! [X0,X1] : (! [X2] : (v5_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X1))) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.58/0.99    inference(ennf_transformation,[],[f11])).
% 3.58/0.99  
% 3.58/0.99  fof(f26,plain,(
% 3.58/0.99    ! [X0,X1] : (! [X2] : (v5_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X1))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.58/0.99    inference(flattening,[],[f25])).
% 3.58/0.99  
% 3.58/0.99  fof(f49,plain,(
% 3.58/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.58/0.99    inference(cnf_transformation,[],[f26])).
% 3.58/0.99  
% 3.58/0.99  fof(f43,plain,(
% 3.58/0.99    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 3.58/0.99    inference(cnf_transformation,[],[f21])).
% 3.58/0.99  
% 3.58/0.99  fof(f56,plain,(
% 3.58/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.58/0.99    inference(cnf_transformation,[],[f30])).
% 3.58/0.99  
% 3.58/0.99  fof(f10,axiom,(
% 3.58/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X1)) => v4_relat_1(X2,X0)))),
% 3.58/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.58/0.99  
% 3.58/0.99  fof(f23,plain,(
% 3.58/0.99    ! [X0,X1] : (! [X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X1))) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.58/0.99    inference(ennf_transformation,[],[f10])).
% 3.58/0.99  
% 3.58/0.99  fof(f24,plain,(
% 3.58/0.99    ! [X0,X1] : (! [X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X1))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.58/0.99    inference(flattening,[],[f23])).
% 3.58/0.99  
% 3.58/0.99  fof(f48,plain,(
% 3.58/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.58/0.99    inference(cnf_transformation,[],[f24])).
% 3.58/0.99  
% 3.58/0.99  cnf(c_13,plain,
% 3.58/0.99      ( ~ v5_relat_1(X0,X1) | r1_tarski(k2_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 3.58/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_432,plain,
% 3.58/0.99      ( ~ v5_relat_1(X0_43,X1_43)
% 3.58/0.99      | r1_tarski(k2_relat_1(X0_43),X1_43)
% 3.58/0.99      | ~ v1_relat_1(X0_43) ),
% 3.58/0.99      inference(subtyping,[status(esa)],[c_13]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_953,plain,
% 3.58/0.99      ( v5_relat_1(X0_43,X1_43) != iProver_top
% 3.58/0.99      | r1_tarski(k2_relat_1(X0_43),X1_43) = iProver_top
% 3.58/0.99      | v1_relat_1(X0_43) != iProver_top ),
% 3.58/0.99      inference(predicate_to_equality,[status(thm)],[c_432]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_11,plain,
% 3.58/0.99      ( ~ v4_relat_1(X0,X1) | r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 3.58/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_434,plain,
% 3.58/0.99      ( ~ v4_relat_1(X0_43,X1_43)
% 3.58/0.99      | r1_tarski(k1_relat_1(X0_43),X1_43)
% 3.58/0.99      | ~ v1_relat_1(X0_43) ),
% 3.58/0.99      inference(subtyping,[status(esa)],[c_11]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_951,plain,
% 3.58/0.99      ( v4_relat_1(X0_43,X1_43) != iProver_top
% 3.58/0.99      | r1_tarski(k1_relat_1(X0_43),X1_43) = iProver_top
% 3.58/0.99      | v1_relat_1(X0_43) != iProver_top ),
% 3.58/0.99      inference(predicate_to_equality,[status(thm)],[c_434]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_19,negated_conjecture,
% 3.58/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.58/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_426,negated_conjecture,
% 3.58/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.58/0.99      inference(subtyping,[status(esa)],[c_19]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_959,plain,
% 3.58/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.58/0.99      inference(predicate_to_equality,[status(thm)],[c_426]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_6,plain,
% 3.58/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.58/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_438,plain,
% 3.58/0.99      ( ~ m1_subset_1(X0_43,k1_zfmisc_1(X1_43)) | r1_tarski(X0_43,X1_43) ),
% 3.58/0.99      inference(subtyping,[status(esa)],[c_6]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_947,plain,
% 3.58/0.99      ( m1_subset_1(X0_43,k1_zfmisc_1(X1_43)) != iProver_top
% 3.58/0.99      | r1_tarski(X0_43,X1_43) = iProver_top ),
% 3.58/0.99      inference(predicate_to_equality,[status(thm)],[c_438]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_1330,plain,
% 3.58/0.99      ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 3.58/0.99      inference(superposition,[status(thm)],[c_959,c_947]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_7,plain,
% 3.58/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.58/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_5,plain,
% 3.58/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.58/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_151,plain,
% 3.58/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.58/0.99      inference(prop_impl,[status(thm)],[c_5]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_152,plain,
% 3.58/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.58/0.99      inference(renaming,[status(thm)],[c_151]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_185,plain,
% 3.58/0.99      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.58/0.99      inference(bin_hyper_res,[status(thm)],[c_7,c_152]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_425,plain,
% 3.58/0.99      ( ~ r1_tarski(X0_43,X1_43) | ~ v1_relat_1(X1_43) | v1_relat_1(X0_43) ),
% 3.58/0.99      inference(subtyping,[status(esa)],[c_185]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_960,plain,
% 3.58/0.99      ( r1_tarski(X0_43,X1_43) != iProver_top
% 3.58/0.99      | v1_relat_1(X1_43) != iProver_top
% 3.58/0.99      | v1_relat_1(X0_43) = iProver_top ),
% 3.58/0.99      inference(predicate_to_equality,[status(thm)],[c_425]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_3878,plain,
% 3.58/0.99      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 3.58/0.99      | v1_relat_1(sK2) = iProver_top ),
% 3.58/0.99      inference(superposition,[status(thm)],[c_1330,c_960]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_1120,plain,
% 3.58/0.99      ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
% 3.58/0.99      inference(resolution,[status(thm)],[c_438,c_426]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_1200,plain,
% 3.58/0.99      ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK2) ),
% 3.58/0.99      inference(resolution,[status(thm)],[c_425,c_1120]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_15,plain,
% 3.58/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.58/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_430,plain,
% 3.58/0.99      ( v1_relat_1(k2_zfmisc_1(X0_43,X1_43)) ),
% 3.58/0.99      inference(subtyping,[status(esa)],[c_15]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_1232,plain,
% 3.58/0.99      ( v1_relat_1(sK2) ),
% 3.58/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_1200,c_430]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_1233,plain,
% 3.58/0.99      ( v1_relat_1(sK2) = iProver_top ),
% 3.58/0.99      inference(predicate_to_equality,[status(thm)],[c_1232]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_4141,plain,
% 3.58/0.99      ( v1_relat_1(sK2) = iProver_top ),
% 3.58/0.99      inference(global_propositional_subsumption,[status(thm)],[c_3878,c_1233]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_14,plain,
% 3.58/0.99      ( ~ v1_relat_1(X0)
% 3.58/0.99      | k3_tarski(k2_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) ),
% 3.58/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_431,plain,
% 3.58/0.99      ( ~ v1_relat_1(X0_43)
% 3.58/0.99      | k3_tarski(k2_enumset1(k1_relat_1(X0_43),k1_relat_1(X0_43),k1_relat_1(X0_43),k2_relat_1(X0_43))) = k3_relat_1(X0_43) ),
% 3.58/0.99      inference(subtyping,[status(esa)],[c_14]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_954,plain,
% 3.58/0.99      ( k3_tarski(k2_enumset1(k1_relat_1(X0_43),k1_relat_1(X0_43),k1_relat_1(X0_43),k2_relat_1(X0_43))) = k3_relat_1(X0_43)
% 3.58/0.99      | v1_relat_1(X0_43) != iProver_top ),
% 3.58/0.99      inference(predicate_to_equality,[status(thm)],[c_431]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_4343,plain,
% 3.58/0.99      ( k3_tarski(k2_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k1_relat_1(sK2),k2_relat_1(sK2))) = k3_relat_1(sK2) ),
% 3.58/0.99      inference(superposition,[status(thm)],[c_4141,c_954]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_1,plain,
% 3.58/0.99      ( ~ r1_tarski(X0,X1)
% 3.58/0.99      | ~ r1_tarski(X2,X1)
% 3.58/0.99      | r1_tarski(k3_tarski(k2_enumset1(X2,X2,X2,X0)),X1) ),
% 3.58/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_443,plain,
% 3.58/0.99      ( ~ r1_tarski(X0_43,X1_43)
% 3.58/0.99      | ~ r1_tarski(X2_43,X1_43)
% 3.58/0.99      | r1_tarski(k3_tarski(k2_enumset1(X2_43,X2_43,X2_43,X0_43)),X1_43) ),
% 3.58/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_943,plain,
% 3.58/0.99      ( r1_tarski(X0_43,X1_43) != iProver_top
% 3.58/0.99      | r1_tarski(X2_43,X1_43) != iProver_top
% 3.58/0.99      | r1_tarski(k3_tarski(k2_enumset1(X2_43,X2_43,X2_43,X0_43)),X1_43) = iProver_top ),
% 3.58/0.99      inference(predicate_to_equality,[status(thm)],[c_443]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_4485,plain,
% 3.58/0.99      ( r1_tarski(k3_relat_1(sK2),X0_43) = iProver_top
% 3.58/0.99      | r1_tarski(k2_relat_1(sK2),X0_43) != iProver_top
% 3.58/0.99      | r1_tarski(k1_relat_1(sK2),X0_43) != iProver_top ),
% 3.58/0.99      inference(superposition,[status(thm)],[c_4343,c_943]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_5805,plain,
% 3.58/0.99      ( v4_relat_1(sK2,X0_43) != iProver_top
% 3.58/0.99      | r1_tarski(k3_relat_1(sK2),X0_43) = iProver_top
% 3.58/0.99      | r1_tarski(k2_relat_1(sK2),X0_43) != iProver_top
% 3.58/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.58/0.99      inference(superposition,[status(thm)],[c_951,c_4485]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_9890,plain,
% 3.58/0.99      ( r1_tarski(k2_relat_1(sK2),X0_43) != iProver_top
% 3.58/0.99      | r1_tarski(k3_relat_1(sK2),X0_43) = iProver_top
% 3.58/0.99      | v4_relat_1(sK2,X0_43) != iProver_top ),
% 3.58/0.99      inference(global_propositional_subsumption,[status(thm)],[c_5805,c_1233]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_9891,plain,
% 3.58/0.99      ( v4_relat_1(sK2,X0_43) != iProver_top
% 3.58/0.99      | r1_tarski(k3_relat_1(sK2),X0_43) = iProver_top
% 3.58/0.99      | r1_tarski(k2_relat_1(sK2),X0_43) != iProver_top ),
% 3.58/0.99      inference(renaming,[status(thm)],[c_9890]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_9899,plain,
% 3.58/0.99      ( v5_relat_1(sK2,X0_43) != iProver_top
% 3.58/0.99      | v4_relat_1(sK2,X0_43) != iProver_top
% 3.58/0.99      | r1_tarski(k3_relat_1(sK2),X0_43) = iProver_top
% 3.58/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.58/0.99      inference(superposition,[status(thm)],[c_953,c_9891]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_10505,plain,
% 3.58/0.99      ( r1_tarski(k3_relat_1(sK2),X0_43) = iProver_top
% 3.58/0.99      | v4_relat_1(sK2,X0_43) != iProver_top
% 3.58/0.99      | v5_relat_1(sK2,X0_43) != iProver_top ),
% 3.58/0.99      inference(global_propositional_subsumption,[status(thm)],[c_9899,c_1233]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_10506,plain,
% 3.58/0.99      ( v5_relat_1(sK2,X0_43) != iProver_top
% 3.58/0.99      | v4_relat_1(sK2,X0_43) != iProver_top
% 3.58/0.99      | r1_tarski(k3_relat_1(sK2),X0_43) = iProver_top ),
% 3.58/0.99      inference(renaming,[status(thm)],[c_10505]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_18,negated_conjecture,
% 3.58/0.99      ( ~ r1_tarski(k3_relat_1(sK2),k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1))) ),
% 3.58/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_427,negated_conjecture,
% 3.58/0.99      ( ~ r1_tarski(k3_relat_1(sK2),k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1))) ),
% 3.58/0.99      inference(subtyping,[status(esa)],[c_18]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_958,plain,
% 3.58/0.99      ( r1_tarski(k3_relat_1(sK2),k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1))) != iProver_top ),
% 3.58/0.99      inference(predicate_to_equality,[status(thm)],[c_427]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_10514,plain,
% 3.58/0.99      ( v5_relat_1(sK2,k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1))) != iProver_top
% 3.58/0.99      | v4_relat_1(sK2,k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1))) != iProver_top ),
% 3.58/0.99      inference(superposition,[status(thm)],[c_10506,c_958]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_2,plain,
% 3.58/0.99      ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
% 3.58/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_442,plain,
% 3.58/0.99      ( k2_enumset1(X0_43,X0_43,X0_43,X1_43) = k2_enumset1(X1_43,X1_43,X1_43,X0_43) ),
% 3.58/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_0,plain,
% 3.58/0.99      ( r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
% 3.58/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_444,plain,
% 3.58/0.99      ( r1_tarski(X0_43,k3_tarski(k2_enumset1(X0_43,X0_43,X0_43,X1_43))) ),
% 3.58/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_942,plain,
% 3.58/0.99      ( r1_tarski(X0_43,k3_tarski(k2_enumset1(X0_43,X0_43,X0_43,X1_43))) = iProver_top ),
% 3.58/0.99      inference(predicate_to_equality,[status(thm)],[c_444]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_1222,plain,
% 3.58/0.99      ( r1_tarski(X0_43,k3_tarski(k2_enumset1(X1_43,X1_43,X1_43,X0_43))) = iProver_top ),
% 3.58/0.99      inference(superposition,[status(thm)],[c_442,c_942]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_3,plain,
% 3.58/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
% 3.58/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_441,plain,
% 3.58/0.99      ( ~ r1_tarski(X0_43,X1_43)
% 3.58/0.99      | r1_tarski(k2_zfmisc_1(X2_43,X0_43),k2_zfmisc_1(X2_43,X1_43)) ),
% 3.58/0.99      inference(subtyping,[status(esa)],[c_3]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_944,plain,
% 3.58/0.99      ( r1_tarski(X0_43,X1_43) != iProver_top
% 3.58/0.99      | r1_tarski(k2_zfmisc_1(X2_43,X0_43),k2_zfmisc_1(X2_43,X1_43)) = iProver_top ),
% 3.58/0.99      inference(predicate_to_equality,[status(thm)],[c_441]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_439,plain,
% 3.58/0.99      ( m1_subset_1(X0_43,k1_zfmisc_1(X1_43)) | ~ r1_tarski(X0_43,X1_43) ),
% 3.58/0.99      inference(subtyping,[status(esa)],[c_5]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_946,plain,
% 3.58/0.99      ( m1_subset_1(X0_43,k1_zfmisc_1(X1_43)) = iProver_top
% 3.58/0.99      | r1_tarski(X0_43,X1_43) != iProver_top ),
% 3.58/0.99      inference(predicate_to_equality,[status(thm)],[c_439]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_16,plain,
% 3.58/0.99      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.58/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_429,plain,
% 3.58/0.99      ( v5_relat_1(X0_43,X1_43)
% 3.58/0.99      | ~ m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X2_43,X1_43))) ),
% 3.58/0.99      inference(subtyping,[status(esa)],[c_16]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_956,plain,
% 3.58/0.99      ( v5_relat_1(X0_43,X1_43) = iProver_top
% 3.58/0.99      | m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X2_43,X1_43))) != iProver_top ),
% 3.58/0.99      inference(predicate_to_equality,[status(thm)],[c_429]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_1497,plain,
% 3.58/0.99      ( v5_relat_1(X0_43,X1_43) = iProver_top
% 3.58/0.99      | r1_tarski(X0_43,k2_zfmisc_1(X2_43,X1_43)) != iProver_top ),
% 3.58/0.99      inference(superposition,[status(thm)],[c_946,c_956]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_2196,plain,
% 3.58/0.99      ( v5_relat_1(k2_zfmisc_1(X0_43,X1_43),X2_43) = iProver_top
% 3.58/0.99      | r1_tarski(X1_43,X2_43) != iProver_top ),
% 3.58/0.99      inference(superposition,[status(thm)],[c_944,c_1497]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_9,plain,
% 3.58/0.99      ( ~ v5_relat_1(X0,X1)
% 3.58/0.99      | v5_relat_1(X2,X1)
% 3.58/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
% 3.58/0.99      | ~ v1_relat_1(X0) ),
% 3.58/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_436,plain,
% 3.58/0.99      ( ~ v5_relat_1(X0_43,X1_43)
% 3.58/0.99      | v5_relat_1(X2_43,X1_43)
% 3.58/0.99      | ~ m1_subset_1(X2_43,k1_zfmisc_1(X0_43))
% 3.58/0.99      | ~ v1_relat_1(X0_43) ),
% 3.58/0.99      inference(subtyping,[status(esa)],[c_9]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_949,plain,
% 3.58/0.99      ( v5_relat_1(X0_43,X1_43) != iProver_top
% 3.58/0.99      | v5_relat_1(X2_43,X1_43) = iProver_top
% 3.58/0.99      | m1_subset_1(X2_43,k1_zfmisc_1(X0_43)) != iProver_top
% 3.58/0.99      | v1_relat_1(X0_43) != iProver_top ),
% 3.58/0.99      inference(predicate_to_equality,[status(thm)],[c_436]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_4319,plain,
% 3.58/0.99      ( v5_relat_1(k2_zfmisc_1(sK0,sK1),X0_43) != iProver_top
% 3.58/0.99      | v5_relat_1(sK2,X0_43) = iProver_top
% 3.58/0.99      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top ),
% 3.58/0.99      inference(superposition,[status(thm)],[c_959,c_949]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_1426,plain,
% 3.58/0.99      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 3.58/0.99      inference(instantiation,[status(thm)],[c_430]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_1427,plain,
% 3.58/0.99      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 3.58/0.99      inference(predicate_to_equality,[status(thm)],[c_1426]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_4932,plain,
% 3.58/0.99      ( v5_relat_1(sK2,X0_43) = iProver_top
% 3.58/0.99      | v5_relat_1(k2_zfmisc_1(sK0,sK1),X0_43) != iProver_top ),
% 3.58/0.99      inference(global_propositional_subsumption,[status(thm)],[c_4319,c_1427]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_4933,plain,
% 3.58/0.99      ( v5_relat_1(k2_zfmisc_1(sK0,sK1),X0_43) != iProver_top
% 3.58/0.99      | v5_relat_1(sK2,X0_43) = iProver_top ),
% 3.58/0.99      inference(renaming,[status(thm)],[c_4932]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_4941,plain,
% 3.58/0.99      ( v5_relat_1(sK2,X0_43) = iProver_top
% 3.58/0.99      | r1_tarski(sK1,X0_43) != iProver_top ),
% 3.58/0.99      inference(superposition,[status(thm)],[c_2196,c_4933]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_5447,plain,
% 3.58/0.99      ( v5_relat_1(sK2,k3_tarski(k2_enumset1(X0_43,X0_43,X0_43,sK1))) = iProver_top ),
% 3.58/0.99      inference(superposition,[status(thm)],[c_1222,c_4941]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_5456,plain,
% 3.58/0.99      ( v5_relat_1(sK2,k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1))) = iProver_top ),
% 3.58/0.99      inference(instantiation,[status(thm)],[c_5447]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_10577,plain,
% 3.58/0.99      ( v4_relat_1(sK2,k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1))) != iProver_top ),
% 3.58/0.99      inference(global_propositional_subsumption,
% 3.58/0.99                [status(thm)],
% 3.58/0.99                [c_10514,c_5456]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_4,plain,
% 3.58/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
% 3.58/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_440,plain,
% 3.58/0.99      ( ~ r1_tarski(X0_43,X1_43)
% 3.58/0.99      | r1_tarski(k2_zfmisc_1(X0_43,X2_43),k2_zfmisc_1(X1_43,X2_43)) ),
% 3.58/0.99      inference(subtyping,[status(esa)],[c_4]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_945,plain,
% 3.58/0.99      ( r1_tarski(X0_43,X1_43) != iProver_top
% 3.58/0.99      | r1_tarski(k2_zfmisc_1(X0_43,X2_43),k2_zfmisc_1(X1_43,X2_43)) = iProver_top ),
% 3.58/0.99      inference(predicate_to_equality,[status(thm)],[c_440]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_17,plain,
% 3.58/0.99      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.58/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_428,plain,
% 3.58/0.99      ( v4_relat_1(X0_43,X1_43)
% 3.58/0.99      | ~ m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X1_43,X2_43))) ),
% 3.58/0.99      inference(subtyping,[status(esa)],[c_17]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_957,plain,
% 3.58/0.99      ( v4_relat_1(X0_43,X1_43) = iProver_top
% 3.58/0.99      | m1_subset_1(X0_43,k1_zfmisc_1(k2_zfmisc_1(X1_43,X2_43))) != iProver_top ),
% 3.58/0.99      inference(predicate_to_equality,[status(thm)],[c_428]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_1629,plain,
% 3.58/0.99      ( v4_relat_1(X0_43,X1_43) = iProver_top
% 3.58/0.99      | r1_tarski(X0_43,k2_zfmisc_1(X1_43,X2_43)) != iProver_top ),
% 3.58/0.99      inference(superposition,[status(thm)],[c_946,c_957]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_2223,plain,
% 3.58/0.99      ( v4_relat_1(k2_zfmisc_1(X0_43,X1_43),X2_43) = iProver_top
% 3.58/0.99      | r1_tarski(X0_43,X2_43) != iProver_top ),
% 3.58/0.99      inference(superposition,[status(thm)],[c_945,c_1629]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_8,plain,
% 3.58/0.99      ( ~ v4_relat_1(X0,X1)
% 3.58/0.99      | v4_relat_1(X2,X1)
% 3.58/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
% 3.58/0.99      | ~ v1_relat_1(X0) ),
% 3.58/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_437,plain,
% 3.58/0.99      ( ~ v4_relat_1(X0_43,X1_43)
% 3.58/0.99      | v4_relat_1(X2_43,X1_43)
% 3.58/0.99      | ~ m1_subset_1(X2_43,k1_zfmisc_1(X0_43))
% 3.58/0.99      | ~ v1_relat_1(X0_43) ),
% 3.58/0.99      inference(subtyping,[status(esa)],[c_8]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_948,plain,
% 3.58/0.99      ( v4_relat_1(X0_43,X1_43) != iProver_top
% 3.58/0.99      | v4_relat_1(X2_43,X1_43) = iProver_top
% 3.58/0.99      | m1_subset_1(X2_43,k1_zfmisc_1(X0_43)) != iProver_top
% 3.58/0.99      | v1_relat_1(X0_43) != iProver_top ),
% 3.58/0.99      inference(predicate_to_equality,[status(thm)],[c_437]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_2709,plain,
% 3.58/0.99      ( v4_relat_1(k2_zfmisc_1(sK0,sK1),X0_43) != iProver_top
% 3.58/0.99      | v4_relat_1(sK2,X0_43) = iProver_top
% 3.58/0.99      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top ),
% 3.58/0.99      inference(superposition,[status(thm)],[c_959,c_948]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_3550,plain,
% 3.58/0.99      ( v4_relat_1(sK2,X0_43) = iProver_top
% 3.58/0.99      | v4_relat_1(k2_zfmisc_1(sK0,sK1),X0_43) != iProver_top ),
% 3.58/0.99      inference(global_propositional_subsumption,[status(thm)],[c_2709,c_1427]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_3551,plain,
% 3.58/0.99      ( v4_relat_1(k2_zfmisc_1(sK0,sK1),X0_43) != iProver_top
% 3.58/0.99      | v4_relat_1(sK2,X0_43) = iProver_top ),
% 3.58/0.99      inference(renaming,[status(thm)],[c_3550]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_3556,plain,
% 3.58/0.99      ( v4_relat_1(sK2,X0_43) = iProver_top
% 3.58/0.99      | r1_tarski(sK0,X0_43) != iProver_top ),
% 3.58/0.99      inference(superposition,[status(thm)],[c_2223,c_3551]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_3561,plain,
% 3.58/0.99      ( v4_relat_1(sK2,k3_tarski(k2_enumset1(sK0,sK0,sK0,X0_43))) = iProver_top ),
% 3.58/0.99      inference(superposition,[status(thm)],[c_942,c_3556]) ).
% 3.58/0.99  
% 3.58/0.99  cnf(c_10582,plain,
% 3.58/0.99      ( $false ),
% 3.58/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_10577,c_3561]) ).
% 3.58/0.99  
% 3.58/0.99  
% 3.58/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.58/0.99  
% 3.58/0.99  ------                               Statistics
% 3.58/0.99  
% 3.58/0.99  ------ Selected
% 3.58/0.99  
% 3.58/0.99  total_time:                             0.352
% 3.58/0.99  
%------------------------------------------------------------------------------
