%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:44:06 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :  177 ( 402 expanded)
%              Number of clauses        :  119 ( 217 expanded)
%              Number of leaves         :   22 (  73 expanded)
%              Depth                    :   18
%              Number of atoms          :  394 ( 906 expanded)
%              Number of equality atoms :  212 ( 442 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f39,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f18,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f34,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f36,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f36])).

fof(f57,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f17,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f17])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f55,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f17])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f47,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f48,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k6_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k6_subset_1(X0,X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k6_subset_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
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
    inference(cnf_transformation,[],[f35])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f21])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f59,plain,(
    ! [X0,X1] : r1_xboole_0(k6_subset_1(X0,X1),X1) ),
    inference(definition_unfolding,[],[f42,f44])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f51,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f58,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_538,plain,
    ( ~ v1_xboole_0(X0_41)
    | k1_xboole_0 = X0_41 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_876,plain,
    ( ~ v1_xboole_0(k5_relat_1(X0_41,X1_41))
    | k1_xboole_0 = k5_relat_1(X0_41,X1_41) ),
    inference(instantiation,[status(thm)],[c_538])).

cnf(c_3655,plain,
    ( ~ v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))
    | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    inference(instantiation,[status(thm)],[c_876])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_534,plain,
    ( ~ v1_relat_1(X0_41)
    | ~ v1_relat_1(X1_41)
    | v1_relat_1(k5_relat_1(X0_41,X1_41)) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_810,plain,
    ( v1_relat_1(X0_41) != iProver_top
    | v1_relat_1(X1_41) != iProver_top
    | v1_relat_1(k5_relat_1(X1_41,X0_41)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_534])).

cnf(c_19,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_525,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_816,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_525])).

cnf(c_2,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_537,plain,
    ( r1_tarski(k1_xboole_0,X0_41) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_807,plain,
    ( r1_tarski(k1_xboole_0,X0_41) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_537])).

cnf(c_16,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_528,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_14,plain,
    ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_530,plain,
    ( ~ r1_tarski(k2_relat_1(X0_41),k1_relat_1(X1_41))
    | ~ v1_relat_1(X0_41)
    | ~ v1_relat_1(X1_41)
    | k1_relat_1(k5_relat_1(X0_41,X1_41)) = k1_relat_1(X0_41) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_814,plain,
    ( k1_relat_1(k5_relat_1(X0_41,X1_41)) = k1_relat_1(X0_41)
    | r1_tarski(k2_relat_1(X0_41),k1_relat_1(X1_41)) != iProver_top
    | v1_relat_1(X1_41) != iProver_top
    | v1_relat_1(X0_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_530])).

cnf(c_1614,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0_41)) = k1_relat_1(k1_xboole_0)
    | r1_tarski(k1_xboole_0,k1_relat_1(X0_41)) != iProver_top
    | v1_relat_1(X0_41) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_528,c_814])).

cnf(c_17,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_527,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1616,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0_41)) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k1_relat_1(X0_41)) != iProver_top
    | v1_relat_1(X0_41) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1614,c_527])).

cnf(c_8,plain,
    ( v1_relat_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_42,plain,
    ( v1_relat_1(X0) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_44,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_42])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_66,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1624,plain,
    ( v1_relat_1(X0_41) != iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(X0_41)) != iProver_top
    | k1_relat_1(k5_relat_1(k1_xboole_0,X0_41)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1616,c_44,c_66])).

cnf(c_1625,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0_41)) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k1_relat_1(X0_41)) != iProver_top
    | v1_relat_1(X0_41) != iProver_top ),
    inference(renaming,[status(thm)],[c_1624])).

cnf(c_1628,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0_41)) = k1_xboole_0
    | v1_relat_1(X0_41) != iProver_top ),
    inference(superposition,[status(thm)],[c_807,c_1625])).

cnf(c_2299,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_816,c_1628])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_533,plain,
    ( ~ v1_relat_1(X0_41)
    | v1_xboole_0(X0_41)
    | ~ v1_xboole_0(k1_relat_1(X0_41)) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_811,plain,
    ( v1_relat_1(X0_41) != iProver_top
    | v1_xboole_0(X0_41) = iProver_top
    | v1_xboole_0(k1_relat_1(X0_41)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_533])).

cnf(c_2312,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) != iProver_top
    | v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2299,c_811])).

cnf(c_3234,plain,
    ( v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) = iProver_top
    | v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2312,c_66])).

cnf(c_3235,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) != iProver_top
    | v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_3234])).

cnf(c_3238,plain,
    ( v1_relat_1(sK0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top
    | v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_810,c_3235])).

cnf(c_3239,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_xboole_0)
    | v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3238])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k4_relat_1(X0)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_535,plain,
    ( ~ v1_relat_1(X0_41)
    | v1_relat_1(k4_relat_1(X0_41)) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_809,plain,
    ( v1_relat_1(X0_41) != iProver_top
    | v1_relat_1(k4_relat_1(X0_41)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_535])).

cnf(c_2301,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(X0_41))) = k1_xboole_0
    | v1_relat_1(X0_41) != iProver_top ),
    inference(superposition,[status(thm)],[c_809,c_1628])).

cnf(c_2893,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_816,c_2301])).

cnf(c_539,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_805,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_539])).

cnf(c_536,plain,
    ( v1_relat_1(X0_41)
    | ~ v1_xboole_0(X0_41) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_808,plain,
    ( v1_relat_1(X0_41) = iProver_top
    | v1_xboole_0(X0_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_536])).

cnf(c_1044,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_805,c_808])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_529,plain,
    ( ~ v1_relat_1(X0_41)
    | ~ v1_relat_1(X1_41)
    | k5_relat_1(k4_relat_1(X1_41),k4_relat_1(X0_41)) = k4_relat_1(k5_relat_1(X0_41,X1_41)) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_815,plain,
    ( k5_relat_1(k4_relat_1(X0_41),k4_relat_1(X1_41)) = k4_relat_1(k5_relat_1(X1_41,X0_41))
    | v1_relat_1(X0_41) != iProver_top
    | v1_relat_1(X1_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_529])).

cnf(c_1526,plain,
    ( k5_relat_1(k4_relat_1(X0_41),k4_relat_1(sK0)) = k4_relat_1(k5_relat_1(sK0,X0_41))
    | v1_relat_1(X0_41) != iProver_top ),
    inference(superposition,[status(thm)],[c_816,c_815])).

cnf(c_1808,plain,
    ( k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(sK0)) = k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_1044,c_1526])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k6_subset_1(X0,X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_531,plain,
    ( ~ v1_relat_1(X0_41)
    | ~ v1_relat_1(X1_41)
    | k6_subset_1(k4_relat_1(X0_41),k4_relat_1(X1_41)) = k4_relat_1(k6_subset_1(X0_41,X1_41)) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_813,plain,
    ( k6_subset_1(k4_relat_1(X0_41),k4_relat_1(X1_41)) = k4_relat_1(k6_subset_1(X0_41,X1_41))
    | v1_relat_1(X1_41) != iProver_top
    | v1_relat_1(X0_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_531])).

cnf(c_1510,plain,
    ( k6_subset_1(k4_relat_1(X0_41),k4_relat_1(sK0)) = k4_relat_1(k6_subset_1(X0_41,sK0))
    | v1_relat_1(X0_41) != iProver_top ),
    inference(superposition,[status(thm)],[c_816,c_813])).

cnf(c_1699,plain,
    ( k6_subset_1(k4_relat_1(sK0),k4_relat_1(sK0)) = k4_relat_1(k6_subset_1(sK0,sK0)) ),
    inference(superposition,[status(thm)],[c_816,c_1510])).

cnf(c_5,plain,
    ( m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_141,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_142,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_141])).

cnf(c_255,plain,
    ( r1_tarski(X0,X1)
    | k6_subset_1(X2,X3) != X0
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X2) ),
    inference(resolution_lifted,[status(thm)],[c_5,c_142])).

cnf(c_256,plain,
    ( r1_tarski(k6_subset_1(X0,X1),X2)
    | k1_zfmisc_1(X2) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_255])).

cnf(c_523,plain,
    ( r1_tarski(k6_subset_1(X0_41,X1_41),X2_41)
    | k1_zfmisc_1(X2_41) != k1_zfmisc_1(X0_41) ),
    inference(subtyping,[status(esa)],[c_256])).

cnf(c_818,plain,
    ( k1_zfmisc_1(X0_41) != k1_zfmisc_1(X1_41)
    | r1_tarski(k6_subset_1(X1_41,X2_41),X0_41) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_523])).

cnf(c_1359,plain,
    ( r1_tarski(k6_subset_1(X0_41,X1_41),X0_41) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_818])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_4,plain,
    ( r1_xboole_0(k6_subset_1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_239,plain,
    ( ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0)
    | X2 != X1
    | k6_subset_1(X3,X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_4])).

cnf(c_240,plain,
    ( ~ r1_tarski(k6_subset_1(X0,X1),X1)
    | v1_xboole_0(k6_subset_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_239])).

cnf(c_524,plain,
    ( ~ r1_tarski(k6_subset_1(X0_41,X1_41),X1_41)
    | v1_xboole_0(k6_subset_1(X0_41,X1_41)) ),
    inference(subtyping,[status(esa)],[c_240])).

cnf(c_817,plain,
    ( r1_tarski(k6_subset_1(X0_41,X1_41),X1_41) != iProver_top
    | v1_xboole_0(k6_subset_1(X0_41,X1_41)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_524])).

cnf(c_1436,plain,
    ( v1_xboole_0(k6_subset_1(X0_41,X0_41)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1359,c_817])).

cnf(c_806,plain,
    ( k1_xboole_0 = X0_41
    | v1_xboole_0(X0_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_538])).

cnf(c_1442,plain,
    ( k6_subset_1(X0_41,X0_41) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1436,c_806])).

cnf(c_1703,plain,
    ( k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1699,c_1442])).

cnf(c_1811,plain,
    ( k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) = k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(light_normalisation,[status(thm)],[c_1808,c_1703])).

cnf(c_2900,plain,
    ( k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2893,c_1811])).

cnf(c_3088,plain,
    ( v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) != iProver_top
    | v1_xboole_0(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2900,c_811])).

cnf(c_1006,plain,
    ( ~ v1_xboole_0(k4_relat_1(k5_relat_1(X0_41,X1_41)))
    | k1_xboole_0 = k4_relat_1(k5_relat_1(X0_41,X1_41)) ),
    inference(instantiation,[status(thm)],[c_538])).

cnf(c_2980,plain,
    ( ~ v1_xboole_0(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | k1_xboole_0 = k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_1006])).

cnf(c_2981,plain,
    ( k1_xboole_0 = k4_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | v1_xboole_0(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2980])).

cnf(c_543,plain,
    ( X0_41 != X1_41
    | X2_41 != X1_41
    | X2_41 = X0_41 ),
    theory(equality)).

cnf(c_1234,plain,
    ( X0_41 != X1_41
    | k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) != X1_41
    | k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = X0_41 ),
    inference(instantiation,[status(thm)],[c_543])).

cnf(c_1367,plain,
    ( X0_41 != k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = X0_41
    | k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) != k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_1234])).

cnf(c_2282,plain,
    ( k4_relat_1(X0_41) != k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = k4_relat_1(X0_41)
    | k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) != k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_1367])).

cnf(c_2283,plain,
    ( k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) != k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = k4_relat_1(k1_xboole_0)
    | k4_relat_1(k1_xboole_0) != k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_2282])).

cnf(c_1364,plain,
    ( X0_41 != k5_relat_1(sK0,k1_xboole_0)
    | k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = X0_41
    | k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) != k5_relat_1(sK0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1234])).

cnf(c_2108,plain,
    ( k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) != k5_relat_1(sK0,k1_xboole_0)
    | k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_1364])).

cnf(c_1387,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_535])).

cnf(c_1388,plain,
    ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) != iProver_top
    | v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1387])).

cnf(c_549,plain,
    ( X0_41 != X1_41
    | k4_relat_1(X0_41) = k4_relat_1(X1_41) ),
    theory(equality)).

cnf(c_1356,plain,
    ( X0_41 != k4_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | k4_relat_1(X0_41) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_549])).

cnf(c_1357,plain,
    ( k4_relat_1(k1_xboole_0) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | k1_xboole_0 != k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_1356])).

cnf(c_1351,plain,
    ( k4_relat_1(X0_41) != X1_41
    | k1_xboole_0 != X1_41
    | k1_xboole_0 = k4_relat_1(X0_41) ),
    inference(instantiation,[status(thm)],[c_543])).

cnf(c_1352,plain,
    ( k4_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k4_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1351])).

cnf(c_1070,plain,
    ( k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) != X0_41
    | k1_xboole_0 != X0_41
    | k1_xboole_0 = k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_543])).

cnf(c_1235,plain,
    ( k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) != k4_relat_1(X0_41)
    | k1_xboole_0 != k4_relat_1(X0_41)
    | k1_xboole_0 = k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_1070])).

cnf(c_1236,plain,
    ( k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) != k4_relat_1(k1_xboole_0)
    | k1_xboole_0 = k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | k1_xboole_0 != k4_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1235])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | k4_relat_1(k4_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_532,plain,
    ( ~ v1_relat_1(X0_41)
    | k4_relat_1(k4_relat_1(X0_41)) = X0_41 ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1081,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = k5_relat_1(sK0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_532])).

cnf(c_837,plain,
    ( k5_relat_1(sK0,k1_xboole_0) != X0_41
    | k1_xboole_0 != X0_41
    | k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_543])).

cnf(c_1021,plain,
    ( k5_relat_1(sK0,k1_xboole_0) != k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
    inference(instantiation,[status(thm)],[c_837])).

cnf(c_850,plain,
    ( X0_41 != X1_41
    | k5_relat_1(sK0,k1_xboole_0) != X1_41
    | k5_relat_1(sK0,k1_xboole_0) = X0_41 ),
    inference(instantiation,[status(thm)],[c_543])).

cnf(c_871,plain,
    ( X0_41 != k5_relat_1(sK0,k1_xboole_0)
    | k5_relat_1(sK0,k1_xboole_0) = X0_41
    | k5_relat_1(sK0,k1_xboole_0) != k5_relat_1(sK0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_850])).

cnf(c_944,plain,
    ( k5_relat_1(sK0,k1_xboole_0) != k5_relat_1(sK0,k1_xboole_0)
    | k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
    | k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) != k5_relat_1(sK0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_871])).

cnf(c_541,plain,
    ( X0_41 = X0_41 ),
    theory(equality)).

cnf(c_892,plain,
    ( k5_relat_1(sK0,k1_xboole_0) = k5_relat_1(sK0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_541])).

cnf(c_861,plain,
    ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_534])).

cnf(c_862,plain,
    ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) = iProver_top
    | v1_relat_1(sK0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_861])).

cnf(c_18,negated_conjecture,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_526,negated_conjecture,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_562,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_541])).

cnf(c_43,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_20,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3655,c_3239,c_3088,c_2981,c_2283,c_2108,c_1703,c_1388,c_1357,c_1352,c_1236,c_1081,c_1021,c_944,c_892,c_862,c_861,c_526,c_562,c_66,c_0,c_44,c_43,c_20,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:55:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.21/1.06  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.06  
% 2.21/1.06  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.21/1.06  
% 2.21/1.06  ------  iProver source info
% 2.21/1.06  
% 2.21/1.06  git: date: 2020-06-30 10:37:57 +0100
% 2.21/1.06  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.21/1.06  git: non_committed_changes: false
% 2.21/1.06  git: last_make_outside_of_git: false
% 2.21/1.06  
% 2.21/1.06  ------ 
% 2.21/1.06  
% 2.21/1.06  ------ Input Options
% 2.21/1.06  
% 2.21/1.06  --out_options                           all
% 2.21/1.06  --tptp_safe_out                         true
% 2.21/1.06  --problem_path                          ""
% 2.21/1.06  --include_path                          ""
% 2.21/1.06  --clausifier                            res/vclausify_rel
% 2.21/1.06  --clausifier_options                    ""
% 2.21/1.06  --stdin                                 false
% 2.21/1.06  --stats_out                             all
% 2.21/1.06  
% 2.21/1.06  ------ General Options
% 2.21/1.06  
% 2.21/1.06  --fof                                   false
% 2.21/1.06  --time_out_real                         305.
% 2.21/1.06  --time_out_virtual                      -1.
% 2.21/1.06  --symbol_type_check                     false
% 2.21/1.06  --clausify_out                          false
% 2.21/1.06  --sig_cnt_out                           false
% 2.21/1.06  --trig_cnt_out                          false
% 2.21/1.06  --trig_cnt_out_tolerance                1.
% 2.21/1.06  --trig_cnt_out_sk_spl                   false
% 2.21/1.06  --abstr_cl_out                          false
% 2.21/1.06  
% 2.21/1.06  ------ Global Options
% 2.21/1.06  
% 2.21/1.06  --schedule                              default
% 2.21/1.06  --add_important_lit                     false
% 2.21/1.06  --prop_solver_per_cl                    1000
% 2.21/1.06  --min_unsat_core                        false
% 2.21/1.06  --soft_assumptions                      false
% 2.21/1.06  --soft_lemma_size                       3
% 2.21/1.06  --prop_impl_unit_size                   0
% 2.21/1.06  --prop_impl_unit                        []
% 2.21/1.06  --share_sel_clauses                     true
% 2.21/1.06  --reset_solvers                         false
% 2.21/1.06  --bc_imp_inh                            [conj_cone]
% 2.21/1.06  --conj_cone_tolerance                   3.
% 2.21/1.06  --extra_neg_conj                        none
% 2.21/1.06  --large_theory_mode                     true
% 2.21/1.06  --prolific_symb_bound                   200
% 2.21/1.06  --lt_threshold                          2000
% 2.21/1.06  --clause_weak_htbl                      true
% 2.21/1.06  --gc_record_bc_elim                     false
% 2.21/1.06  
% 2.21/1.06  ------ Preprocessing Options
% 2.21/1.06  
% 2.21/1.06  --preprocessing_flag                    true
% 2.21/1.06  --time_out_prep_mult                    0.1
% 2.21/1.06  --splitting_mode                        input
% 2.21/1.06  --splitting_grd                         true
% 2.21/1.06  --splitting_cvd                         false
% 2.21/1.06  --splitting_cvd_svl                     false
% 2.21/1.06  --splitting_nvd                         32
% 2.21/1.06  --sub_typing                            true
% 2.21/1.06  --prep_gs_sim                           true
% 2.21/1.06  --prep_unflatten                        true
% 2.21/1.06  --prep_res_sim                          true
% 2.21/1.06  --prep_upred                            true
% 2.21/1.06  --prep_sem_filter                       exhaustive
% 2.21/1.06  --prep_sem_filter_out                   false
% 2.21/1.06  --pred_elim                             true
% 2.21/1.06  --res_sim_input                         true
% 2.21/1.06  --eq_ax_congr_red                       true
% 2.21/1.06  --pure_diseq_elim                       true
% 2.21/1.06  --brand_transform                       false
% 2.21/1.06  --non_eq_to_eq                          false
% 2.21/1.06  --prep_def_merge                        true
% 2.21/1.06  --prep_def_merge_prop_impl              false
% 2.21/1.06  --prep_def_merge_mbd                    true
% 2.21/1.06  --prep_def_merge_tr_red                 false
% 2.21/1.06  --prep_def_merge_tr_cl                  false
% 2.21/1.06  --smt_preprocessing                     true
% 2.21/1.06  --smt_ac_axioms                         fast
% 2.21/1.06  --preprocessed_out                      false
% 2.21/1.06  --preprocessed_stats                    false
% 2.21/1.06  
% 2.21/1.06  ------ Abstraction refinement Options
% 2.21/1.06  
% 2.21/1.06  --abstr_ref                             []
% 2.21/1.06  --abstr_ref_prep                        false
% 2.21/1.06  --abstr_ref_until_sat                   false
% 2.21/1.06  --abstr_ref_sig_restrict                funpre
% 2.21/1.06  --abstr_ref_af_restrict_to_split_sk     false
% 2.21/1.06  --abstr_ref_under                       []
% 2.21/1.06  
% 2.21/1.06  ------ SAT Options
% 2.21/1.06  
% 2.21/1.06  --sat_mode                              false
% 2.21/1.06  --sat_fm_restart_options                ""
% 2.21/1.06  --sat_gr_def                            false
% 2.21/1.06  --sat_epr_types                         true
% 2.21/1.06  --sat_non_cyclic_types                  false
% 2.21/1.06  --sat_finite_models                     false
% 2.21/1.06  --sat_fm_lemmas                         false
% 2.21/1.06  --sat_fm_prep                           false
% 2.21/1.06  --sat_fm_uc_incr                        true
% 2.21/1.06  --sat_out_model                         small
% 2.21/1.06  --sat_out_clauses                       false
% 2.21/1.06  
% 2.21/1.06  ------ QBF Options
% 2.21/1.06  
% 2.21/1.06  --qbf_mode                              false
% 2.21/1.06  --qbf_elim_univ                         false
% 2.21/1.06  --qbf_dom_inst                          none
% 2.21/1.06  --qbf_dom_pre_inst                      false
% 2.21/1.06  --qbf_sk_in                             false
% 2.21/1.06  --qbf_pred_elim                         true
% 2.21/1.06  --qbf_split                             512
% 2.21/1.06  
% 2.21/1.06  ------ BMC1 Options
% 2.21/1.06  
% 2.21/1.06  --bmc1_incremental                      false
% 2.21/1.06  --bmc1_axioms                           reachable_all
% 2.21/1.06  --bmc1_min_bound                        0
% 2.21/1.06  --bmc1_max_bound                        -1
% 2.21/1.06  --bmc1_max_bound_default                -1
% 2.21/1.06  --bmc1_symbol_reachability              true
% 2.21/1.06  --bmc1_property_lemmas                  false
% 2.21/1.06  --bmc1_k_induction                      false
% 2.21/1.06  --bmc1_non_equiv_states                 false
% 2.21/1.06  --bmc1_deadlock                         false
% 2.21/1.06  --bmc1_ucm                              false
% 2.21/1.06  --bmc1_add_unsat_core                   none
% 2.21/1.06  --bmc1_unsat_core_children              false
% 2.21/1.06  --bmc1_unsat_core_extrapolate_axioms    false
% 2.21/1.06  --bmc1_out_stat                         full
% 2.21/1.06  --bmc1_ground_init                      false
% 2.21/1.06  --bmc1_pre_inst_next_state              false
% 2.21/1.06  --bmc1_pre_inst_state                   false
% 2.21/1.06  --bmc1_pre_inst_reach_state             false
% 2.21/1.06  --bmc1_out_unsat_core                   false
% 2.21/1.06  --bmc1_aig_witness_out                  false
% 2.21/1.06  --bmc1_verbose                          false
% 2.21/1.06  --bmc1_dump_clauses_tptp                false
% 2.21/1.06  --bmc1_dump_unsat_core_tptp             false
% 2.21/1.06  --bmc1_dump_file                        -
% 2.21/1.06  --bmc1_ucm_expand_uc_limit              128
% 2.21/1.06  --bmc1_ucm_n_expand_iterations          6
% 2.21/1.06  --bmc1_ucm_extend_mode                  1
% 2.21/1.06  --bmc1_ucm_init_mode                    2
% 2.21/1.06  --bmc1_ucm_cone_mode                    none
% 2.21/1.06  --bmc1_ucm_reduced_relation_type        0
% 2.21/1.06  --bmc1_ucm_relax_model                  4
% 2.21/1.06  --bmc1_ucm_full_tr_after_sat            true
% 2.21/1.06  --bmc1_ucm_expand_neg_assumptions       false
% 2.21/1.06  --bmc1_ucm_layered_model                none
% 2.21/1.06  --bmc1_ucm_max_lemma_size               10
% 2.21/1.06  
% 2.21/1.06  ------ AIG Options
% 2.21/1.06  
% 2.21/1.06  --aig_mode                              false
% 2.21/1.06  
% 2.21/1.06  ------ Instantiation Options
% 2.21/1.06  
% 2.21/1.06  --instantiation_flag                    true
% 2.21/1.06  --inst_sos_flag                         true
% 2.21/1.06  --inst_sos_phase                        true
% 2.21/1.06  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.21/1.06  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.21/1.06  --inst_lit_sel_side                     num_symb
% 2.21/1.06  --inst_solver_per_active                1400
% 2.21/1.06  --inst_solver_calls_frac                1.
% 2.21/1.06  --inst_passive_queue_type               priority_queues
% 2.21/1.06  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.21/1.06  --inst_passive_queues_freq              [25;2]
% 2.21/1.06  --inst_dismatching                      true
% 2.21/1.06  --inst_eager_unprocessed_to_passive     true
% 2.21/1.06  --inst_prop_sim_given                   true
% 2.21/1.06  --inst_prop_sim_new                     false
% 2.21/1.06  --inst_subs_new                         false
% 2.21/1.06  --inst_eq_res_simp                      false
% 2.21/1.06  --inst_subs_given                       false
% 2.21/1.06  --inst_orphan_elimination               true
% 2.21/1.06  --inst_learning_loop_flag               true
% 2.21/1.06  --inst_learning_start                   3000
% 2.21/1.06  --inst_learning_factor                  2
% 2.21/1.06  --inst_start_prop_sim_after_learn       3
% 2.21/1.06  --inst_sel_renew                        solver
% 2.21/1.06  --inst_lit_activity_flag                true
% 2.21/1.06  --inst_restr_to_given                   false
% 2.21/1.06  --inst_activity_threshold               500
% 2.21/1.06  --inst_out_proof                        true
% 2.21/1.06  
% 2.21/1.06  ------ Resolution Options
% 2.21/1.06  
% 2.21/1.06  --resolution_flag                       true
% 2.21/1.06  --res_lit_sel                           adaptive
% 2.21/1.06  --res_lit_sel_side                      none
% 2.21/1.06  --res_ordering                          kbo
% 2.21/1.06  --res_to_prop_solver                    active
% 2.21/1.06  --res_prop_simpl_new                    false
% 2.21/1.06  --res_prop_simpl_given                  true
% 2.21/1.06  --res_passive_queue_type                priority_queues
% 2.21/1.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.21/1.06  --res_passive_queues_freq               [15;5]
% 2.21/1.06  --res_forward_subs                      full
% 2.21/1.06  --res_backward_subs                     full
% 2.21/1.06  --res_forward_subs_resolution           true
% 2.21/1.06  --res_backward_subs_resolution          true
% 2.21/1.06  --res_orphan_elimination                true
% 2.21/1.06  --res_time_limit                        2.
% 2.21/1.06  --res_out_proof                         true
% 2.21/1.06  
% 2.21/1.06  ------ Superposition Options
% 2.21/1.06  
% 2.21/1.06  --superposition_flag                    true
% 2.21/1.06  --sup_passive_queue_type                priority_queues
% 2.21/1.06  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.21/1.06  --sup_passive_queues_freq               [8;1;4]
% 2.21/1.06  --demod_completeness_check              fast
% 2.21/1.06  --demod_use_ground                      true
% 2.21/1.06  --sup_to_prop_solver                    passive
% 2.21/1.06  --sup_prop_simpl_new                    true
% 2.21/1.06  --sup_prop_simpl_given                  true
% 2.21/1.06  --sup_fun_splitting                     true
% 2.21/1.06  --sup_smt_interval                      50000
% 2.21/1.06  
% 2.21/1.06  ------ Superposition Simplification Setup
% 2.21/1.06  
% 2.21/1.06  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 2.21/1.06  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 2.21/1.06  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 2.21/1.06  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 2.21/1.06  --sup_full_triv                         [TrivRules;PropSubs]
% 2.21/1.06  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 2.21/1.06  --sup_full_bw                           [BwDemod;BwSubsumption]
% 2.21/1.06  --sup_immed_triv                        [TrivRules]
% 2.21/1.06  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.21/1.06  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 2.21/1.06  --sup_immed_bw_main                     []
% 2.21/1.06  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 2.21/1.06  --sup_input_triv                        [Unflattening;TrivRules]
% 2.21/1.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 2.21/1.06  --sup_input_bw                          []
% 2.21/1.06  
% 2.21/1.06  ------ Combination Options
% 2.21/1.06  
% 2.21/1.06  --comb_res_mult                         3
% 2.21/1.06  --comb_sup_mult                         2
% 2.21/1.06  --comb_inst_mult                        10
% 2.21/1.06  
% 2.21/1.06  ------ Debug Options
% 2.21/1.06  
% 2.21/1.06  --dbg_backtrace                         false
% 2.21/1.06  --dbg_dump_prop_clauses                 false
% 2.21/1.06  --dbg_dump_prop_clauses_file            -
% 2.21/1.06  --dbg_out_stat                          false
% 2.21/1.06  ------ Parsing...
% 2.21/1.06  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.21/1.06  
% 2.21/1.06  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.21/1.06  
% 2.21/1.06  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.21/1.06  
% 2.21/1.06  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.21/1.06  ------ Proving...
% 2.21/1.06  ------ Problem Properties 
% 2.21/1.06  
% 2.21/1.06  
% 2.21/1.06  clauses                                 17
% 2.21/1.06  conjectures                             2
% 2.21/1.06  EPR                                     5
% 2.21/1.06  Horn                                    17
% 2.21/1.06  unary                                   5
% 2.21/1.06  binary                                  7
% 2.21/1.06  lits                                    35
% 2.21/1.06  lits eq                                 10
% 2.21/1.06  fd_pure                                 0
% 2.21/1.06  fd_pseudo                               0
% 2.21/1.06  fd_cond                                 1
% 2.21/1.06  fd_pseudo_cond                          0
% 2.21/1.06  AC symbols                              0
% 2.21/1.06  
% 2.21/1.06  ------ Schedule dynamic 5 is on 
% 2.21/1.06  
% 2.21/1.06  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.21/1.06  
% 2.21/1.06  
% 2.21/1.06  ------ 
% 2.21/1.06  Current options:
% 2.21/1.06  ------ 
% 2.21/1.06  
% 2.21/1.06  ------ Input Options
% 2.21/1.06  
% 2.21/1.06  --out_options                           all
% 2.21/1.06  --tptp_safe_out                         true
% 2.21/1.06  --problem_path                          ""
% 2.21/1.06  --include_path                          ""
% 2.21/1.06  --clausifier                            res/vclausify_rel
% 2.21/1.06  --clausifier_options                    ""
% 2.21/1.06  --stdin                                 false
% 2.21/1.06  --stats_out                             all
% 2.21/1.06  
% 2.21/1.06  ------ General Options
% 2.21/1.06  
% 2.21/1.06  --fof                                   false
% 2.21/1.06  --time_out_real                         305.
% 2.21/1.06  --time_out_virtual                      -1.
% 2.21/1.06  --symbol_type_check                     false
% 2.21/1.06  --clausify_out                          false
% 2.21/1.06  --sig_cnt_out                           false
% 2.21/1.06  --trig_cnt_out                          false
% 2.21/1.06  --trig_cnt_out_tolerance                1.
% 2.21/1.06  --trig_cnt_out_sk_spl                   false
% 2.21/1.06  --abstr_cl_out                          false
% 2.21/1.06  
% 2.21/1.06  ------ Global Options
% 2.21/1.06  
% 2.21/1.06  --schedule                              default
% 2.21/1.06  --add_important_lit                     false
% 2.21/1.06  --prop_solver_per_cl                    1000
% 2.21/1.06  --min_unsat_core                        false
% 2.21/1.06  --soft_assumptions                      false
% 2.21/1.06  --soft_lemma_size                       3
% 2.21/1.06  --prop_impl_unit_size                   0
% 2.21/1.06  --prop_impl_unit                        []
% 2.21/1.06  --share_sel_clauses                     true
% 2.21/1.06  --reset_solvers                         false
% 2.21/1.06  --bc_imp_inh                            [conj_cone]
% 2.21/1.06  --conj_cone_tolerance                   3.
% 2.21/1.06  --extra_neg_conj                        none
% 2.21/1.06  --large_theory_mode                     true
% 2.21/1.06  --prolific_symb_bound                   200
% 2.21/1.06  --lt_threshold                          2000
% 2.21/1.06  --clause_weak_htbl                      true
% 2.21/1.06  --gc_record_bc_elim                     false
% 2.21/1.06  
% 2.21/1.06  ------ Preprocessing Options
% 2.21/1.06  
% 2.21/1.06  --preprocessing_flag                    true
% 2.21/1.06  --time_out_prep_mult                    0.1
% 2.21/1.06  --splitting_mode                        input
% 2.21/1.06  --splitting_grd                         true
% 2.21/1.06  --splitting_cvd                         false
% 2.21/1.06  --splitting_cvd_svl                     false
% 2.21/1.06  --splitting_nvd                         32
% 2.21/1.06  --sub_typing                            true
% 2.21/1.06  --prep_gs_sim                           true
% 2.21/1.06  --prep_unflatten                        true
% 2.21/1.06  --prep_res_sim                          true
% 2.21/1.06  --prep_upred                            true
% 2.21/1.06  --prep_sem_filter                       exhaustive
% 2.21/1.06  --prep_sem_filter_out                   false
% 2.21/1.06  --pred_elim                             true
% 2.21/1.06  --res_sim_input                         true
% 2.21/1.06  --eq_ax_congr_red                       true
% 2.21/1.06  --pure_diseq_elim                       true
% 2.21/1.06  --brand_transform                       false
% 2.21/1.06  --non_eq_to_eq                          false
% 2.21/1.06  --prep_def_merge                        true
% 2.21/1.06  --prep_def_merge_prop_impl              false
% 2.21/1.06  --prep_def_merge_mbd                    true
% 2.21/1.06  --prep_def_merge_tr_red                 false
% 2.21/1.06  --prep_def_merge_tr_cl                  false
% 2.21/1.06  --smt_preprocessing                     true
% 2.21/1.06  --smt_ac_axioms                         fast
% 2.21/1.06  --preprocessed_out                      false
% 2.21/1.06  --preprocessed_stats                    false
% 2.21/1.06  
% 2.21/1.06  ------ Abstraction refinement Options
% 2.21/1.06  
% 2.21/1.06  --abstr_ref                             []
% 2.21/1.06  --abstr_ref_prep                        false
% 2.21/1.06  --abstr_ref_until_sat                   false
% 2.21/1.06  --abstr_ref_sig_restrict                funpre
% 2.21/1.06  --abstr_ref_af_restrict_to_split_sk     false
% 2.21/1.06  --abstr_ref_under                       []
% 2.21/1.06  
% 2.21/1.06  ------ SAT Options
% 2.21/1.06  
% 2.21/1.06  --sat_mode                              false
% 2.21/1.06  --sat_fm_restart_options                ""
% 2.21/1.06  --sat_gr_def                            false
% 2.21/1.06  --sat_epr_types                         true
% 2.21/1.06  --sat_non_cyclic_types                  false
% 2.21/1.06  --sat_finite_models                     false
% 2.21/1.06  --sat_fm_lemmas                         false
% 2.21/1.06  --sat_fm_prep                           false
% 2.21/1.06  --sat_fm_uc_incr                        true
% 2.21/1.06  --sat_out_model                         small
% 2.21/1.06  --sat_out_clauses                       false
% 2.21/1.06  
% 2.21/1.06  ------ QBF Options
% 2.21/1.06  
% 2.21/1.06  --qbf_mode                              false
% 2.21/1.06  --qbf_elim_univ                         false
% 2.21/1.06  --qbf_dom_inst                          none
% 2.21/1.06  --qbf_dom_pre_inst                      false
% 2.21/1.06  --qbf_sk_in                             false
% 2.21/1.06  --qbf_pred_elim                         true
% 2.21/1.06  --qbf_split                             512
% 2.21/1.06  
% 2.21/1.06  ------ BMC1 Options
% 2.21/1.06  
% 2.21/1.06  --bmc1_incremental                      false
% 2.21/1.06  --bmc1_axioms                           reachable_all
% 2.21/1.06  --bmc1_min_bound                        0
% 2.21/1.06  --bmc1_max_bound                        -1
% 2.21/1.06  --bmc1_max_bound_default                -1
% 2.21/1.06  --bmc1_symbol_reachability              true
% 2.21/1.06  --bmc1_property_lemmas                  false
% 2.21/1.06  --bmc1_k_induction                      false
% 2.21/1.06  --bmc1_non_equiv_states                 false
% 2.21/1.06  --bmc1_deadlock                         false
% 2.21/1.06  --bmc1_ucm                              false
% 2.21/1.06  --bmc1_add_unsat_core                   none
% 2.21/1.06  --bmc1_unsat_core_children              false
% 2.21/1.06  --bmc1_unsat_core_extrapolate_axioms    false
% 2.21/1.06  --bmc1_out_stat                         full
% 2.21/1.06  --bmc1_ground_init                      false
% 2.21/1.06  --bmc1_pre_inst_next_state              false
% 2.21/1.06  --bmc1_pre_inst_state                   false
% 2.21/1.06  --bmc1_pre_inst_reach_state             false
% 2.21/1.06  --bmc1_out_unsat_core                   false
% 2.21/1.06  --bmc1_aig_witness_out                  false
% 2.21/1.06  --bmc1_verbose                          false
% 2.21/1.06  --bmc1_dump_clauses_tptp                false
% 2.21/1.06  --bmc1_dump_unsat_core_tptp             false
% 2.21/1.06  --bmc1_dump_file                        -
% 2.21/1.06  --bmc1_ucm_expand_uc_limit              128
% 2.21/1.06  --bmc1_ucm_n_expand_iterations          6
% 2.21/1.06  --bmc1_ucm_extend_mode                  1
% 2.21/1.06  --bmc1_ucm_init_mode                    2
% 2.21/1.06  --bmc1_ucm_cone_mode                    none
% 2.21/1.06  --bmc1_ucm_reduced_relation_type        0
% 2.21/1.06  --bmc1_ucm_relax_model                  4
% 2.21/1.06  --bmc1_ucm_full_tr_after_sat            true
% 2.21/1.06  --bmc1_ucm_expand_neg_assumptions       false
% 2.21/1.06  --bmc1_ucm_layered_model                none
% 2.21/1.06  --bmc1_ucm_max_lemma_size               10
% 2.21/1.06  
% 2.21/1.06  ------ AIG Options
% 2.21/1.06  
% 2.21/1.06  --aig_mode                              false
% 2.21/1.06  
% 2.21/1.06  ------ Instantiation Options
% 2.21/1.06  
% 2.21/1.06  --instantiation_flag                    true
% 2.21/1.06  --inst_sos_flag                         true
% 2.21/1.06  --inst_sos_phase                        true
% 2.21/1.06  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.21/1.06  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.21/1.06  --inst_lit_sel_side                     none
% 2.21/1.06  --inst_solver_per_active                1400
% 2.21/1.06  --inst_solver_calls_frac                1.
% 2.21/1.06  --inst_passive_queue_type               priority_queues
% 2.21/1.06  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.21/1.06  --inst_passive_queues_freq              [25;2]
% 2.21/1.06  --inst_dismatching                      true
% 2.21/1.06  --inst_eager_unprocessed_to_passive     true
% 2.21/1.06  --inst_prop_sim_given                   true
% 2.21/1.06  --inst_prop_sim_new                     false
% 2.21/1.06  --inst_subs_new                         false
% 2.21/1.06  --inst_eq_res_simp                      false
% 2.21/1.06  --inst_subs_given                       false
% 2.21/1.06  --inst_orphan_elimination               true
% 2.21/1.06  --inst_learning_loop_flag               true
% 2.21/1.06  --inst_learning_start                   3000
% 2.21/1.06  --inst_learning_factor                  2
% 2.21/1.06  --inst_start_prop_sim_after_learn       3
% 2.21/1.06  --inst_sel_renew                        solver
% 2.21/1.06  --inst_lit_activity_flag                true
% 2.21/1.06  --inst_restr_to_given                   false
% 2.21/1.06  --inst_activity_threshold               500
% 2.21/1.06  --inst_out_proof                        true
% 2.21/1.06  
% 2.21/1.06  ------ Resolution Options
% 2.21/1.06  
% 2.21/1.06  --resolution_flag                       false
% 2.21/1.06  --res_lit_sel                           adaptive
% 2.21/1.06  --res_lit_sel_side                      none
% 2.21/1.06  --res_ordering                          kbo
% 2.21/1.06  --res_to_prop_solver                    active
% 2.21/1.06  --res_prop_simpl_new                    false
% 2.21/1.06  --res_prop_simpl_given                  true
% 2.21/1.06  --res_passive_queue_type                priority_queues
% 2.21/1.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.21/1.06  --res_passive_queues_freq               [15;5]
% 2.21/1.06  --res_forward_subs                      full
% 2.21/1.06  --res_backward_subs                     full
% 2.21/1.06  --res_forward_subs_resolution           true
% 2.21/1.06  --res_backward_subs_resolution          true
% 2.21/1.06  --res_orphan_elimination                true
% 2.21/1.06  --res_time_limit                        2.
% 2.21/1.06  --res_out_proof                         true
% 2.21/1.06  
% 2.21/1.06  ------ Superposition Options
% 2.21/1.06  
% 2.21/1.06  --superposition_flag                    true
% 2.21/1.06  --sup_passive_queue_type                priority_queues
% 2.21/1.06  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.21/1.06  --sup_passive_queues_freq               [8;1;4]
% 2.21/1.06  --demod_completeness_check              fast
% 2.21/1.06  --demod_use_ground                      true
% 2.21/1.06  --sup_to_prop_solver                    passive
% 2.21/1.06  --sup_prop_simpl_new                    true
% 2.21/1.06  --sup_prop_simpl_given                  true
% 2.21/1.06  --sup_fun_splitting                     true
% 2.21/1.06  --sup_smt_interval                      50000
% 2.21/1.06  
% 2.21/1.06  ------ Superposition Simplification Setup
% 2.21/1.06  
% 2.21/1.06  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 2.21/1.06  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 2.21/1.06  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 2.21/1.06  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 2.21/1.06  --sup_full_triv                         [TrivRules;PropSubs]
% 2.21/1.06  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 2.21/1.06  --sup_full_bw                           [BwDemod;BwSubsumption]
% 2.21/1.06  --sup_immed_triv                        [TrivRules]
% 2.21/1.06  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.21/1.06  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 2.21/1.06  --sup_immed_bw_main                     []
% 2.21/1.06  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 2.21/1.06  --sup_input_triv                        [Unflattening;TrivRules]
% 2.21/1.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 2.21/1.06  --sup_input_bw                          []
% 2.21/1.06  
% 2.21/1.06  ------ Combination Options
% 2.21/1.06  
% 2.21/1.06  --comb_res_mult                         3
% 2.21/1.06  --comb_sup_mult                         2
% 2.21/1.06  --comb_inst_mult                        10
% 2.21/1.06  
% 2.21/1.06  ------ Debug Options
% 2.21/1.06  
% 2.21/1.06  --dbg_backtrace                         false
% 2.21/1.06  --dbg_dump_prop_clauses                 false
% 2.21/1.06  --dbg_dump_prop_clauses_file            -
% 2.21/1.06  --dbg_out_stat                          false
% 2.21/1.06  
% 2.21/1.06  
% 2.21/1.06  
% 2.21/1.06  
% 2.21/1.06  ------ Proving...
% 2.21/1.06  
% 2.21/1.06  
% 2.21/1.06  % SZS status Theorem for theBenchmark.p
% 2.21/1.06  
% 2.21/1.06  % SZS output start CNFRefutation for theBenchmark.p
% 2.21/1.06  
% 2.21/1.06  fof(f2,axiom,(
% 2.21/1.06    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.21/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.21/1.06  
% 2.21/1.06  fof(f20,plain,(
% 2.21/1.06    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.21/1.06    inference(ennf_transformation,[],[f2])).
% 2.21/1.06  
% 2.21/1.06  fof(f39,plain,(
% 2.21/1.06    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.21/1.06    inference(cnf_transformation,[],[f20])).
% 2.21/1.06  
% 2.21/1.06  fof(f11,axiom,(
% 2.21/1.06    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 2.21/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.21/1.06  
% 2.21/1.06  fof(f25,plain,(
% 2.21/1.06    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 2.21/1.06    inference(ennf_transformation,[],[f11])).
% 2.21/1.06  
% 2.21/1.06  fof(f26,plain,(
% 2.21/1.06    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 2.21/1.06    inference(flattening,[],[f25])).
% 2.21/1.06  
% 2.21/1.06  fof(f49,plain,(
% 2.21/1.06    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.21/1.06    inference(cnf_transformation,[],[f26])).
% 2.21/1.06  
% 2.21/1.06  fof(f18,conjecture,(
% 2.21/1.06    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 2.21/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.21/1.06  
% 2.21/1.06  fof(f19,negated_conjecture,(
% 2.21/1.06    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 2.21/1.06    inference(negated_conjecture,[],[f18])).
% 2.21/1.06  
% 2.21/1.06  fof(f34,plain,(
% 2.21/1.06    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 2.21/1.06    inference(ennf_transformation,[],[f19])).
% 2.21/1.06  
% 2.21/1.06  fof(f36,plain,(
% 2.21/1.06    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 2.21/1.06    introduced(choice_axiom,[])).
% 2.21/1.06  
% 2.21/1.06  fof(f37,plain,(
% 2.21/1.06    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 2.21/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f36])).
% 2.21/1.06  
% 2.21/1.06  fof(f57,plain,(
% 2.21/1.06    v1_relat_1(sK0)),
% 2.21/1.06    inference(cnf_transformation,[],[f37])).
% 2.21/1.06  
% 2.21/1.06  fof(f3,axiom,(
% 2.21/1.06    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.21/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.21/1.06  
% 2.21/1.06  fof(f40,plain,(
% 2.21/1.06    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.21/1.06    inference(cnf_transformation,[],[f3])).
% 2.21/1.06  
% 2.21/1.06  fof(f17,axiom,(
% 2.21/1.06    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.21/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.21/1.06  
% 2.21/1.06  fof(f56,plain,(
% 2.21/1.06    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 2.21/1.06    inference(cnf_transformation,[],[f17])).
% 2.21/1.06  
% 2.21/1.06  fof(f15,axiom,(
% 2.21/1.06    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 2.21/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.21/1.06  
% 2.21/1.06  fof(f31,plain,(
% 2.21/1.06    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.21/1.06    inference(ennf_transformation,[],[f15])).
% 2.21/1.06  
% 2.21/1.06  fof(f32,plain,(
% 2.21/1.06    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.21/1.06    inference(flattening,[],[f31])).
% 2.21/1.06  
% 2.21/1.06  fof(f53,plain,(
% 2.21/1.06    ( ! [X0,X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.21/1.06    inference(cnf_transformation,[],[f32])).
% 2.21/1.06  
% 2.21/1.06  fof(f55,plain,(
% 2.21/1.06    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.21/1.06    inference(cnf_transformation,[],[f17])).
% 2.21/1.06  
% 2.21/1.06  fof(f9,axiom,(
% 2.21/1.06    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 2.21/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.21/1.06  
% 2.21/1.06  fof(f23,plain,(
% 2.21/1.06    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 2.21/1.06    inference(ennf_transformation,[],[f9])).
% 2.21/1.06  
% 2.21/1.06  fof(f47,plain,(
% 2.21/1.06    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 2.21/1.06    inference(cnf_transformation,[],[f23])).
% 2.21/1.06  
% 2.21/1.06  fof(f1,axiom,(
% 2.21/1.06    v1_xboole_0(k1_xboole_0)),
% 2.21/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.21/1.06  
% 2.21/1.06  fof(f38,plain,(
% 2.21/1.06    v1_xboole_0(k1_xboole_0)),
% 2.21/1.06    inference(cnf_transformation,[],[f1])).
% 2.21/1.06  
% 2.21/1.06  fof(f12,axiom,(
% 2.21/1.06    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k1_relat_1(X0)))),
% 2.21/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.21/1.06  
% 2.21/1.06  fof(f27,plain,(
% 2.21/1.06    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 2.21/1.06    inference(ennf_transformation,[],[f12])).
% 2.21/1.06  
% 2.21/1.06  fof(f28,plain,(
% 2.21/1.06    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 2.21/1.06    inference(flattening,[],[f27])).
% 2.21/1.06  
% 2.21/1.06  fof(f50,plain,(
% 2.21/1.06    ( ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 2.21/1.06    inference(cnf_transformation,[],[f28])).
% 2.21/1.06  
% 2.21/1.06  fof(f10,axiom,(
% 2.21/1.06    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 2.21/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.21/1.06  
% 2.21/1.06  fof(f24,plain,(
% 2.21/1.06    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.21/1.06    inference(ennf_transformation,[],[f10])).
% 2.21/1.06  
% 2.21/1.06  fof(f48,plain,(
% 2.21/1.06    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.21/1.06    inference(cnf_transformation,[],[f24])).
% 2.21/1.06  
% 2.21/1.06  fof(f16,axiom,(
% 2.21/1.06    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 2.21/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.21/1.06  
% 2.21/1.06  fof(f33,plain,(
% 2.21/1.06    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.21/1.06    inference(ennf_transformation,[],[f16])).
% 2.21/1.06  
% 2.21/1.06  fof(f54,plain,(
% 2.21/1.06    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.21/1.06    inference(cnf_transformation,[],[f33])).
% 2.21/1.06  
% 2.21/1.06  fof(f14,axiom,(
% 2.21/1.06    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k6_subset_1(X0,X1))))),
% 2.21/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.21/1.06  
% 2.21/1.06  fof(f30,plain,(
% 2.21/1.06    ! [X0] : (! [X1] : (k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k6_subset_1(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.21/1.06    inference(ennf_transformation,[],[f14])).
% 2.21/1.06  
% 2.21/1.06  fof(f52,plain,(
% 2.21/1.06    ( ! [X0,X1] : (k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k6_subset_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.21/1.06    inference(cnf_transformation,[],[f30])).
% 2.21/1.06  
% 2.21/1.06  fof(f6,axiom,(
% 2.21/1.06    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 2.21/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.21/1.06  
% 2.21/1.06  fof(f43,plain,(
% 2.21/1.06    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 2.21/1.06    inference(cnf_transformation,[],[f6])).
% 2.21/1.06  
% 2.21/1.06  fof(f8,axiom,(
% 2.21/1.06    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.21/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.21/1.06  
% 2.21/1.06  fof(f35,plain,(
% 2.21/1.06    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.21/1.06    inference(nnf_transformation,[],[f8])).
% 2.21/1.06  
% 2.21/1.06  fof(f45,plain,(
% 2.21/1.06    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.21/1.06    inference(cnf_transformation,[],[f35])).
% 2.21/1.06  
% 2.21/1.06  fof(f4,axiom,(
% 2.21/1.06    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 2.21/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.21/1.06  
% 2.21/1.06  fof(f21,plain,(
% 2.21/1.06    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 2.21/1.06    inference(ennf_transformation,[],[f4])).
% 2.21/1.06  
% 2.21/1.06  fof(f22,plain,(
% 2.21/1.06    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 2.21/1.06    inference(flattening,[],[f21])).
% 2.21/1.06  
% 2.21/1.06  fof(f41,plain,(
% 2.21/1.06    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 2.21/1.06    inference(cnf_transformation,[],[f22])).
% 2.21/1.06  
% 2.21/1.06  fof(f5,axiom,(
% 2.21/1.06    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 2.21/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.21/1.06  
% 2.21/1.06  fof(f42,plain,(
% 2.21/1.06    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 2.21/1.06    inference(cnf_transformation,[],[f5])).
% 2.21/1.06  
% 2.21/1.06  fof(f7,axiom,(
% 2.21/1.06    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 2.21/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.21/1.06  
% 2.21/1.06  fof(f44,plain,(
% 2.21/1.06    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 2.21/1.06    inference(cnf_transformation,[],[f7])).
% 2.21/1.06  
% 2.21/1.06  fof(f59,plain,(
% 2.21/1.06    ( ! [X0,X1] : (r1_xboole_0(k6_subset_1(X0,X1),X1)) )),
% 2.21/1.06    inference(definition_unfolding,[],[f42,f44])).
% 2.21/1.06  
% 2.21/1.06  fof(f13,axiom,(
% 2.21/1.06    ! [X0] : (v1_relat_1(X0) => k4_relat_1(k4_relat_1(X0)) = X0)),
% 2.21/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.21/1.06  
% 2.21/1.06  fof(f29,plain,(
% 2.21/1.06    ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 2.21/1.06    inference(ennf_transformation,[],[f13])).
% 2.21/1.06  
% 2.21/1.06  fof(f51,plain,(
% 2.21/1.06    ( ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 2.21/1.06    inference(cnf_transformation,[],[f29])).
% 2.21/1.06  
% 2.21/1.06  fof(f58,plain,(
% 2.21/1.06    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 2.21/1.06    inference(cnf_transformation,[],[f37])).
% 2.21/1.06  
% 2.21/1.06  cnf(c_1,plain,
% 2.21/1.06      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.21/1.06      inference(cnf_transformation,[],[f39]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_538,plain,
% 2.21/1.06      ( ~ v1_xboole_0(X0_41) | k1_xboole_0 = X0_41 ),
% 2.21/1.06      inference(subtyping,[status(esa)],[c_1]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_876,plain,
% 2.21/1.06      ( ~ v1_xboole_0(k5_relat_1(X0_41,X1_41))
% 2.21/1.06      | k1_xboole_0 = k5_relat_1(X0_41,X1_41) ),
% 2.21/1.06      inference(instantiation,[status(thm)],[c_538]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_3655,plain,
% 2.21/1.06      ( ~ v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))
% 2.21/1.06      | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
% 2.21/1.06      inference(instantiation,[status(thm)],[c_876]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_10,plain,
% 2.21/1.06      ( ~ v1_relat_1(X0)
% 2.21/1.06      | ~ v1_relat_1(X1)
% 2.21/1.06      | v1_relat_1(k5_relat_1(X0,X1)) ),
% 2.21/1.06      inference(cnf_transformation,[],[f49]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_534,plain,
% 2.21/1.06      ( ~ v1_relat_1(X0_41)
% 2.21/1.06      | ~ v1_relat_1(X1_41)
% 2.21/1.06      | v1_relat_1(k5_relat_1(X0_41,X1_41)) ),
% 2.21/1.06      inference(subtyping,[status(esa)],[c_10]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_810,plain,
% 2.21/1.06      ( v1_relat_1(X0_41) != iProver_top
% 2.21/1.06      | v1_relat_1(X1_41) != iProver_top
% 2.21/1.06      | v1_relat_1(k5_relat_1(X1_41,X0_41)) = iProver_top ),
% 2.21/1.06      inference(predicate_to_equality,[status(thm)],[c_534]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_19,negated_conjecture,
% 2.21/1.06      ( v1_relat_1(sK0) ),
% 2.21/1.06      inference(cnf_transformation,[],[f57]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_525,negated_conjecture,
% 2.21/1.06      ( v1_relat_1(sK0) ),
% 2.21/1.06      inference(subtyping,[status(esa)],[c_19]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_816,plain,
% 2.21/1.06      ( v1_relat_1(sK0) = iProver_top ),
% 2.21/1.06      inference(predicate_to_equality,[status(thm)],[c_525]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_2,plain,
% 2.21/1.06      ( r1_tarski(k1_xboole_0,X0) ),
% 2.21/1.06      inference(cnf_transformation,[],[f40]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_537,plain,
% 2.21/1.06      ( r1_tarski(k1_xboole_0,X0_41) ),
% 2.21/1.06      inference(subtyping,[status(esa)],[c_2]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_807,plain,
% 2.21/1.06      ( r1_tarski(k1_xboole_0,X0_41) = iProver_top ),
% 2.21/1.06      inference(predicate_to_equality,[status(thm)],[c_537]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_16,plain,
% 2.21/1.06      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.21/1.06      inference(cnf_transformation,[],[f56]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_528,plain,
% 2.21/1.06      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.21/1.06      inference(subtyping,[status(esa)],[c_16]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_14,plain,
% 2.21/1.06      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
% 2.21/1.06      | ~ v1_relat_1(X0)
% 2.21/1.06      | ~ v1_relat_1(X1)
% 2.21/1.06      | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ),
% 2.21/1.06      inference(cnf_transformation,[],[f53]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_530,plain,
% 2.21/1.06      ( ~ r1_tarski(k2_relat_1(X0_41),k1_relat_1(X1_41))
% 2.21/1.06      | ~ v1_relat_1(X0_41)
% 2.21/1.06      | ~ v1_relat_1(X1_41)
% 2.21/1.06      | k1_relat_1(k5_relat_1(X0_41,X1_41)) = k1_relat_1(X0_41) ),
% 2.21/1.06      inference(subtyping,[status(esa)],[c_14]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_814,plain,
% 2.21/1.06      ( k1_relat_1(k5_relat_1(X0_41,X1_41)) = k1_relat_1(X0_41)
% 2.21/1.06      | r1_tarski(k2_relat_1(X0_41),k1_relat_1(X1_41)) != iProver_top
% 2.21/1.06      | v1_relat_1(X1_41) != iProver_top
% 2.21/1.06      | v1_relat_1(X0_41) != iProver_top ),
% 2.21/1.06      inference(predicate_to_equality,[status(thm)],[c_530]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_1614,plain,
% 2.21/1.06      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0_41)) = k1_relat_1(k1_xboole_0)
% 2.21/1.06      | r1_tarski(k1_xboole_0,k1_relat_1(X0_41)) != iProver_top
% 2.21/1.06      | v1_relat_1(X0_41) != iProver_top
% 2.21/1.06      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 2.21/1.06      inference(superposition,[status(thm)],[c_528,c_814]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_17,plain,
% 2.21/1.06      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.21/1.06      inference(cnf_transformation,[],[f55]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_527,plain,
% 2.21/1.06      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.21/1.06      inference(subtyping,[status(esa)],[c_17]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_1616,plain,
% 2.21/1.06      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0_41)) = k1_xboole_0
% 2.21/1.06      | r1_tarski(k1_xboole_0,k1_relat_1(X0_41)) != iProver_top
% 2.21/1.06      | v1_relat_1(X0_41) != iProver_top
% 2.21/1.06      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 2.21/1.06      inference(light_normalisation,[status(thm)],[c_1614,c_527]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_8,plain,
% 2.21/1.06      ( v1_relat_1(X0) | ~ v1_xboole_0(X0) ),
% 2.21/1.06      inference(cnf_transformation,[],[f47]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_42,plain,
% 2.21/1.06      ( v1_relat_1(X0) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 2.21/1.06      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_44,plain,
% 2.21/1.06      ( v1_relat_1(k1_xboole_0) = iProver_top
% 2.21/1.06      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.21/1.06      inference(instantiation,[status(thm)],[c_42]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_0,plain,
% 2.21/1.06      ( v1_xboole_0(k1_xboole_0) ),
% 2.21/1.06      inference(cnf_transformation,[],[f38]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_66,plain,
% 2.21/1.06      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.21/1.06      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_1624,plain,
% 2.21/1.06      ( v1_relat_1(X0_41) != iProver_top
% 2.21/1.06      | r1_tarski(k1_xboole_0,k1_relat_1(X0_41)) != iProver_top
% 2.21/1.06      | k1_relat_1(k5_relat_1(k1_xboole_0,X0_41)) = k1_xboole_0 ),
% 2.21/1.06      inference(global_propositional_subsumption,
% 2.21/1.06                [status(thm)],
% 2.21/1.06                [c_1616,c_44,c_66]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_1625,plain,
% 2.21/1.06      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0_41)) = k1_xboole_0
% 2.21/1.06      | r1_tarski(k1_xboole_0,k1_relat_1(X0_41)) != iProver_top
% 2.21/1.06      | v1_relat_1(X0_41) != iProver_top ),
% 2.21/1.06      inference(renaming,[status(thm)],[c_1624]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_1628,plain,
% 2.21/1.06      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0_41)) = k1_xboole_0
% 2.21/1.06      | v1_relat_1(X0_41) != iProver_top ),
% 2.21/1.06      inference(superposition,[status(thm)],[c_807,c_1625]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_2299,plain,
% 2.21/1.06      ( k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k1_xboole_0 ),
% 2.21/1.06      inference(superposition,[status(thm)],[c_816,c_1628]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_11,plain,
% 2.21/1.06      ( ~ v1_relat_1(X0)
% 2.21/1.06      | v1_xboole_0(X0)
% 2.21/1.06      | ~ v1_xboole_0(k1_relat_1(X0)) ),
% 2.21/1.06      inference(cnf_transformation,[],[f50]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_533,plain,
% 2.21/1.06      ( ~ v1_relat_1(X0_41)
% 2.21/1.06      | v1_xboole_0(X0_41)
% 2.21/1.06      | ~ v1_xboole_0(k1_relat_1(X0_41)) ),
% 2.21/1.06      inference(subtyping,[status(esa)],[c_11]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_811,plain,
% 2.21/1.06      ( v1_relat_1(X0_41) != iProver_top
% 2.21/1.06      | v1_xboole_0(X0_41) = iProver_top
% 2.21/1.06      | v1_xboole_0(k1_relat_1(X0_41)) != iProver_top ),
% 2.21/1.06      inference(predicate_to_equality,[status(thm)],[c_533]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_2312,plain,
% 2.21/1.06      ( v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) != iProver_top
% 2.21/1.06      | v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) = iProver_top
% 2.21/1.06      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.21/1.06      inference(superposition,[status(thm)],[c_2299,c_811]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_3234,plain,
% 2.21/1.06      ( v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) = iProver_top
% 2.21/1.06      | v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) != iProver_top ),
% 2.21/1.06      inference(global_propositional_subsumption,
% 2.21/1.06                [status(thm)],
% 2.21/1.06                [c_2312,c_66]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_3235,plain,
% 2.21/1.06      ( v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) != iProver_top
% 2.21/1.06      | v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) = iProver_top ),
% 2.21/1.06      inference(renaming,[status(thm)],[c_3234]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_3238,plain,
% 2.21/1.06      ( v1_relat_1(sK0) != iProver_top
% 2.21/1.06      | v1_relat_1(k1_xboole_0) != iProver_top
% 2.21/1.06      | v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) = iProver_top ),
% 2.21/1.06      inference(superposition,[status(thm)],[c_810,c_3235]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_3239,plain,
% 2.21/1.06      ( ~ v1_relat_1(sK0)
% 2.21/1.06      | ~ v1_relat_1(k1_xboole_0)
% 2.21/1.06      | v1_xboole_0(k5_relat_1(k1_xboole_0,sK0)) ),
% 2.21/1.06      inference(predicate_to_equality_rev,[status(thm)],[c_3238]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_9,plain,
% 2.21/1.06      ( ~ v1_relat_1(X0) | v1_relat_1(k4_relat_1(X0)) ),
% 2.21/1.06      inference(cnf_transformation,[],[f48]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_535,plain,
% 2.21/1.06      ( ~ v1_relat_1(X0_41) | v1_relat_1(k4_relat_1(X0_41)) ),
% 2.21/1.06      inference(subtyping,[status(esa)],[c_9]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_809,plain,
% 2.21/1.06      ( v1_relat_1(X0_41) != iProver_top
% 2.21/1.06      | v1_relat_1(k4_relat_1(X0_41)) = iProver_top ),
% 2.21/1.06      inference(predicate_to_equality,[status(thm)],[c_535]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_2301,plain,
% 2.21/1.06      ( k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(X0_41))) = k1_xboole_0
% 2.21/1.06      | v1_relat_1(X0_41) != iProver_top ),
% 2.21/1.06      inference(superposition,[status(thm)],[c_809,c_1628]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_2893,plain,
% 2.21/1.06      ( k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) = k1_xboole_0 ),
% 2.21/1.06      inference(superposition,[status(thm)],[c_816,c_2301]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_539,plain,
% 2.21/1.06      ( v1_xboole_0(k1_xboole_0) ),
% 2.21/1.06      inference(subtyping,[status(esa)],[c_0]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_805,plain,
% 2.21/1.06      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.21/1.06      inference(predicate_to_equality,[status(thm)],[c_539]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_536,plain,
% 2.21/1.06      ( v1_relat_1(X0_41) | ~ v1_xboole_0(X0_41) ),
% 2.21/1.06      inference(subtyping,[status(esa)],[c_8]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_808,plain,
% 2.21/1.06      ( v1_relat_1(X0_41) = iProver_top
% 2.21/1.06      | v1_xboole_0(X0_41) != iProver_top ),
% 2.21/1.06      inference(predicate_to_equality,[status(thm)],[c_536]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_1044,plain,
% 2.21/1.06      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 2.21/1.06      inference(superposition,[status(thm)],[c_805,c_808]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_15,plain,
% 2.21/1.06      ( ~ v1_relat_1(X0)
% 2.21/1.06      | ~ v1_relat_1(X1)
% 2.21/1.06      | k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1)) ),
% 2.21/1.06      inference(cnf_transformation,[],[f54]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_529,plain,
% 2.21/1.06      ( ~ v1_relat_1(X0_41)
% 2.21/1.06      | ~ v1_relat_1(X1_41)
% 2.21/1.06      | k5_relat_1(k4_relat_1(X1_41),k4_relat_1(X0_41)) = k4_relat_1(k5_relat_1(X0_41,X1_41)) ),
% 2.21/1.06      inference(subtyping,[status(esa)],[c_15]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_815,plain,
% 2.21/1.06      ( k5_relat_1(k4_relat_1(X0_41),k4_relat_1(X1_41)) = k4_relat_1(k5_relat_1(X1_41,X0_41))
% 2.21/1.06      | v1_relat_1(X0_41) != iProver_top
% 2.21/1.06      | v1_relat_1(X1_41) != iProver_top ),
% 2.21/1.06      inference(predicate_to_equality,[status(thm)],[c_529]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_1526,plain,
% 2.21/1.06      ( k5_relat_1(k4_relat_1(X0_41),k4_relat_1(sK0)) = k4_relat_1(k5_relat_1(sK0,X0_41))
% 2.21/1.06      | v1_relat_1(X0_41) != iProver_top ),
% 2.21/1.06      inference(superposition,[status(thm)],[c_816,c_815]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_1808,plain,
% 2.21/1.06      ( k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(sK0)) = k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
% 2.21/1.06      inference(superposition,[status(thm)],[c_1044,c_1526]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_13,plain,
% 2.21/1.06      ( ~ v1_relat_1(X0)
% 2.21/1.06      | ~ v1_relat_1(X1)
% 2.21/1.06      | k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k6_subset_1(X0,X1)) ),
% 2.21/1.06      inference(cnf_transformation,[],[f52]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_531,plain,
% 2.21/1.06      ( ~ v1_relat_1(X0_41)
% 2.21/1.06      | ~ v1_relat_1(X1_41)
% 2.21/1.06      | k6_subset_1(k4_relat_1(X0_41),k4_relat_1(X1_41)) = k4_relat_1(k6_subset_1(X0_41,X1_41)) ),
% 2.21/1.06      inference(subtyping,[status(esa)],[c_13]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_813,plain,
% 2.21/1.06      ( k6_subset_1(k4_relat_1(X0_41),k4_relat_1(X1_41)) = k4_relat_1(k6_subset_1(X0_41,X1_41))
% 2.21/1.06      | v1_relat_1(X1_41) != iProver_top
% 2.21/1.06      | v1_relat_1(X0_41) != iProver_top ),
% 2.21/1.06      inference(predicate_to_equality,[status(thm)],[c_531]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_1510,plain,
% 2.21/1.06      ( k6_subset_1(k4_relat_1(X0_41),k4_relat_1(sK0)) = k4_relat_1(k6_subset_1(X0_41,sK0))
% 2.21/1.06      | v1_relat_1(X0_41) != iProver_top ),
% 2.21/1.06      inference(superposition,[status(thm)],[c_816,c_813]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_1699,plain,
% 2.21/1.06      ( k6_subset_1(k4_relat_1(sK0),k4_relat_1(sK0)) = k4_relat_1(k6_subset_1(sK0,sK0)) ),
% 2.21/1.06      inference(superposition,[status(thm)],[c_816,c_1510]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_5,plain,
% 2.21/1.06      ( m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
% 2.21/1.06      inference(cnf_transformation,[],[f43]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_7,plain,
% 2.21/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.21/1.06      inference(cnf_transformation,[],[f45]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_141,plain,
% 2.21/1.06      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.21/1.06      inference(prop_impl,[status(thm)],[c_7]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_142,plain,
% 2.21/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.21/1.06      inference(renaming,[status(thm)],[c_141]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_255,plain,
% 2.21/1.06      ( r1_tarski(X0,X1)
% 2.21/1.06      | k6_subset_1(X2,X3) != X0
% 2.21/1.06      | k1_zfmisc_1(X1) != k1_zfmisc_1(X2) ),
% 2.21/1.06      inference(resolution_lifted,[status(thm)],[c_5,c_142]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_256,plain,
% 2.21/1.06      ( r1_tarski(k6_subset_1(X0,X1),X2)
% 2.21/1.06      | k1_zfmisc_1(X2) != k1_zfmisc_1(X0) ),
% 2.21/1.06      inference(unflattening,[status(thm)],[c_255]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_523,plain,
% 2.21/1.06      ( r1_tarski(k6_subset_1(X0_41,X1_41),X2_41)
% 2.21/1.06      | k1_zfmisc_1(X2_41) != k1_zfmisc_1(X0_41) ),
% 2.21/1.06      inference(subtyping,[status(esa)],[c_256]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_818,plain,
% 2.21/1.06      ( k1_zfmisc_1(X0_41) != k1_zfmisc_1(X1_41)
% 2.21/1.06      | r1_tarski(k6_subset_1(X1_41,X2_41),X0_41) = iProver_top ),
% 2.21/1.06      inference(predicate_to_equality,[status(thm)],[c_523]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_1359,plain,
% 2.21/1.06      ( r1_tarski(k6_subset_1(X0_41,X1_41),X0_41) = iProver_top ),
% 2.21/1.06      inference(equality_resolution,[status(thm)],[c_818]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_3,plain,
% 2.21/1.06      ( ~ r1_xboole_0(X0,X1) | ~ r1_tarski(X0,X1) | v1_xboole_0(X0) ),
% 2.21/1.06      inference(cnf_transformation,[],[f41]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_4,plain,
% 2.21/1.06      ( r1_xboole_0(k6_subset_1(X0,X1),X1) ),
% 2.21/1.06      inference(cnf_transformation,[],[f59]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_239,plain,
% 2.21/1.06      ( ~ r1_tarski(X0,X1)
% 2.21/1.06      | v1_xboole_0(X0)
% 2.21/1.06      | X2 != X1
% 2.21/1.06      | k6_subset_1(X3,X2) != X0 ),
% 2.21/1.06      inference(resolution_lifted,[status(thm)],[c_3,c_4]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_240,plain,
% 2.21/1.06      ( ~ r1_tarski(k6_subset_1(X0,X1),X1)
% 2.21/1.06      | v1_xboole_0(k6_subset_1(X0,X1)) ),
% 2.21/1.06      inference(unflattening,[status(thm)],[c_239]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_524,plain,
% 2.21/1.06      ( ~ r1_tarski(k6_subset_1(X0_41,X1_41),X1_41)
% 2.21/1.06      | v1_xboole_0(k6_subset_1(X0_41,X1_41)) ),
% 2.21/1.06      inference(subtyping,[status(esa)],[c_240]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_817,plain,
% 2.21/1.06      ( r1_tarski(k6_subset_1(X0_41,X1_41),X1_41) != iProver_top
% 2.21/1.06      | v1_xboole_0(k6_subset_1(X0_41,X1_41)) = iProver_top ),
% 2.21/1.06      inference(predicate_to_equality,[status(thm)],[c_524]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_1436,plain,
% 2.21/1.06      ( v1_xboole_0(k6_subset_1(X0_41,X0_41)) = iProver_top ),
% 2.21/1.06      inference(superposition,[status(thm)],[c_1359,c_817]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_806,plain,
% 2.21/1.06      ( k1_xboole_0 = X0_41 | v1_xboole_0(X0_41) != iProver_top ),
% 2.21/1.06      inference(predicate_to_equality,[status(thm)],[c_538]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_1442,plain,
% 2.21/1.06      ( k6_subset_1(X0_41,X0_41) = k1_xboole_0 ),
% 2.21/1.06      inference(superposition,[status(thm)],[c_1436,c_806]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_1703,plain,
% 2.21/1.06      ( k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.21/1.06      inference(demodulation,[status(thm)],[c_1699,c_1442]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_1811,plain,
% 2.21/1.06      ( k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) = k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
% 2.21/1.06      inference(light_normalisation,[status(thm)],[c_1808,c_1703]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_2900,plain,
% 2.21/1.06      ( k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = k1_xboole_0 ),
% 2.21/1.06      inference(light_normalisation,[status(thm)],[c_2893,c_1811]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_3088,plain,
% 2.21/1.06      ( v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) != iProver_top
% 2.21/1.06      | v1_xboole_0(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = iProver_top
% 2.21/1.06      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.21/1.06      inference(superposition,[status(thm)],[c_2900,c_811]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_1006,plain,
% 2.21/1.06      ( ~ v1_xboole_0(k4_relat_1(k5_relat_1(X0_41,X1_41)))
% 2.21/1.06      | k1_xboole_0 = k4_relat_1(k5_relat_1(X0_41,X1_41)) ),
% 2.21/1.06      inference(instantiation,[status(thm)],[c_538]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_2980,plain,
% 2.21/1.06      ( ~ v1_xboole_0(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
% 2.21/1.06      | k1_xboole_0 = k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
% 2.21/1.06      inference(instantiation,[status(thm)],[c_1006]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_2981,plain,
% 2.21/1.06      ( k1_xboole_0 = k4_relat_1(k5_relat_1(sK0,k1_xboole_0))
% 2.21/1.06      | v1_xboole_0(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) != iProver_top ),
% 2.21/1.06      inference(predicate_to_equality,[status(thm)],[c_2980]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_543,plain,
% 2.21/1.06      ( X0_41 != X1_41 | X2_41 != X1_41 | X2_41 = X0_41 ),
% 2.21/1.06      theory(equality) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_1234,plain,
% 2.21/1.06      ( X0_41 != X1_41
% 2.21/1.06      | k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) != X1_41
% 2.21/1.06      | k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = X0_41 ),
% 2.21/1.06      inference(instantiation,[status(thm)],[c_543]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_1367,plain,
% 2.21/1.06      ( X0_41 != k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
% 2.21/1.06      | k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = X0_41
% 2.21/1.06      | k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) != k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
% 2.21/1.06      inference(instantiation,[status(thm)],[c_1234]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_2282,plain,
% 2.21/1.06      ( k4_relat_1(X0_41) != k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
% 2.21/1.06      | k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = k4_relat_1(X0_41)
% 2.21/1.06      | k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) != k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
% 2.21/1.06      inference(instantiation,[status(thm)],[c_1367]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_2283,plain,
% 2.21/1.06      ( k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) != k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
% 2.21/1.06      | k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = k4_relat_1(k1_xboole_0)
% 2.21/1.06      | k4_relat_1(k1_xboole_0) != k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
% 2.21/1.06      inference(instantiation,[status(thm)],[c_2282]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_1364,plain,
% 2.21/1.06      ( X0_41 != k5_relat_1(sK0,k1_xboole_0)
% 2.21/1.06      | k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = X0_41
% 2.21/1.06      | k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) != k5_relat_1(sK0,k1_xboole_0) ),
% 2.21/1.06      inference(instantiation,[status(thm)],[c_1234]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_2108,plain,
% 2.21/1.06      ( k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) != k5_relat_1(sK0,k1_xboole_0)
% 2.21/1.06      | k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
% 2.21/1.06      inference(instantiation,[status(thm)],[c_1364]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_1387,plain,
% 2.21/1.06      ( ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
% 2.21/1.06      | v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
% 2.21/1.06      inference(instantiation,[status(thm)],[c_535]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_1388,plain,
% 2.21/1.06      ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) != iProver_top
% 2.21/1.06      | v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = iProver_top ),
% 2.21/1.06      inference(predicate_to_equality,[status(thm)],[c_1387]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_549,plain,
% 2.21/1.06      ( X0_41 != X1_41 | k4_relat_1(X0_41) = k4_relat_1(X1_41) ),
% 2.21/1.06      theory(equality) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_1356,plain,
% 2.21/1.06      ( X0_41 != k4_relat_1(k5_relat_1(sK0,k1_xboole_0))
% 2.21/1.06      | k4_relat_1(X0_41) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
% 2.21/1.06      inference(instantiation,[status(thm)],[c_549]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_1357,plain,
% 2.21/1.06      ( k4_relat_1(k1_xboole_0) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
% 2.21/1.06      | k1_xboole_0 != k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
% 2.21/1.06      inference(instantiation,[status(thm)],[c_1356]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_1351,plain,
% 2.21/1.06      ( k4_relat_1(X0_41) != X1_41
% 2.21/1.06      | k1_xboole_0 != X1_41
% 2.21/1.06      | k1_xboole_0 = k4_relat_1(X0_41) ),
% 2.21/1.06      inference(instantiation,[status(thm)],[c_543]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_1352,plain,
% 2.21/1.06      ( k4_relat_1(k1_xboole_0) != k1_xboole_0
% 2.21/1.06      | k1_xboole_0 = k4_relat_1(k1_xboole_0)
% 2.21/1.06      | k1_xboole_0 != k1_xboole_0 ),
% 2.21/1.06      inference(instantiation,[status(thm)],[c_1351]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_1070,plain,
% 2.21/1.06      ( k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) != X0_41
% 2.21/1.06      | k1_xboole_0 != X0_41
% 2.21/1.06      | k1_xboole_0 = k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
% 2.21/1.06      inference(instantiation,[status(thm)],[c_543]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_1235,plain,
% 2.21/1.06      ( k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) != k4_relat_1(X0_41)
% 2.21/1.06      | k1_xboole_0 != k4_relat_1(X0_41)
% 2.21/1.06      | k1_xboole_0 = k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
% 2.21/1.06      inference(instantiation,[status(thm)],[c_1070]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_1236,plain,
% 2.21/1.06      ( k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) != k4_relat_1(k1_xboole_0)
% 2.21/1.06      | k1_xboole_0 = k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
% 2.21/1.06      | k1_xboole_0 != k4_relat_1(k1_xboole_0) ),
% 2.21/1.06      inference(instantiation,[status(thm)],[c_1235]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_12,plain,
% 2.21/1.06      ( ~ v1_relat_1(X0) | k4_relat_1(k4_relat_1(X0)) = X0 ),
% 2.21/1.06      inference(cnf_transformation,[],[f51]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_532,plain,
% 2.21/1.06      ( ~ v1_relat_1(X0_41) | k4_relat_1(k4_relat_1(X0_41)) = X0_41 ),
% 2.21/1.06      inference(subtyping,[status(esa)],[c_12]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_1081,plain,
% 2.21/1.06      ( ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
% 2.21/1.06      | k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = k5_relat_1(sK0,k1_xboole_0) ),
% 2.21/1.06      inference(instantiation,[status(thm)],[c_532]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_837,plain,
% 2.21/1.06      ( k5_relat_1(sK0,k1_xboole_0) != X0_41
% 2.21/1.06      | k1_xboole_0 != X0_41
% 2.21/1.06      | k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
% 2.21/1.06      inference(instantiation,[status(thm)],[c_543]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_1021,plain,
% 2.21/1.06      ( k5_relat_1(sK0,k1_xboole_0) != k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
% 2.21/1.06      | k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)
% 2.21/1.06      | k1_xboole_0 != k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
% 2.21/1.06      inference(instantiation,[status(thm)],[c_837]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_850,plain,
% 2.21/1.06      ( X0_41 != X1_41
% 2.21/1.06      | k5_relat_1(sK0,k1_xboole_0) != X1_41
% 2.21/1.06      | k5_relat_1(sK0,k1_xboole_0) = X0_41 ),
% 2.21/1.06      inference(instantiation,[status(thm)],[c_543]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_871,plain,
% 2.21/1.06      ( X0_41 != k5_relat_1(sK0,k1_xboole_0)
% 2.21/1.06      | k5_relat_1(sK0,k1_xboole_0) = X0_41
% 2.21/1.06      | k5_relat_1(sK0,k1_xboole_0) != k5_relat_1(sK0,k1_xboole_0) ),
% 2.21/1.06      inference(instantiation,[status(thm)],[c_850]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_944,plain,
% 2.21/1.06      ( k5_relat_1(sK0,k1_xboole_0) != k5_relat_1(sK0,k1_xboole_0)
% 2.21/1.06      | k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))
% 2.21/1.06      | k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) != k5_relat_1(sK0,k1_xboole_0) ),
% 2.21/1.06      inference(instantiation,[status(thm)],[c_871]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_541,plain,( X0_41 = X0_41 ),theory(equality) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_892,plain,
% 2.21/1.06      ( k5_relat_1(sK0,k1_xboole_0) = k5_relat_1(sK0,k1_xboole_0) ),
% 2.21/1.06      inference(instantiation,[status(thm)],[c_541]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_861,plain,
% 2.21/1.06      ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
% 2.21/1.06      | ~ v1_relat_1(sK0)
% 2.21/1.06      | ~ v1_relat_1(k1_xboole_0) ),
% 2.21/1.06      inference(instantiation,[status(thm)],[c_534]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_862,plain,
% 2.21/1.06      ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) = iProver_top
% 2.21/1.06      | v1_relat_1(sK0) != iProver_top
% 2.21/1.06      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 2.21/1.06      inference(predicate_to_equality,[status(thm)],[c_861]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_18,negated_conjecture,
% 2.21/1.06      ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
% 2.21/1.06      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
% 2.21/1.06      inference(cnf_transformation,[],[f58]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_526,negated_conjecture,
% 2.21/1.06      ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
% 2.21/1.06      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
% 2.21/1.06      inference(subtyping,[status(esa)],[c_18]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_562,plain,
% 2.21/1.06      ( k1_xboole_0 = k1_xboole_0 ),
% 2.21/1.06      inference(instantiation,[status(thm)],[c_541]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_43,plain,
% 2.21/1.06      ( v1_relat_1(k1_xboole_0) | ~ v1_xboole_0(k1_xboole_0) ),
% 2.21/1.06      inference(instantiation,[status(thm)],[c_8]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(c_20,plain,
% 2.21/1.06      ( v1_relat_1(sK0) = iProver_top ),
% 2.21/1.06      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.21/1.06  
% 2.21/1.06  cnf(contradiction,plain,
% 2.21/1.06      ( $false ),
% 2.21/1.06      inference(minisat,
% 2.21/1.06                [status(thm)],
% 2.21/1.06                [c_3655,c_3239,c_3088,c_2981,c_2283,c_2108,c_1703,c_1388,
% 2.21/1.06                 c_1357,c_1352,c_1236,c_1081,c_1021,c_944,c_892,c_862,
% 2.21/1.06                 c_861,c_526,c_562,c_66,c_0,c_44,c_43,c_20,c_19]) ).
% 2.21/1.06  
% 2.21/1.06  
% 2.21/1.06  % SZS output end CNFRefutation for theBenchmark.p
% 2.21/1.06  
% 2.21/1.06  ------                               Statistics
% 2.21/1.06  
% 2.21/1.06  ------ General
% 2.21/1.06  
% 2.21/1.06  abstr_ref_over_cycles:                  0
% 2.21/1.06  abstr_ref_under_cycles:                 0
% 2.21/1.06  gc_basic_clause_elim:                   0
% 2.21/1.06  forced_gc_time:                         0
% 2.21/1.06  parsing_time:                           0.007
% 2.21/1.06  unif_index_cands_time:                  0.
% 2.21/1.06  unif_index_add_time:                    0.
% 2.21/1.06  orderings_time:                         0.
% 2.21/1.06  out_proof_time:                         0.028
% 2.21/1.06  total_time:                             0.175
% 2.21/1.06  num_of_symbols:                         46
% 2.21/1.06  num_of_terms:                           3137
% 2.21/1.06  
% 2.21/1.06  ------ Preprocessing
% 2.21/1.06  
% 2.21/1.06  num_of_splits:                          0
% 2.21/1.06  num_of_split_atoms:                     0
% 2.21/1.06  num_of_reused_defs:                     0
% 2.21/1.06  num_eq_ax_congr_red:                    4
% 2.21/1.06  num_of_sem_filtered_clauses:            1
% 2.21/1.06  num_of_subtypes:                        2
% 2.21/1.06  monotx_restored_types:                  1
% 2.21/1.06  sat_num_of_epr_types:                   0
% 2.21/1.06  sat_num_of_non_cyclic_types:            0
% 2.21/1.06  sat_guarded_non_collapsed_types:        0
% 2.21/1.06  num_pure_diseq_elim:                    0
% 2.21/1.06  simp_replaced_by:                       0
% 2.21/1.06  res_preprocessed:                       96
% 2.21/1.06  prep_upred:                             0
% 2.21/1.06  prep_unflattend:                        11
% 2.21/1.06  smt_new_axioms:                         0
% 2.21/1.06  pred_elim_cands:                        3
% 2.21/1.06  pred_elim:                              2
% 2.21/1.06  pred_elim_cl:                           3
% 2.21/1.06  pred_elim_cycles:                       4
% 2.21/1.06  merged_defs:                            2
% 2.21/1.06  merged_defs_ncl:                        0
% 2.21/1.06  bin_hyper_res:                          2
% 2.21/1.06  prep_cycles:                            4
% 2.21/1.06  pred_elim_time:                         0.004
% 2.21/1.06  splitting_time:                         0.
% 2.21/1.06  sem_filter_time:                        0.
% 2.21/1.06  monotx_time:                            0.
% 2.21/1.06  subtype_inf_time:                       0.001
% 2.21/1.06  
% 2.21/1.06  ------ Problem properties
% 2.21/1.06  
% 2.21/1.06  clauses:                                17
% 2.21/1.06  conjectures:                            2
% 2.21/1.06  epr:                                    5
% 2.21/1.06  horn:                                   17
% 2.21/1.06  ground:                                 5
% 2.21/1.06  unary:                                  5
% 2.21/1.06  binary:                                 7
% 2.21/1.06  lits:                                   35
% 2.21/1.06  lits_eq:                                10
% 2.21/1.06  fd_pure:                                0
% 2.21/1.06  fd_pseudo:                              0
% 2.21/1.06  fd_cond:                                1
% 2.21/1.06  fd_pseudo_cond:                         0
% 2.21/1.06  ac_symbols:                             0
% 2.21/1.06  
% 2.21/1.06  ------ Propositional Solver
% 2.21/1.06  
% 2.21/1.06  prop_solver_calls:                      34
% 2.21/1.06  prop_fast_solver_calls:                 560
% 2.21/1.06  smt_solver_calls:                       0
% 2.21/1.06  smt_fast_solver_calls:                  0
% 2.21/1.06  prop_num_of_clauses:                    1412
% 2.21/1.06  prop_preprocess_simplified:             4577
% 2.21/1.06  prop_fo_subsumed:                       5
% 2.21/1.06  prop_solver_time:                       0.
% 2.21/1.06  smt_solver_time:                        0.
% 2.21/1.06  smt_fast_solver_time:                   0.
% 2.21/1.06  prop_fast_solver_time:                  0.
% 2.21/1.06  prop_unsat_core_time:                   0.
% 2.21/1.06  
% 2.21/1.06  ------ QBF
% 2.21/1.06  
% 2.21/1.06  qbf_q_res:                              0
% 2.21/1.06  qbf_num_tautologies:                    0
% 2.21/1.06  qbf_prep_cycles:                        0
% 2.21/1.06  
% 2.21/1.06  ------ BMC1
% 2.21/1.06  
% 2.21/1.06  bmc1_current_bound:                     -1
% 2.21/1.06  bmc1_last_solved_bound:                 -1
% 2.21/1.06  bmc1_unsat_core_size:                   -1
% 2.21/1.06  bmc1_unsat_core_parents_size:           -1
% 2.21/1.06  bmc1_merge_next_fun:                    0
% 2.21/1.06  bmc1_unsat_core_clauses_time:           0.
% 2.21/1.06  
% 2.21/1.06  ------ Instantiation
% 2.21/1.06  
% 2.21/1.06  inst_num_of_clauses:                    539
% 2.21/1.06  inst_num_in_passive:                    313
% 2.21/1.06  inst_num_in_active:                     221
% 2.21/1.06  inst_num_in_unprocessed:                4
% 2.21/1.06  inst_num_of_loops:                      285
% 2.21/1.06  inst_num_of_learning_restarts:          0
% 2.21/1.06  inst_num_moves_active_passive:          57
% 2.21/1.06  inst_lit_activity:                      0
% 2.21/1.06  inst_lit_activity_moves:                0
% 2.21/1.06  inst_num_tautologies:                   0
% 2.21/1.06  inst_num_prop_implied:                  0
% 2.21/1.06  inst_num_existing_simplified:           0
% 2.21/1.06  inst_num_eq_res_simplified:             0
% 2.21/1.06  inst_num_child_elim:                    0
% 2.21/1.06  inst_num_of_dismatching_blockings:      225
% 2.21/1.06  inst_num_of_non_proper_insts:           652
% 2.21/1.06  inst_num_of_duplicates:                 0
% 2.21/1.06  inst_inst_num_from_inst_to_res:         0
% 2.21/1.06  inst_dismatching_checking_time:         0.
% 2.21/1.06  
% 2.21/1.06  ------ Resolution
% 2.21/1.06  
% 2.21/1.06  res_num_of_clauses:                     0
% 2.21/1.06  res_num_in_passive:                     0
% 2.21/1.06  res_num_in_active:                      0
% 2.21/1.06  res_num_of_loops:                       100
% 2.21/1.06  res_forward_subset_subsumed:            76
% 2.21/1.06  res_backward_subset_subsumed:           0
% 2.21/1.06  res_forward_subsumed:                   0
% 2.21/1.06  res_backward_subsumed:                  0
% 2.21/1.06  res_forward_subsumption_resolution:     0
% 2.21/1.06  res_backward_subsumption_resolution:    0
% 2.21/1.06  res_clause_to_clause_subsumption:       323
% 2.21/1.06  res_orphan_elimination:                 0
% 2.21/1.06  res_tautology_del:                      134
% 2.21/1.06  res_num_eq_res_simplified:              0
% 2.21/1.06  res_num_sel_changes:                    0
% 2.21/1.06  res_moves_from_active_to_pass:          0
% 2.21/1.06  
% 2.21/1.06  ------ Superposition
% 2.21/1.06  
% 2.21/1.06  sup_time_total:                         0.
% 2.21/1.06  sup_time_generating:                    0.
% 2.21/1.06  sup_time_sim_full:                      0.
% 2.21/1.06  sup_time_sim_immed:                     0.
% 2.21/1.06  
% 2.21/1.06  sup_num_of_clauses:                     105
% 2.21/1.06  sup_num_in_active:                      53
% 2.21/1.06  sup_num_in_passive:                     52
% 2.21/1.06  sup_num_of_loops:                       56
% 2.21/1.06  sup_fw_superposition:                   85
% 2.21/1.06  sup_bw_superposition:                   27
% 2.21/1.06  sup_immediate_simplified:               29
% 2.21/1.06  sup_given_eliminated:                   2
% 2.21/1.06  comparisons_done:                       0
% 2.21/1.06  comparisons_avoided:                    0
% 2.21/1.06  
% 2.21/1.06  ------ Simplifications
% 2.21/1.06  
% 2.21/1.06  
% 2.21/1.06  sim_fw_subset_subsumed:                 4
% 2.21/1.06  sim_bw_subset_subsumed:                 0
% 2.21/1.06  sim_fw_subsumed:                        1
% 2.21/1.06  sim_bw_subsumed:                        2
% 2.21/1.06  sim_fw_subsumption_res:                 0
% 2.21/1.06  sim_bw_subsumption_res:                 0
% 2.21/1.06  sim_tautology_del:                      2
% 2.21/1.06  sim_eq_tautology_del:                   12
% 2.21/1.06  sim_eq_res_simp:                        0
% 2.21/1.06  sim_fw_demodulated:                     2
% 2.21/1.06  sim_bw_demodulated:                     3
% 2.21/1.06  sim_light_normalised:                   22
% 2.21/1.06  sim_joinable_taut:                      0
% 2.21/1.06  sim_joinable_simp:                      0
% 2.21/1.06  sim_ac_normalised:                      0
% 2.21/1.06  sim_smt_subsumption:                    0
% 2.21/1.06  
%------------------------------------------------------------------------------
