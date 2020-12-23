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
% DateTime   : Thu Dec  3 11:54:23 EST 2020

% Result     : Theorem 7.12s
% Output     : CNFRefutation 7.12s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 776 expanded)
%              Number of clauses        :   84 ( 317 expanded)
%              Number of leaves         :   14 ( 142 expanded)
%              Depth                    :   23
%              Number of atoms          :  250 (1678 expanded)
%              Number of equality atoms :  138 ( 673 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0)
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f28,plain,
    ( ? [X0,X1,X2] :
        ( k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0)
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0)
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0)
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f28])).

fof(f43,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k2_wellord1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f35,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f34,f33])).

fof(f49,plain,(
    ! [X0] :
      ( k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f35,f46])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f48,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f32,f33,f33])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f31,f46])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(k8_relat_1(X0,X1),X0) = k2_wellord1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_relat_1(k8_relat_1(X0,X1),X0) = k2_wellord1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k7_relat_1(k8_relat_1(X0,X1),X0) = k2_wellord1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)
        & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)
        & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1)) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f44,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f45,plain,(
    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_13,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_145,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_418,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_145])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k2_wellord1(X0,X1)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_152,plain,
    ( ~ v1_relat_1(X0_41)
    | v1_relat_1(k2_wellord1(X0_41,X0_42)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_412,plain,
    ( v1_relat_1(X0_41) != iProver_top
    | v1_relat_1(k2_wellord1(X0_41,X0_42)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_152])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_155,plain,
    ( ~ v1_relat_1(X0_41)
    | k3_tarski(k1_enumset1(k1_relat_1(X0_41),k1_relat_1(X0_41),k2_relat_1(X0_41))) = k3_relat_1(X0_41) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_409,plain,
    ( k3_tarski(k1_enumset1(k1_relat_1(X0_41),k1_relat_1(X0_41),k2_relat_1(X0_41))) = k3_relat_1(X0_41)
    | v1_relat_1(X0_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_155])).

cnf(c_863,plain,
    ( k3_tarski(k1_enumset1(k1_relat_1(k2_wellord1(X0_41,X0_42)),k1_relat_1(k2_wellord1(X0_41,X0_42)),k2_relat_1(k2_wellord1(X0_41,X0_42)))) = k3_relat_1(k2_wellord1(X0_41,X0_42))
    | v1_relat_1(X0_41) != iProver_top ),
    inference(superposition,[status(thm)],[c_412,c_409])).

cnf(c_6325,plain,
    ( k3_tarski(k1_enumset1(k1_relat_1(k2_wellord1(sK2,X0_42)),k1_relat_1(k2_wellord1(sK2,X0_42)),k2_relat_1(k2_wellord1(sK2,X0_42)))) = k3_relat_1(k2_wellord1(sK2,X0_42)) ),
    inference(superposition,[status(thm)],[c_418,c_863])).

cnf(c_2,plain,
    ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_156,plain,
    ( k1_enumset1(X0_42,X0_42,X1_42) = k1_enumset1(X1_42,X1_42,X0_42) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1,plain,
    ( r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_157,plain,
    ( r1_tarski(X0_42,k3_tarski(k1_enumset1(X0_42,X0_42,X1_42))) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_408,plain,
    ( r1_tarski(X0_42,k3_tarski(k1_enumset1(X0_42,X0_42,X1_42))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_157])).

cnf(c_592,plain,
    ( r1_tarski(X0_42,k3_tarski(k1_enumset1(X1_42,X1_42,X0_42))) = iProver_top ),
    inference(superposition,[status(thm)],[c_156,c_408])).

cnf(c_6936,plain,
    ( r1_tarski(k2_relat_1(k2_wellord1(sK2,X0_42)),k3_relat_1(k2_wellord1(sK2,X0_42))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6325,c_592])).

cnf(c_862,plain,
    ( k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k2_relat_1(sK2))) = k3_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_418,c_409])).

cnf(c_1024,plain,
    ( r1_tarski(k2_relat_1(sK2),k3_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_862,c_592])).

cnf(c_4,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k8_relat_1(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_154,plain,
    ( ~ r1_tarski(k2_relat_1(X0_41),X0_42)
    | ~ v1_relat_1(X0_41)
    | k8_relat_1(X0_42,X0_41) = X0_41 ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_410,plain,
    ( k8_relat_1(X0_42,X0_41) = X0_41
    | r1_tarski(k2_relat_1(X0_41),X0_42) != iProver_top
    | v1_relat_1(X0_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_154])).

cnf(c_1356,plain,
    ( k8_relat_1(k3_relat_1(sK2),sK2) = sK2
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1024,c_410])).

cnf(c_14,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1541,plain,
    ( k8_relat_1(k3_relat_1(sK2),sK2) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1356,c_14])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(k8_relat_1(X1,X0),X1) = k2_wellord1(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_151,plain,
    ( ~ v1_relat_1(X0_41)
    | k7_relat_1(k8_relat_1(X0_42,X0_41),X0_42) = k2_wellord1(X0_41,X0_42) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_413,plain,
    ( k7_relat_1(k8_relat_1(X0_42,X0_41),X0_42) = k2_wellord1(X0_41,X0_42)
    | v1_relat_1(X0_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_151])).

cnf(c_751,plain,
    ( k7_relat_1(k8_relat_1(X0_42,sK2),X0_42) = k2_wellord1(sK2,X0_42) ),
    inference(superposition,[status(thm)],[c_418,c_413])).

cnf(c_1544,plain,
    ( k2_wellord1(sK2,k3_relat_1(sK2)) = k7_relat_1(sK2,k3_relat_1(sK2)) ),
    inference(superposition,[status(thm)],[c_1541,c_751])).

cnf(c_1023,plain,
    ( r1_tarski(k1_relat_1(sK2),k3_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_862,c_408])).

cnf(c_5,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_153,plain,
    ( ~ r1_tarski(k1_relat_1(X0_41),X0_42)
    | ~ v1_relat_1(X0_41)
    | k7_relat_1(X0_41,X0_42) = X0_41 ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_411,plain,
    ( k7_relat_1(X0_41,X0_42) = X0_41
    | r1_tarski(k1_relat_1(X0_41),X0_42) != iProver_top
    | v1_relat_1(X0_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_153])).

cnf(c_1520,plain,
    ( k7_relat_1(sK2,k3_relat_1(sK2)) = sK2
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1023,c_411])).

cnf(c_1613,plain,
    ( k7_relat_1(sK2,k3_relat_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1520,c_14])).

cnf(c_1706,plain,
    ( k2_wellord1(sK2,k3_relat_1(sK2)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_1544,c_1613])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | k2_wellord1(k2_wellord1(X0,X1),X2) = k2_wellord1(k2_wellord1(X0,X2),X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_148,plain,
    ( ~ v1_relat_1(X0_41)
    | k2_wellord1(k2_wellord1(X0_41,X0_42),X1_42) = k2_wellord1(k2_wellord1(X0_41,X1_42),X0_42) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_416,plain,
    ( k2_wellord1(k2_wellord1(X0_41,X0_42),X1_42) = k2_wellord1(k2_wellord1(X0_41,X1_42),X0_42)
    | v1_relat_1(X0_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_148])).

cnf(c_935,plain,
    ( k2_wellord1(k2_wellord1(sK2,X0_42),X1_42) = k2_wellord1(k2_wellord1(sK2,X1_42),X0_42) ),
    inference(superposition,[status(thm)],[c_418,c_416])).

cnf(c_9,plain,
    ( r1_tarski(k3_relat_1(k2_wellord1(X0,X1)),k3_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_149,plain,
    ( r1_tarski(k3_relat_1(k2_wellord1(X0_41,X0_42)),k3_relat_1(X0_41))
    | ~ v1_relat_1(X0_41) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_415,plain,
    ( r1_tarski(k3_relat_1(k2_wellord1(X0_41,X0_42)),k3_relat_1(X0_41)) = iProver_top
    | v1_relat_1(X0_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_149])).

cnf(c_1036,plain,
    ( r1_tarski(k3_relat_1(k2_wellord1(k2_wellord1(sK2,X0_42),X1_42)),k3_relat_1(k2_wellord1(sK2,X1_42))) = iProver_top
    | v1_relat_1(k2_wellord1(sK2,X1_42)) != iProver_top ),
    inference(superposition,[status(thm)],[c_935,c_415])).

cnf(c_8,plain,
    ( r1_tarski(k3_relat_1(k2_wellord1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_150,plain,
    ( r1_tarski(k3_relat_1(k2_wellord1(X0_41,X0_42)),X0_42)
    | ~ v1_relat_1(X0_41) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_414,plain,
    ( r1_tarski(k3_relat_1(k2_wellord1(X0_41,X0_42)),X0_42) = iProver_top
    | v1_relat_1(X0_41) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_150])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_158,plain,
    ( ~ r1_tarski(X0_42,X1_42)
    | ~ r1_tarski(X2_42,X0_42)
    | r1_tarski(X2_42,X1_42) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_407,plain,
    ( r1_tarski(X0_42,X1_42) != iProver_top
    | r1_tarski(X2_42,X0_42) != iProver_top
    | r1_tarski(X2_42,X1_42) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_158])).

cnf(c_721,plain,
    ( r1_tarski(X0_42,X1_42) = iProver_top
    | r1_tarski(X0_42,k3_relat_1(k2_wellord1(X0_41,X1_42))) != iProver_top
    | v1_relat_1(X0_41) != iProver_top ),
    inference(superposition,[status(thm)],[c_414,c_407])).

cnf(c_2365,plain,
    ( r1_tarski(k3_relat_1(k2_wellord1(k2_wellord1(sK2,X0_42),X1_42)),X1_42) = iProver_top
    | v1_relat_1(k2_wellord1(sK2,X1_42)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1036,c_721])).

cnf(c_3524,plain,
    ( v1_relat_1(k2_wellord1(sK2,X1_42)) != iProver_top
    | r1_tarski(k3_relat_1(k2_wellord1(k2_wellord1(sK2,X0_42),X1_42)),X1_42) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2365,c_14])).

cnf(c_3525,plain,
    ( r1_tarski(k3_relat_1(k2_wellord1(k2_wellord1(sK2,X0_42),X1_42)),X1_42) = iProver_top
    | v1_relat_1(k2_wellord1(sK2,X1_42)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3524])).

cnf(c_12,negated_conjecture,
    ( r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_146,negated_conjecture,
    ( r1_tarski(sK0,sK1) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_417,plain,
    ( r1_tarski(sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_146])).

cnf(c_720,plain,
    ( r1_tarski(X0_42,sK1) = iProver_top
    | r1_tarski(X0_42,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_417,c_407])).

cnf(c_3535,plain,
    ( r1_tarski(k3_relat_1(k2_wellord1(k2_wellord1(sK2,X0_42),sK0)),sK1) = iProver_top
    | v1_relat_1(k2_wellord1(sK2,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3525,c_720])).

cnf(c_196,plain,
    ( v1_relat_1(X0_41) != iProver_top
    | v1_relat_1(k2_wellord1(X0_41,X0_42)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_152])).

cnf(c_198,plain,
    ( v1_relat_1(k2_wellord1(sK2,sK0)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_196])).

cnf(c_1118,plain,
    ( r1_tarski(k3_relat_1(k2_wellord1(X0_41,sK0)),sK1) = iProver_top
    | v1_relat_1(X0_41) != iProver_top ),
    inference(superposition,[status(thm)],[c_414,c_720])).

cnf(c_1335,plain,
    ( r1_tarski(X0_42,k3_relat_1(k2_wellord1(X0_41,sK0))) != iProver_top
    | r1_tarski(X0_42,sK1) = iProver_top
    | v1_relat_1(X0_41) != iProver_top ),
    inference(superposition,[status(thm)],[c_1118,c_407])).

cnf(c_3166,plain,
    ( r1_tarski(k3_relat_1(k2_wellord1(k2_wellord1(sK2,X0_42),sK0)),sK1) = iProver_top
    | v1_relat_1(k2_wellord1(sK2,sK0)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1036,c_1335])).

cnf(c_4250,plain,
    ( r1_tarski(k3_relat_1(k2_wellord1(k2_wellord1(sK2,X0_42),sK0)),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3535,c_14,c_198,c_3166])).

cnf(c_4259,plain,
    ( r1_tarski(k3_relat_1(k2_wellord1(sK2,sK0)),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1706,c_4250])).

cnf(c_4719,plain,
    ( r1_tarski(X0_42,k3_relat_1(k2_wellord1(sK2,sK0))) != iProver_top
    | r1_tarski(X0_42,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_4259,c_407])).

cnf(c_7182,plain,
    ( r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_6936,c_4719])).

cnf(c_18208,plain,
    ( k8_relat_1(sK1,k2_wellord1(sK2,sK0)) = k2_wellord1(sK2,sK0)
    | v1_relat_1(k2_wellord1(sK2,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7182,c_410])).

cnf(c_19913,plain,
    ( k8_relat_1(sK1,k2_wellord1(sK2,sK0)) = k2_wellord1(sK2,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18208,c_14,c_198])).

cnf(c_752,plain,
    ( k7_relat_1(k8_relat_1(X0_42,k2_wellord1(X0_41,X1_42)),X0_42) = k2_wellord1(k2_wellord1(X0_41,X1_42),X0_42)
    | v1_relat_1(X0_41) != iProver_top ),
    inference(superposition,[status(thm)],[c_412,c_413])).

cnf(c_3684,plain,
    ( k7_relat_1(k8_relat_1(X0_42,k2_wellord1(sK2,X1_42)),X0_42) = k2_wellord1(k2_wellord1(sK2,X1_42),X0_42) ),
    inference(superposition,[status(thm)],[c_418,c_752])).

cnf(c_19916,plain,
    ( k2_wellord1(k2_wellord1(sK2,sK0),sK1) = k7_relat_1(k2_wellord1(sK2,sK0),sK1) ),
    inference(superposition,[status(thm)],[c_19913,c_3684])).

cnf(c_6934,plain,
    ( r1_tarski(k1_relat_1(k2_wellord1(sK2,X0_42)),k3_relat_1(k2_wellord1(sK2,X0_42))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6325,c_408])).

cnf(c_7130,plain,
    ( r1_tarski(k1_relat_1(k2_wellord1(sK2,sK0)),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_6934,c_4719])).

cnf(c_7749,plain,
    ( k7_relat_1(k2_wellord1(sK2,sK0),sK1) = k2_wellord1(sK2,sK0)
    | v1_relat_1(k2_wellord1(sK2,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7130,c_411])).

cnf(c_11214,plain,
    ( k7_relat_1(k2_wellord1(sK2,sK0),sK1) = k2_wellord1(sK2,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7749,c_14,c_198])).

cnf(c_19917,plain,
    ( k2_wellord1(k2_wellord1(sK2,sK0),sK1) = k2_wellord1(sK2,sK0) ),
    inference(light_normalisation,[status(thm)],[c_19916,c_11214])).

cnf(c_11,negated_conjecture,
    ( k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_147,negated_conjecture,
    ( k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1032,plain,
    ( k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(sK2,sK0) ),
    inference(demodulation,[status(thm)],[c_935,c_147])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_19917,c_1032])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:25:32 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.35  % Running in FOF mode
% 7.12/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.12/1.50  
% 7.12/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.12/1.50  
% 7.12/1.50  ------  iProver source info
% 7.12/1.50  
% 7.12/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.12/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.12/1.50  git: non_committed_changes: false
% 7.12/1.50  git: last_make_outside_of_git: false
% 7.12/1.50  
% 7.12/1.50  ------ 
% 7.12/1.50  
% 7.12/1.50  ------ Input Options
% 7.12/1.50  
% 7.12/1.50  --out_options                           all
% 7.12/1.50  --tptp_safe_out                         true
% 7.12/1.50  --problem_path                          ""
% 7.12/1.50  --include_path                          ""
% 7.12/1.50  --clausifier                            res/vclausify_rel
% 7.12/1.50  --clausifier_options                    --mode clausify
% 7.12/1.50  --stdin                                 false
% 7.12/1.50  --stats_out                             all
% 7.12/1.50  
% 7.12/1.50  ------ General Options
% 7.12/1.50  
% 7.12/1.50  --fof                                   false
% 7.12/1.50  --time_out_real                         305.
% 7.12/1.50  --time_out_virtual                      -1.
% 7.12/1.50  --symbol_type_check                     false
% 7.12/1.50  --clausify_out                          false
% 7.12/1.50  --sig_cnt_out                           false
% 7.12/1.50  --trig_cnt_out                          false
% 7.12/1.50  --trig_cnt_out_tolerance                1.
% 7.12/1.50  --trig_cnt_out_sk_spl                   false
% 7.12/1.50  --abstr_cl_out                          false
% 7.12/1.50  
% 7.12/1.50  ------ Global Options
% 7.12/1.50  
% 7.12/1.50  --schedule                              default
% 7.12/1.50  --add_important_lit                     false
% 7.12/1.50  --prop_solver_per_cl                    1000
% 7.12/1.50  --min_unsat_core                        false
% 7.12/1.50  --soft_assumptions                      false
% 7.12/1.50  --soft_lemma_size                       3
% 7.12/1.50  --prop_impl_unit_size                   0
% 7.12/1.50  --prop_impl_unit                        []
% 7.12/1.50  --share_sel_clauses                     true
% 7.12/1.50  --reset_solvers                         false
% 7.12/1.50  --bc_imp_inh                            [conj_cone]
% 7.12/1.50  --conj_cone_tolerance                   3.
% 7.12/1.50  --extra_neg_conj                        none
% 7.12/1.50  --large_theory_mode                     true
% 7.12/1.50  --prolific_symb_bound                   200
% 7.12/1.50  --lt_threshold                          2000
% 7.12/1.50  --clause_weak_htbl                      true
% 7.12/1.50  --gc_record_bc_elim                     false
% 7.12/1.50  
% 7.12/1.50  ------ Preprocessing Options
% 7.12/1.50  
% 7.12/1.50  --preprocessing_flag                    true
% 7.12/1.50  --time_out_prep_mult                    0.1
% 7.12/1.50  --splitting_mode                        input
% 7.12/1.50  --splitting_grd                         true
% 7.12/1.50  --splitting_cvd                         false
% 7.12/1.50  --splitting_cvd_svl                     false
% 7.12/1.50  --splitting_nvd                         32
% 7.12/1.50  --sub_typing                            true
% 7.12/1.50  --prep_gs_sim                           true
% 7.12/1.50  --prep_unflatten                        true
% 7.12/1.50  --prep_res_sim                          true
% 7.12/1.50  --prep_upred                            true
% 7.12/1.50  --prep_sem_filter                       exhaustive
% 7.12/1.50  --prep_sem_filter_out                   false
% 7.12/1.50  --pred_elim                             true
% 7.12/1.50  --res_sim_input                         true
% 7.12/1.50  --eq_ax_congr_red                       true
% 7.12/1.50  --pure_diseq_elim                       true
% 7.12/1.50  --brand_transform                       false
% 7.12/1.50  --non_eq_to_eq                          false
% 7.12/1.50  --prep_def_merge                        true
% 7.12/1.50  --prep_def_merge_prop_impl              false
% 7.12/1.51  --prep_def_merge_mbd                    true
% 7.12/1.51  --prep_def_merge_tr_red                 false
% 7.12/1.51  --prep_def_merge_tr_cl                  false
% 7.12/1.51  --smt_preprocessing                     true
% 7.12/1.51  --smt_ac_axioms                         fast
% 7.12/1.51  --preprocessed_out                      false
% 7.12/1.51  --preprocessed_stats                    false
% 7.12/1.51  
% 7.12/1.51  ------ Abstraction refinement Options
% 7.12/1.51  
% 7.12/1.51  --abstr_ref                             []
% 7.12/1.51  --abstr_ref_prep                        false
% 7.12/1.51  --abstr_ref_until_sat                   false
% 7.12/1.51  --abstr_ref_sig_restrict                funpre
% 7.12/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.12/1.51  --abstr_ref_under                       []
% 7.12/1.51  
% 7.12/1.51  ------ SAT Options
% 7.12/1.51  
% 7.12/1.51  --sat_mode                              false
% 7.12/1.51  --sat_fm_restart_options                ""
% 7.12/1.51  --sat_gr_def                            false
% 7.12/1.51  --sat_epr_types                         true
% 7.12/1.51  --sat_non_cyclic_types                  false
% 7.12/1.51  --sat_finite_models                     false
% 7.12/1.51  --sat_fm_lemmas                         false
% 7.12/1.51  --sat_fm_prep                           false
% 7.12/1.51  --sat_fm_uc_incr                        true
% 7.12/1.51  --sat_out_model                         small
% 7.12/1.51  --sat_out_clauses                       false
% 7.12/1.51  
% 7.12/1.51  ------ QBF Options
% 7.12/1.51  
% 7.12/1.51  --qbf_mode                              false
% 7.12/1.51  --qbf_elim_univ                         false
% 7.12/1.51  --qbf_dom_inst                          none
% 7.12/1.51  --qbf_dom_pre_inst                      false
% 7.12/1.51  --qbf_sk_in                             false
% 7.12/1.51  --qbf_pred_elim                         true
% 7.12/1.51  --qbf_split                             512
% 7.12/1.51  
% 7.12/1.51  ------ BMC1 Options
% 7.12/1.51  
% 7.12/1.51  --bmc1_incremental                      false
% 7.12/1.51  --bmc1_axioms                           reachable_all
% 7.12/1.51  --bmc1_min_bound                        0
% 7.12/1.51  --bmc1_max_bound                        -1
% 7.12/1.51  --bmc1_max_bound_default                -1
% 7.12/1.51  --bmc1_symbol_reachability              true
% 7.12/1.51  --bmc1_property_lemmas                  false
% 7.12/1.51  --bmc1_k_induction                      false
% 7.12/1.51  --bmc1_non_equiv_states                 false
% 7.12/1.51  --bmc1_deadlock                         false
% 7.12/1.51  --bmc1_ucm                              false
% 7.12/1.51  --bmc1_add_unsat_core                   none
% 7.12/1.51  --bmc1_unsat_core_children              false
% 7.12/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.12/1.51  --bmc1_out_stat                         full
% 7.12/1.51  --bmc1_ground_init                      false
% 7.12/1.51  --bmc1_pre_inst_next_state              false
% 7.12/1.51  --bmc1_pre_inst_state                   false
% 7.12/1.51  --bmc1_pre_inst_reach_state             false
% 7.12/1.51  --bmc1_out_unsat_core                   false
% 7.12/1.51  --bmc1_aig_witness_out                  false
% 7.12/1.51  --bmc1_verbose                          false
% 7.12/1.51  --bmc1_dump_clauses_tptp                false
% 7.12/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.12/1.51  --bmc1_dump_file                        -
% 7.12/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.12/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.12/1.51  --bmc1_ucm_extend_mode                  1
% 7.12/1.51  --bmc1_ucm_init_mode                    2
% 7.12/1.51  --bmc1_ucm_cone_mode                    none
% 7.12/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.12/1.51  --bmc1_ucm_relax_model                  4
% 7.12/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.12/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.12/1.51  --bmc1_ucm_layered_model                none
% 7.12/1.51  --bmc1_ucm_max_lemma_size               10
% 7.12/1.51  
% 7.12/1.51  ------ AIG Options
% 7.12/1.51  
% 7.12/1.51  --aig_mode                              false
% 7.12/1.51  
% 7.12/1.51  ------ Instantiation Options
% 7.12/1.51  
% 7.12/1.51  --instantiation_flag                    true
% 7.12/1.51  --inst_sos_flag                         false
% 7.12/1.51  --inst_sos_phase                        true
% 7.12/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.12/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.12/1.51  --inst_lit_sel_side                     num_symb
% 7.12/1.51  --inst_solver_per_active                1400
% 7.12/1.51  --inst_solver_calls_frac                1.
% 7.12/1.51  --inst_passive_queue_type               priority_queues
% 7.12/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.12/1.51  --inst_passive_queues_freq              [25;2]
% 7.12/1.51  --inst_dismatching                      true
% 7.12/1.51  --inst_eager_unprocessed_to_passive     true
% 7.12/1.51  --inst_prop_sim_given                   true
% 7.12/1.51  --inst_prop_sim_new                     false
% 7.12/1.51  --inst_subs_new                         false
% 7.12/1.51  --inst_eq_res_simp                      false
% 7.12/1.51  --inst_subs_given                       false
% 7.12/1.51  --inst_orphan_elimination               true
% 7.12/1.51  --inst_learning_loop_flag               true
% 7.12/1.51  --inst_learning_start                   3000
% 7.12/1.51  --inst_learning_factor                  2
% 7.12/1.51  --inst_start_prop_sim_after_learn       3
% 7.12/1.51  --inst_sel_renew                        solver
% 7.12/1.51  --inst_lit_activity_flag                true
% 7.12/1.51  --inst_restr_to_given                   false
% 7.12/1.51  --inst_activity_threshold               500
% 7.12/1.51  --inst_out_proof                        true
% 7.12/1.51  
% 7.12/1.51  ------ Resolution Options
% 7.12/1.51  
% 7.12/1.51  --resolution_flag                       true
% 7.12/1.51  --res_lit_sel                           adaptive
% 7.12/1.51  --res_lit_sel_side                      none
% 7.12/1.51  --res_ordering                          kbo
% 7.12/1.51  --res_to_prop_solver                    active
% 7.12/1.51  --res_prop_simpl_new                    false
% 7.12/1.51  --res_prop_simpl_given                  true
% 7.12/1.51  --res_passive_queue_type                priority_queues
% 7.12/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.12/1.51  --res_passive_queues_freq               [15;5]
% 7.12/1.51  --res_forward_subs                      full
% 7.12/1.51  --res_backward_subs                     full
% 7.12/1.51  --res_forward_subs_resolution           true
% 7.12/1.51  --res_backward_subs_resolution          true
% 7.12/1.51  --res_orphan_elimination                true
% 7.12/1.51  --res_time_limit                        2.
% 7.12/1.51  --res_out_proof                         true
% 7.12/1.51  
% 7.12/1.51  ------ Superposition Options
% 7.12/1.51  
% 7.12/1.51  --superposition_flag                    true
% 7.12/1.51  --sup_passive_queue_type                priority_queues
% 7.12/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.12/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.12/1.51  --demod_completeness_check              fast
% 7.12/1.51  --demod_use_ground                      true
% 7.12/1.51  --sup_to_prop_solver                    passive
% 7.12/1.51  --sup_prop_simpl_new                    true
% 7.12/1.51  --sup_prop_simpl_given                  true
% 7.12/1.51  --sup_fun_splitting                     false
% 7.12/1.51  --sup_smt_interval                      50000
% 7.12/1.51  
% 7.12/1.51  ------ Superposition Simplification Setup
% 7.12/1.51  
% 7.12/1.51  --sup_indices_passive                   []
% 7.12/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.12/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.12/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.12/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.12/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.12/1.51  --sup_full_bw                           [BwDemod]
% 7.12/1.51  --sup_immed_triv                        [TrivRules]
% 7.12/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.12/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.12/1.51  --sup_immed_bw_main                     []
% 7.12/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.12/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.12/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.12/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.12/1.51  
% 7.12/1.51  ------ Combination Options
% 7.12/1.51  
% 7.12/1.51  --comb_res_mult                         3
% 7.12/1.51  --comb_sup_mult                         2
% 7.12/1.51  --comb_inst_mult                        10
% 7.12/1.51  
% 7.12/1.51  ------ Debug Options
% 7.12/1.51  
% 7.12/1.51  --dbg_backtrace                         false
% 7.12/1.51  --dbg_dump_prop_clauses                 false
% 7.12/1.51  --dbg_dump_prop_clauses_file            -
% 7.12/1.51  --dbg_out_stat                          false
% 7.12/1.51  ------ Parsing...
% 7.12/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.12/1.51  
% 7.12/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.12/1.51  
% 7.12/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.12/1.51  
% 7.12/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.12/1.51  ------ Proving...
% 7.12/1.51  ------ Problem Properties 
% 7.12/1.51  
% 7.12/1.51  
% 7.12/1.51  clauses                                 14
% 7.12/1.51  conjectures                             3
% 7.12/1.51  EPR                                     3
% 7.12/1.51  Horn                                    14
% 7.12/1.51  unary                                   5
% 7.12/1.51  binary                                  6
% 7.12/1.51  lits                                    26
% 7.12/1.51  lits eq                                 7
% 7.12/1.51  fd_pure                                 0
% 7.12/1.51  fd_pseudo                               0
% 7.12/1.51  fd_cond                                 0
% 7.12/1.51  fd_pseudo_cond                          0
% 7.12/1.51  AC symbols                              0
% 7.12/1.51  
% 7.12/1.51  ------ Schedule dynamic 5 is on 
% 7.12/1.51  
% 7.12/1.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.12/1.51  
% 7.12/1.51  
% 7.12/1.51  ------ 
% 7.12/1.51  Current options:
% 7.12/1.51  ------ 
% 7.12/1.51  
% 7.12/1.51  ------ Input Options
% 7.12/1.51  
% 7.12/1.51  --out_options                           all
% 7.12/1.51  --tptp_safe_out                         true
% 7.12/1.51  --problem_path                          ""
% 7.12/1.51  --include_path                          ""
% 7.12/1.51  --clausifier                            res/vclausify_rel
% 7.12/1.51  --clausifier_options                    --mode clausify
% 7.12/1.51  --stdin                                 false
% 7.12/1.51  --stats_out                             all
% 7.12/1.51  
% 7.12/1.51  ------ General Options
% 7.12/1.51  
% 7.12/1.51  --fof                                   false
% 7.12/1.51  --time_out_real                         305.
% 7.12/1.51  --time_out_virtual                      -1.
% 7.12/1.51  --symbol_type_check                     false
% 7.12/1.51  --clausify_out                          false
% 7.12/1.51  --sig_cnt_out                           false
% 7.12/1.51  --trig_cnt_out                          false
% 7.12/1.51  --trig_cnt_out_tolerance                1.
% 7.12/1.51  --trig_cnt_out_sk_spl                   false
% 7.12/1.51  --abstr_cl_out                          false
% 7.12/1.51  
% 7.12/1.51  ------ Global Options
% 7.12/1.51  
% 7.12/1.51  --schedule                              default
% 7.12/1.51  --add_important_lit                     false
% 7.12/1.51  --prop_solver_per_cl                    1000
% 7.12/1.51  --min_unsat_core                        false
% 7.12/1.51  --soft_assumptions                      false
% 7.12/1.51  --soft_lemma_size                       3
% 7.12/1.51  --prop_impl_unit_size                   0
% 7.12/1.51  --prop_impl_unit                        []
% 7.12/1.51  --share_sel_clauses                     true
% 7.12/1.51  --reset_solvers                         false
% 7.12/1.51  --bc_imp_inh                            [conj_cone]
% 7.12/1.51  --conj_cone_tolerance                   3.
% 7.12/1.51  --extra_neg_conj                        none
% 7.12/1.51  --large_theory_mode                     true
% 7.12/1.51  --prolific_symb_bound                   200
% 7.12/1.51  --lt_threshold                          2000
% 7.12/1.51  --clause_weak_htbl                      true
% 7.12/1.51  --gc_record_bc_elim                     false
% 7.12/1.51  
% 7.12/1.51  ------ Preprocessing Options
% 7.12/1.51  
% 7.12/1.51  --preprocessing_flag                    true
% 7.12/1.51  --time_out_prep_mult                    0.1
% 7.12/1.51  --splitting_mode                        input
% 7.12/1.51  --splitting_grd                         true
% 7.12/1.51  --splitting_cvd                         false
% 7.12/1.51  --splitting_cvd_svl                     false
% 7.12/1.51  --splitting_nvd                         32
% 7.12/1.51  --sub_typing                            true
% 7.12/1.51  --prep_gs_sim                           true
% 7.12/1.51  --prep_unflatten                        true
% 7.12/1.51  --prep_res_sim                          true
% 7.12/1.51  --prep_upred                            true
% 7.12/1.51  --prep_sem_filter                       exhaustive
% 7.12/1.51  --prep_sem_filter_out                   false
% 7.12/1.51  --pred_elim                             true
% 7.12/1.51  --res_sim_input                         true
% 7.12/1.51  --eq_ax_congr_red                       true
% 7.12/1.51  --pure_diseq_elim                       true
% 7.12/1.51  --brand_transform                       false
% 7.12/1.51  --non_eq_to_eq                          false
% 7.12/1.51  --prep_def_merge                        true
% 7.12/1.51  --prep_def_merge_prop_impl              false
% 7.12/1.51  --prep_def_merge_mbd                    true
% 7.12/1.51  --prep_def_merge_tr_red                 false
% 7.12/1.51  --prep_def_merge_tr_cl                  false
% 7.12/1.51  --smt_preprocessing                     true
% 7.12/1.51  --smt_ac_axioms                         fast
% 7.12/1.51  --preprocessed_out                      false
% 7.12/1.51  --preprocessed_stats                    false
% 7.12/1.51  
% 7.12/1.51  ------ Abstraction refinement Options
% 7.12/1.51  
% 7.12/1.51  --abstr_ref                             []
% 7.12/1.51  --abstr_ref_prep                        false
% 7.12/1.51  --abstr_ref_until_sat                   false
% 7.12/1.51  --abstr_ref_sig_restrict                funpre
% 7.12/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.12/1.51  --abstr_ref_under                       []
% 7.12/1.51  
% 7.12/1.51  ------ SAT Options
% 7.12/1.51  
% 7.12/1.51  --sat_mode                              false
% 7.12/1.51  --sat_fm_restart_options                ""
% 7.12/1.51  --sat_gr_def                            false
% 7.12/1.51  --sat_epr_types                         true
% 7.12/1.51  --sat_non_cyclic_types                  false
% 7.12/1.51  --sat_finite_models                     false
% 7.12/1.51  --sat_fm_lemmas                         false
% 7.12/1.51  --sat_fm_prep                           false
% 7.12/1.51  --sat_fm_uc_incr                        true
% 7.12/1.51  --sat_out_model                         small
% 7.12/1.51  --sat_out_clauses                       false
% 7.12/1.51  
% 7.12/1.51  ------ QBF Options
% 7.12/1.51  
% 7.12/1.51  --qbf_mode                              false
% 7.12/1.51  --qbf_elim_univ                         false
% 7.12/1.51  --qbf_dom_inst                          none
% 7.12/1.51  --qbf_dom_pre_inst                      false
% 7.12/1.51  --qbf_sk_in                             false
% 7.12/1.51  --qbf_pred_elim                         true
% 7.12/1.51  --qbf_split                             512
% 7.12/1.51  
% 7.12/1.51  ------ BMC1 Options
% 7.12/1.51  
% 7.12/1.51  --bmc1_incremental                      false
% 7.12/1.51  --bmc1_axioms                           reachable_all
% 7.12/1.51  --bmc1_min_bound                        0
% 7.12/1.51  --bmc1_max_bound                        -1
% 7.12/1.51  --bmc1_max_bound_default                -1
% 7.12/1.51  --bmc1_symbol_reachability              true
% 7.12/1.51  --bmc1_property_lemmas                  false
% 7.12/1.51  --bmc1_k_induction                      false
% 7.12/1.51  --bmc1_non_equiv_states                 false
% 7.12/1.51  --bmc1_deadlock                         false
% 7.12/1.51  --bmc1_ucm                              false
% 7.12/1.51  --bmc1_add_unsat_core                   none
% 7.12/1.51  --bmc1_unsat_core_children              false
% 7.12/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.12/1.51  --bmc1_out_stat                         full
% 7.12/1.51  --bmc1_ground_init                      false
% 7.12/1.51  --bmc1_pre_inst_next_state              false
% 7.12/1.51  --bmc1_pre_inst_state                   false
% 7.12/1.51  --bmc1_pre_inst_reach_state             false
% 7.12/1.51  --bmc1_out_unsat_core                   false
% 7.12/1.51  --bmc1_aig_witness_out                  false
% 7.12/1.51  --bmc1_verbose                          false
% 7.12/1.51  --bmc1_dump_clauses_tptp                false
% 7.12/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.12/1.51  --bmc1_dump_file                        -
% 7.12/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.12/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.12/1.51  --bmc1_ucm_extend_mode                  1
% 7.12/1.51  --bmc1_ucm_init_mode                    2
% 7.12/1.51  --bmc1_ucm_cone_mode                    none
% 7.12/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.12/1.51  --bmc1_ucm_relax_model                  4
% 7.12/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.12/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.12/1.51  --bmc1_ucm_layered_model                none
% 7.12/1.51  --bmc1_ucm_max_lemma_size               10
% 7.12/1.51  
% 7.12/1.51  ------ AIG Options
% 7.12/1.51  
% 7.12/1.51  --aig_mode                              false
% 7.12/1.51  
% 7.12/1.51  ------ Instantiation Options
% 7.12/1.51  
% 7.12/1.51  --instantiation_flag                    true
% 7.12/1.51  --inst_sos_flag                         false
% 7.12/1.51  --inst_sos_phase                        true
% 7.12/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.12/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.12/1.51  --inst_lit_sel_side                     none
% 7.12/1.51  --inst_solver_per_active                1400
% 7.12/1.51  --inst_solver_calls_frac                1.
% 7.12/1.51  --inst_passive_queue_type               priority_queues
% 7.12/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.12/1.51  --inst_passive_queues_freq              [25;2]
% 7.12/1.51  --inst_dismatching                      true
% 7.12/1.51  --inst_eager_unprocessed_to_passive     true
% 7.12/1.51  --inst_prop_sim_given                   true
% 7.12/1.51  --inst_prop_sim_new                     false
% 7.12/1.51  --inst_subs_new                         false
% 7.12/1.51  --inst_eq_res_simp                      false
% 7.12/1.51  --inst_subs_given                       false
% 7.12/1.51  --inst_orphan_elimination               true
% 7.12/1.51  --inst_learning_loop_flag               true
% 7.12/1.51  --inst_learning_start                   3000
% 7.12/1.51  --inst_learning_factor                  2
% 7.12/1.51  --inst_start_prop_sim_after_learn       3
% 7.12/1.51  --inst_sel_renew                        solver
% 7.12/1.51  --inst_lit_activity_flag                true
% 7.12/1.51  --inst_restr_to_given                   false
% 7.12/1.51  --inst_activity_threshold               500
% 7.12/1.51  --inst_out_proof                        true
% 7.12/1.51  
% 7.12/1.51  ------ Resolution Options
% 7.12/1.51  
% 7.12/1.51  --resolution_flag                       false
% 7.12/1.51  --res_lit_sel                           adaptive
% 7.12/1.51  --res_lit_sel_side                      none
% 7.12/1.51  --res_ordering                          kbo
% 7.12/1.51  --res_to_prop_solver                    active
% 7.12/1.51  --res_prop_simpl_new                    false
% 7.12/1.51  --res_prop_simpl_given                  true
% 7.12/1.51  --res_passive_queue_type                priority_queues
% 7.12/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.12/1.51  --res_passive_queues_freq               [15;5]
% 7.12/1.51  --res_forward_subs                      full
% 7.12/1.51  --res_backward_subs                     full
% 7.12/1.51  --res_forward_subs_resolution           true
% 7.12/1.51  --res_backward_subs_resolution          true
% 7.12/1.51  --res_orphan_elimination                true
% 7.12/1.51  --res_time_limit                        2.
% 7.12/1.51  --res_out_proof                         true
% 7.12/1.51  
% 7.12/1.51  ------ Superposition Options
% 7.12/1.51  
% 7.12/1.51  --superposition_flag                    true
% 7.12/1.51  --sup_passive_queue_type                priority_queues
% 7.12/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.12/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.12/1.51  --demod_completeness_check              fast
% 7.12/1.51  --demod_use_ground                      true
% 7.12/1.51  --sup_to_prop_solver                    passive
% 7.12/1.51  --sup_prop_simpl_new                    true
% 7.12/1.51  --sup_prop_simpl_given                  true
% 7.12/1.51  --sup_fun_splitting                     false
% 7.12/1.51  --sup_smt_interval                      50000
% 7.12/1.51  
% 7.12/1.51  ------ Superposition Simplification Setup
% 7.12/1.51  
% 7.12/1.51  --sup_indices_passive                   []
% 7.12/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.12/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.12/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.12/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.12/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.12/1.51  --sup_full_bw                           [BwDemod]
% 7.12/1.51  --sup_immed_triv                        [TrivRules]
% 7.12/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.12/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.12/1.51  --sup_immed_bw_main                     []
% 7.12/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.12/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.12/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.12/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.12/1.51  
% 7.12/1.51  ------ Combination Options
% 7.12/1.51  
% 7.12/1.51  --comb_res_mult                         3
% 7.12/1.51  --comb_sup_mult                         2
% 7.12/1.51  --comb_inst_mult                        10
% 7.12/1.51  
% 7.12/1.51  ------ Debug Options
% 7.12/1.51  
% 7.12/1.51  --dbg_backtrace                         false
% 7.12/1.51  --dbg_dump_prop_clauses                 false
% 7.12/1.51  --dbg_dump_prop_clauses_file            -
% 7.12/1.51  --dbg_out_stat                          false
% 7.12/1.51  
% 7.12/1.51  
% 7.12/1.51  
% 7.12/1.51  
% 7.12/1.51  ------ Proving...
% 7.12/1.51  
% 7.12/1.51  
% 7.12/1.51  % SZS status Theorem for theBenchmark.p
% 7.12/1.51  
% 7.12/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 7.12/1.51  
% 7.12/1.51  fof(f13,conjecture,(
% 7.12/1.51    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0)))),
% 7.12/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.12/1.51  
% 7.12/1.51  fof(f14,negated_conjecture,(
% 7.12/1.51    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0)))),
% 7.12/1.51    inference(negated_conjecture,[],[f13])).
% 7.12/1.51  
% 7.12/1.51  fof(f26,plain,(
% 7.12/1.51    ? [X0,X1,X2] : ((k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 7.12/1.51    inference(ennf_transformation,[],[f14])).
% 7.12/1.51  
% 7.12/1.51  fof(f27,plain,(
% 7.12/1.51    ? [X0,X1,X2] : (k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 7.12/1.51    inference(flattening,[],[f26])).
% 7.12/1.51  
% 7.12/1.51  fof(f28,plain,(
% 7.12/1.51    ? [X0,X1,X2] : (k2_wellord1(X2,X0) != k2_wellord1(k2_wellord1(X2,X1),X0) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) & r1_tarski(sK0,sK1) & v1_relat_1(sK2))),
% 7.12/1.51    introduced(choice_axiom,[])).
% 7.12/1.51  
% 7.12/1.51  fof(f29,plain,(
% 7.12/1.51    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) & r1_tarski(sK0,sK1) & v1_relat_1(sK2)),
% 7.12/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f28])).
% 7.12/1.51  
% 7.12/1.51  fof(f43,plain,(
% 7.12/1.51    v1_relat_1(sK2)),
% 7.12/1.51    inference(cnf_transformation,[],[f29])).
% 7.12/1.51  
% 7.12/1.51  fof(f9,axiom,(
% 7.12/1.51    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k2_wellord1(X0,X1)))),
% 7.12/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.12/1.51  
% 7.12/1.51  fof(f22,plain,(
% 7.12/1.51    ! [X0,X1] : (v1_relat_1(k2_wellord1(X0,X1)) | ~v1_relat_1(X0))),
% 7.12/1.51    inference(ennf_transformation,[],[f9])).
% 7.12/1.51  
% 7.12/1.51  fof(f38,plain,(
% 7.12/1.51    ( ! [X0,X1] : (v1_relat_1(k2_wellord1(X0,X1)) | ~v1_relat_1(X0)) )),
% 7.12/1.51    inference(cnf_transformation,[],[f22])).
% 7.12/1.51  
% 7.12/1.51  fof(f6,axiom,(
% 7.12/1.51    ! [X0] : (v1_relat_1(X0) => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0))),
% 7.12/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.12/1.51  
% 7.12/1.51  fof(f17,plain,(
% 7.12/1.51    ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0))),
% 7.12/1.51    inference(ennf_transformation,[],[f6])).
% 7.12/1.51  
% 7.12/1.51  fof(f35,plain,(
% 7.12/1.51    ( ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 7.12/1.51    inference(cnf_transformation,[],[f17])).
% 7.12/1.51  
% 7.12/1.51  fof(f5,axiom,(
% 7.12/1.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 7.12/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.12/1.51  
% 7.12/1.51  fof(f34,plain,(
% 7.12/1.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 7.12/1.51    inference(cnf_transformation,[],[f5])).
% 7.12/1.51  
% 7.12/1.51  fof(f4,axiom,(
% 7.12/1.51    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.12/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.12/1.51  
% 7.12/1.51  fof(f33,plain,(
% 7.12/1.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.12/1.51    inference(cnf_transformation,[],[f4])).
% 7.12/1.51  
% 7.12/1.51  fof(f46,plain,(
% 7.12/1.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 7.12/1.51    inference(definition_unfolding,[],[f34,f33])).
% 7.12/1.51  
% 7.12/1.51  fof(f49,plain,(
% 7.12/1.51    ( ! [X0] : (k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 7.12/1.51    inference(definition_unfolding,[],[f35,f46])).
% 7.12/1.51  
% 7.12/1.51  fof(f3,axiom,(
% 7.12/1.51    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 7.12/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.12/1.51  
% 7.12/1.51  fof(f32,plain,(
% 7.12/1.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 7.12/1.51    inference(cnf_transformation,[],[f3])).
% 7.12/1.51  
% 7.12/1.51  fof(f48,plain,(
% 7.12/1.51    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 7.12/1.51    inference(definition_unfolding,[],[f32,f33,f33])).
% 7.12/1.51  
% 7.12/1.51  fof(f2,axiom,(
% 7.12/1.51    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 7.12/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.12/1.51  
% 7.12/1.51  fof(f31,plain,(
% 7.12/1.51    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 7.12/1.51    inference(cnf_transformation,[],[f2])).
% 7.12/1.51  
% 7.12/1.51  fof(f47,plain,(
% 7.12/1.51    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1)))) )),
% 7.12/1.51    inference(definition_unfolding,[],[f31,f46])).
% 7.12/1.51  
% 7.12/1.51  fof(f7,axiom,(
% 7.12/1.51    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 7.12/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.12/1.51  
% 7.12/1.51  fof(f18,plain,(
% 7.12/1.51    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.12/1.51    inference(ennf_transformation,[],[f7])).
% 7.12/1.51  
% 7.12/1.51  fof(f19,plain,(
% 7.12/1.51    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 7.12/1.51    inference(flattening,[],[f18])).
% 7.12/1.51  
% 7.12/1.51  fof(f36,plain,(
% 7.12/1.51    ( ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 7.12/1.51    inference(cnf_transformation,[],[f19])).
% 7.12/1.51  
% 7.12/1.51  fof(f10,axiom,(
% 7.12/1.51    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(k8_relat_1(X0,X1),X0) = k2_wellord1(X1,X0))),
% 7.12/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.12/1.51  
% 7.12/1.51  fof(f23,plain,(
% 7.12/1.51    ! [X0,X1] : (k7_relat_1(k8_relat_1(X0,X1),X0) = k2_wellord1(X1,X0) | ~v1_relat_1(X1))),
% 7.12/1.51    inference(ennf_transformation,[],[f10])).
% 7.12/1.51  
% 7.12/1.51  fof(f39,plain,(
% 7.12/1.51    ( ! [X0,X1] : (k7_relat_1(k8_relat_1(X0,X1),X0) = k2_wellord1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.12/1.51    inference(cnf_transformation,[],[f23])).
% 7.12/1.51  
% 7.12/1.51  fof(f8,axiom,(
% 7.12/1.51    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 7.12/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.12/1.51  
% 7.12/1.51  fof(f20,plain,(
% 7.12/1.51    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.12/1.51    inference(ennf_transformation,[],[f8])).
% 7.12/1.51  
% 7.12/1.51  fof(f21,plain,(
% 7.12/1.51    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 7.12/1.51    inference(flattening,[],[f20])).
% 7.12/1.51  
% 7.12/1.51  fof(f37,plain,(
% 7.12/1.51    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 7.12/1.51    inference(cnf_transformation,[],[f21])).
% 7.12/1.51  
% 7.12/1.51  fof(f12,axiom,(
% 7.12/1.51    ! [X0,X1,X2] : (v1_relat_1(X2) => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0))),
% 7.12/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.12/1.51  
% 7.12/1.51  fof(f25,plain,(
% 7.12/1.51    ! [X0,X1,X2] : (k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) | ~v1_relat_1(X2))),
% 7.12/1.51    inference(ennf_transformation,[],[f12])).
% 7.12/1.51  
% 7.12/1.51  fof(f42,plain,(
% 7.12/1.51    ( ! [X2,X0,X1] : (k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) | ~v1_relat_1(X2)) )),
% 7.12/1.51    inference(cnf_transformation,[],[f25])).
% 7.12/1.51  
% 7.12/1.51  fof(f11,axiom,(
% 7.12/1.51    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0) & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1))))),
% 7.12/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.12/1.51  
% 7.12/1.51  fof(f24,plain,(
% 7.12/1.51    ! [X0,X1] : ((r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0) & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1))) | ~v1_relat_1(X1))),
% 7.12/1.51    inference(ennf_transformation,[],[f11])).
% 7.12/1.51  
% 7.12/1.51  fof(f40,plain,(
% 7.12/1.51    ( ! [X0,X1] : (r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 7.12/1.51    inference(cnf_transformation,[],[f24])).
% 7.12/1.51  
% 7.12/1.51  fof(f41,plain,(
% 7.12/1.51    ( ! [X0,X1] : (r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 7.12/1.51    inference(cnf_transformation,[],[f24])).
% 7.12/1.51  
% 7.12/1.51  fof(f1,axiom,(
% 7.12/1.51    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 7.12/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.12/1.51  
% 7.12/1.51  fof(f15,plain,(
% 7.12/1.51    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 7.12/1.51    inference(ennf_transformation,[],[f1])).
% 7.12/1.51  
% 7.12/1.51  fof(f16,plain,(
% 7.12/1.51    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 7.12/1.51    inference(flattening,[],[f15])).
% 7.12/1.51  
% 7.12/1.51  fof(f30,plain,(
% 7.12/1.51    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 7.12/1.51    inference(cnf_transformation,[],[f16])).
% 7.12/1.51  
% 7.12/1.51  fof(f44,plain,(
% 7.12/1.51    r1_tarski(sK0,sK1)),
% 7.12/1.51    inference(cnf_transformation,[],[f29])).
% 7.12/1.51  
% 7.12/1.51  fof(f45,plain,(
% 7.12/1.51    k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0)),
% 7.12/1.51    inference(cnf_transformation,[],[f29])).
% 7.12/1.51  
% 7.12/1.51  cnf(c_13,negated_conjecture,
% 7.12/1.51      ( v1_relat_1(sK2) ),
% 7.12/1.51      inference(cnf_transformation,[],[f43]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_145,negated_conjecture,
% 7.12/1.51      ( v1_relat_1(sK2) ),
% 7.12/1.51      inference(subtyping,[status(esa)],[c_13]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_418,plain,
% 7.12/1.51      ( v1_relat_1(sK2) = iProver_top ),
% 7.12/1.51      inference(predicate_to_equality,[status(thm)],[c_145]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_6,plain,
% 7.12/1.51      ( ~ v1_relat_1(X0) | v1_relat_1(k2_wellord1(X0,X1)) ),
% 7.12/1.51      inference(cnf_transformation,[],[f38]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_152,plain,
% 7.12/1.51      ( ~ v1_relat_1(X0_41) | v1_relat_1(k2_wellord1(X0_41,X0_42)) ),
% 7.12/1.51      inference(subtyping,[status(esa)],[c_6]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_412,plain,
% 7.12/1.51      ( v1_relat_1(X0_41) != iProver_top
% 7.12/1.51      | v1_relat_1(k2_wellord1(X0_41,X0_42)) = iProver_top ),
% 7.12/1.51      inference(predicate_to_equality,[status(thm)],[c_152]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_3,plain,
% 7.12/1.51      ( ~ v1_relat_1(X0)
% 7.12/1.51      | k3_tarski(k1_enumset1(k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) = k3_relat_1(X0) ),
% 7.12/1.51      inference(cnf_transformation,[],[f49]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_155,plain,
% 7.12/1.51      ( ~ v1_relat_1(X0_41)
% 7.12/1.51      | k3_tarski(k1_enumset1(k1_relat_1(X0_41),k1_relat_1(X0_41),k2_relat_1(X0_41))) = k3_relat_1(X0_41) ),
% 7.12/1.51      inference(subtyping,[status(esa)],[c_3]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_409,plain,
% 7.12/1.51      ( k3_tarski(k1_enumset1(k1_relat_1(X0_41),k1_relat_1(X0_41),k2_relat_1(X0_41))) = k3_relat_1(X0_41)
% 7.12/1.51      | v1_relat_1(X0_41) != iProver_top ),
% 7.12/1.51      inference(predicate_to_equality,[status(thm)],[c_155]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_863,plain,
% 7.12/1.51      ( k3_tarski(k1_enumset1(k1_relat_1(k2_wellord1(X0_41,X0_42)),k1_relat_1(k2_wellord1(X0_41,X0_42)),k2_relat_1(k2_wellord1(X0_41,X0_42)))) = k3_relat_1(k2_wellord1(X0_41,X0_42))
% 7.12/1.51      | v1_relat_1(X0_41) != iProver_top ),
% 7.12/1.51      inference(superposition,[status(thm)],[c_412,c_409]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_6325,plain,
% 7.12/1.51      ( k3_tarski(k1_enumset1(k1_relat_1(k2_wellord1(sK2,X0_42)),k1_relat_1(k2_wellord1(sK2,X0_42)),k2_relat_1(k2_wellord1(sK2,X0_42)))) = k3_relat_1(k2_wellord1(sK2,X0_42)) ),
% 7.12/1.51      inference(superposition,[status(thm)],[c_418,c_863]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_2,plain,
% 7.12/1.51      ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
% 7.12/1.51      inference(cnf_transformation,[],[f48]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_156,plain,
% 7.12/1.51      ( k1_enumset1(X0_42,X0_42,X1_42) = k1_enumset1(X1_42,X1_42,X0_42) ),
% 7.12/1.51      inference(subtyping,[status(esa)],[c_2]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_1,plain,
% 7.12/1.51      ( r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
% 7.12/1.51      inference(cnf_transformation,[],[f47]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_157,plain,
% 7.12/1.51      ( r1_tarski(X0_42,k3_tarski(k1_enumset1(X0_42,X0_42,X1_42))) ),
% 7.12/1.51      inference(subtyping,[status(esa)],[c_1]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_408,plain,
% 7.12/1.51      ( r1_tarski(X0_42,k3_tarski(k1_enumset1(X0_42,X0_42,X1_42))) = iProver_top ),
% 7.12/1.51      inference(predicate_to_equality,[status(thm)],[c_157]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_592,plain,
% 7.12/1.51      ( r1_tarski(X0_42,k3_tarski(k1_enumset1(X1_42,X1_42,X0_42))) = iProver_top ),
% 7.12/1.51      inference(superposition,[status(thm)],[c_156,c_408]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_6936,plain,
% 7.12/1.51      ( r1_tarski(k2_relat_1(k2_wellord1(sK2,X0_42)),k3_relat_1(k2_wellord1(sK2,X0_42))) = iProver_top ),
% 7.12/1.51      inference(superposition,[status(thm)],[c_6325,c_592]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_862,plain,
% 7.12/1.51      ( k3_tarski(k1_enumset1(k1_relat_1(sK2),k1_relat_1(sK2),k2_relat_1(sK2))) = k3_relat_1(sK2) ),
% 7.12/1.51      inference(superposition,[status(thm)],[c_418,c_409]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_1024,plain,
% 7.12/1.51      ( r1_tarski(k2_relat_1(sK2),k3_relat_1(sK2)) = iProver_top ),
% 7.12/1.51      inference(superposition,[status(thm)],[c_862,c_592]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_4,plain,
% 7.12/1.51      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 7.12/1.51      | ~ v1_relat_1(X0)
% 7.12/1.51      | k8_relat_1(X1,X0) = X0 ),
% 7.12/1.51      inference(cnf_transformation,[],[f36]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_154,plain,
% 7.12/1.51      ( ~ r1_tarski(k2_relat_1(X0_41),X0_42)
% 7.12/1.51      | ~ v1_relat_1(X0_41)
% 7.12/1.51      | k8_relat_1(X0_42,X0_41) = X0_41 ),
% 7.12/1.51      inference(subtyping,[status(esa)],[c_4]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_410,plain,
% 7.12/1.51      ( k8_relat_1(X0_42,X0_41) = X0_41
% 7.12/1.51      | r1_tarski(k2_relat_1(X0_41),X0_42) != iProver_top
% 7.12/1.51      | v1_relat_1(X0_41) != iProver_top ),
% 7.12/1.51      inference(predicate_to_equality,[status(thm)],[c_154]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_1356,plain,
% 7.12/1.51      ( k8_relat_1(k3_relat_1(sK2),sK2) = sK2
% 7.12/1.51      | v1_relat_1(sK2) != iProver_top ),
% 7.12/1.51      inference(superposition,[status(thm)],[c_1024,c_410]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_14,plain,
% 7.12/1.51      ( v1_relat_1(sK2) = iProver_top ),
% 7.12/1.51      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_1541,plain,
% 7.12/1.51      ( k8_relat_1(k3_relat_1(sK2),sK2) = sK2 ),
% 7.12/1.51      inference(global_propositional_subsumption,
% 7.12/1.51                [status(thm)],
% 7.12/1.51                [c_1356,c_14]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_7,plain,
% 7.12/1.51      ( ~ v1_relat_1(X0)
% 7.12/1.51      | k7_relat_1(k8_relat_1(X1,X0),X1) = k2_wellord1(X0,X1) ),
% 7.12/1.51      inference(cnf_transformation,[],[f39]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_151,plain,
% 7.12/1.51      ( ~ v1_relat_1(X0_41)
% 7.12/1.51      | k7_relat_1(k8_relat_1(X0_42,X0_41),X0_42) = k2_wellord1(X0_41,X0_42) ),
% 7.12/1.51      inference(subtyping,[status(esa)],[c_7]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_413,plain,
% 7.12/1.51      ( k7_relat_1(k8_relat_1(X0_42,X0_41),X0_42) = k2_wellord1(X0_41,X0_42)
% 7.12/1.51      | v1_relat_1(X0_41) != iProver_top ),
% 7.12/1.51      inference(predicate_to_equality,[status(thm)],[c_151]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_751,plain,
% 7.12/1.51      ( k7_relat_1(k8_relat_1(X0_42,sK2),X0_42) = k2_wellord1(sK2,X0_42) ),
% 7.12/1.51      inference(superposition,[status(thm)],[c_418,c_413]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_1544,plain,
% 7.12/1.51      ( k2_wellord1(sK2,k3_relat_1(sK2)) = k7_relat_1(sK2,k3_relat_1(sK2)) ),
% 7.12/1.51      inference(superposition,[status(thm)],[c_1541,c_751]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_1023,plain,
% 7.12/1.51      ( r1_tarski(k1_relat_1(sK2),k3_relat_1(sK2)) = iProver_top ),
% 7.12/1.51      inference(superposition,[status(thm)],[c_862,c_408]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_5,plain,
% 7.12/1.51      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 7.12/1.51      | ~ v1_relat_1(X0)
% 7.12/1.51      | k7_relat_1(X0,X1) = X0 ),
% 7.12/1.51      inference(cnf_transformation,[],[f37]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_153,plain,
% 7.12/1.51      ( ~ r1_tarski(k1_relat_1(X0_41),X0_42)
% 7.12/1.51      | ~ v1_relat_1(X0_41)
% 7.12/1.51      | k7_relat_1(X0_41,X0_42) = X0_41 ),
% 7.12/1.51      inference(subtyping,[status(esa)],[c_5]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_411,plain,
% 7.12/1.51      ( k7_relat_1(X0_41,X0_42) = X0_41
% 7.12/1.51      | r1_tarski(k1_relat_1(X0_41),X0_42) != iProver_top
% 7.12/1.51      | v1_relat_1(X0_41) != iProver_top ),
% 7.12/1.51      inference(predicate_to_equality,[status(thm)],[c_153]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_1520,plain,
% 7.12/1.51      ( k7_relat_1(sK2,k3_relat_1(sK2)) = sK2
% 7.12/1.51      | v1_relat_1(sK2) != iProver_top ),
% 7.12/1.51      inference(superposition,[status(thm)],[c_1023,c_411]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_1613,plain,
% 7.12/1.51      ( k7_relat_1(sK2,k3_relat_1(sK2)) = sK2 ),
% 7.12/1.51      inference(global_propositional_subsumption,
% 7.12/1.51                [status(thm)],
% 7.12/1.51                [c_1520,c_14]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_1706,plain,
% 7.12/1.51      ( k2_wellord1(sK2,k3_relat_1(sK2)) = sK2 ),
% 7.12/1.51      inference(light_normalisation,[status(thm)],[c_1544,c_1613]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_10,plain,
% 7.12/1.51      ( ~ v1_relat_1(X0)
% 7.12/1.51      | k2_wellord1(k2_wellord1(X0,X1),X2) = k2_wellord1(k2_wellord1(X0,X2),X1) ),
% 7.12/1.51      inference(cnf_transformation,[],[f42]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_148,plain,
% 7.12/1.51      ( ~ v1_relat_1(X0_41)
% 7.12/1.51      | k2_wellord1(k2_wellord1(X0_41,X0_42),X1_42) = k2_wellord1(k2_wellord1(X0_41,X1_42),X0_42) ),
% 7.12/1.51      inference(subtyping,[status(esa)],[c_10]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_416,plain,
% 7.12/1.51      ( k2_wellord1(k2_wellord1(X0_41,X0_42),X1_42) = k2_wellord1(k2_wellord1(X0_41,X1_42),X0_42)
% 7.12/1.51      | v1_relat_1(X0_41) != iProver_top ),
% 7.12/1.51      inference(predicate_to_equality,[status(thm)],[c_148]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_935,plain,
% 7.12/1.51      ( k2_wellord1(k2_wellord1(sK2,X0_42),X1_42) = k2_wellord1(k2_wellord1(sK2,X1_42),X0_42) ),
% 7.12/1.51      inference(superposition,[status(thm)],[c_418,c_416]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_9,plain,
% 7.12/1.51      ( r1_tarski(k3_relat_1(k2_wellord1(X0,X1)),k3_relat_1(X0))
% 7.12/1.51      | ~ v1_relat_1(X0) ),
% 7.12/1.51      inference(cnf_transformation,[],[f40]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_149,plain,
% 7.12/1.51      ( r1_tarski(k3_relat_1(k2_wellord1(X0_41,X0_42)),k3_relat_1(X0_41))
% 7.12/1.51      | ~ v1_relat_1(X0_41) ),
% 7.12/1.51      inference(subtyping,[status(esa)],[c_9]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_415,plain,
% 7.12/1.51      ( r1_tarski(k3_relat_1(k2_wellord1(X0_41,X0_42)),k3_relat_1(X0_41)) = iProver_top
% 7.12/1.51      | v1_relat_1(X0_41) != iProver_top ),
% 7.12/1.51      inference(predicate_to_equality,[status(thm)],[c_149]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_1036,plain,
% 7.12/1.51      ( r1_tarski(k3_relat_1(k2_wellord1(k2_wellord1(sK2,X0_42),X1_42)),k3_relat_1(k2_wellord1(sK2,X1_42))) = iProver_top
% 7.12/1.51      | v1_relat_1(k2_wellord1(sK2,X1_42)) != iProver_top ),
% 7.12/1.51      inference(superposition,[status(thm)],[c_935,c_415]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_8,plain,
% 7.12/1.51      ( r1_tarski(k3_relat_1(k2_wellord1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 7.12/1.51      inference(cnf_transformation,[],[f41]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_150,plain,
% 7.12/1.51      ( r1_tarski(k3_relat_1(k2_wellord1(X0_41,X0_42)),X0_42)
% 7.12/1.51      | ~ v1_relat_1(X0_41) ),
% 7.12/1.51      inference(subtyping,[status(esa)],[c_8]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_414,plain,
% 7.12/1.51      ( r1_tarski(k3_relat_1(k2_wellord1(X0_41,X0_42)),X0_42) = iProver_top
% 7.12/1.51      | v1_relat_1(X0_41) != iProver_top ),
% 7.12/1.51      inference(predicate_to_equality,[status(thm)],[c_150]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_0,plain,
% 7.12/1.51      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 7.12/1.51      inference(cnf_transformation,[],[f30]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_158,plain,
% 7.12/1.51      ( ~ r1_tarski(X0_42,X1_42)
% 7.12/1.51      | ~ r1_tarski(X2_42,X0_42)
% 7.12/1.51      | r1_tarski(X2_42,X1_42) ),
% 7.12/1.51      inference(subtyping,[status(esa)],[c_0]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_407,plain,
% 7.12/1.51      ( r1_tarski(X0_42,X1_42) != iProver_top
% 7.12/1.51      | r1_tarski(X2_42,X0_42) != iProver_top
% 7.12/1.51      | r1_tarski(X2_42,X1_42) = iProver_top ),
% 7.12/1.51      inference(predicate_to_equality,[status(thm)],[c_158]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_721,plain,
% 7.12/1.51      ( r1_tarski(X0_42,X1_42) = iProver_top
% 7.12/1.51      | r1_tarski(X0_42,k3_relat_1(k2_wellord1(X0_41,X1_42))) != iProver_top
% 7.12/1.51      | v1_relat_1(X0_41) != iProver_top ),
% 7.12/1.51      inference(superposition,[status(thm)],[c_414,c_407]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_2365,plain,
% 7.12/1.51      ( r1_tarski(k3_relat_1(k2_wellord1(k2_wellord1(sK2,X0_42),X1_42)),X1_42) = iProver_top
% 7.12/1.51      | v1_relat_1(k2_wellord1(sK2,X1_42)) != iProver_top
% 7.12/1.51      | v1_relat_1(sK2) != iProver_top ),
% 7.12/1.51      inference(superposition,[status(thm)],[c_1036,c_721]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_3524,plain,
% 7.12/1.51      ( v1_relat_1(k2_wellord1(sK2,X1_42)) != iProver_top
% 7.12/1.51      | r1_tarski(k3_relat_1(k2_wellord1(k2_wellord1(sK2,X0_42),X1_42)),X1_42) = iProver_top ),
% 7.12/1.51      inference(global_propositional_subsumption,
% 7.12/1.51                [status(thm)],
% 7.12/1.51                [c_2365,c_14]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_3525,plain,
% 7.12/1.51      ( r1_tarski(k3_relat_1(k2_wellord1(k2_wellord1(sK2,X0_42),X1_42)),X1_42) = iProver_top
% 7.12/1.51      | v1_relat_1(k2_wellord1(sK2,X1_42)) != iProver_top ),
% 7.12/1.51      inference(renaming,[status(thm)],[c_3524]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_12,negated_conjecture,
% 7.12/1.51      ( r1_tarski(sK0,sK1) ),
% 7.12/1.51      inference(cnf_transformation,[],[f44]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_146,negated_conjecture,
% 7.12/1.51      ( r1_tarski(sK0,sK1) ),
% 7.12/1.51      inference(subtyping,[status(esa)],[c_12]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_417,plain,
% 7.12/1.51      ( r1_tarski(sK0,sK1) = iProver_top ),
% 7.12/1.51      inference(predicate_to_equality,[status(thm)],[c_146]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_720,plain,
% 7.12/1.51      ( r1_tarski(X0_42,sK1) = iProver_top
% 7.12/1.51      | r1_tarski(X0_42,sK0) != iProver_top ),
% 7.12/1.51      inference(superposition,[status(thm)],[c_417,c_407]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_3535,plain,
% 7.12/1.51      ( r1_tarski(k3_relat_1(k2_wellord1(k2_wellord1(sK2,X0_42),sK0)),sK1) = iProver_top
% 7.12/1.51      | v1_relat_1(k2_wellord1(sK2,sK0)) != iProver_top ),
% 7.12/1.51      inference(superposition,[status(thm)],[c_3525,c_720]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_196,plain,
% 7.12/1.51      ( v1_relat_1(X0_41) != iProver_top
% 7.12/1.51      | v1_relat_1(k2_wellord1(X0_41,X0_42)) = iProver_top ),
% 7.12/1.51      inference(predicate_to_equality,[status(thm)],[c_152]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_198,plain,
% 7.12/1.51      ( v1_relat_1(k2_wellord1(sK2,sK0)) = iProver_top
% 7.12/1.51      | v1_relat_1(sK2) != iProver_top ),
% 7.12/1.51      inference(instantiation,[status(thm)],[c_196]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_1118,plain,
% 7.12/1.51      ( r1_tarski(k3_relat_1(k2_wellord1(X0_41,sK0)),sK1) = iProver_top
% 7.12/1.51      | v1_relat_1(X0_41) != iProver_top ),
% 7.12/1.51      inference(superposition,[status(thm)],[c_414,c_720]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_1335,plain,
% 7.12/1.51      ( r1_tarski(X0_42,k3_relat_1(k2_wellord1(X0_41,sK0))) != iProver_top
% 7.12/1.51      | r1_tarski(X0_42,sK1) = iProver_top
% 7.12/1.51      | v1_relat_1(X0_41) != iProver_top ),
% 7.12/1.51      inference(superposition,[status(thm)],[c_1118,c_407]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_3166,plain,
% 7.12/1.51      ( r1_tarski(k3_relat_1(k2_wellord1(k2_wellord1(sK2,X0_42),sK0)),sK1) = iProver_top
% 7.12/1.51      | v1_relat_1(k2_wellord1(sK2,sK0)) != iProver_top
% 7.12/1.51      | v1_relat_1(sK2) != iProver_top ),
% 7.12/1.51      inference(superposition,[status(thm)],[c_1036,c_1335]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_4250,plain,
% 7.12/1.51      ( r1_tarski(k3_relat_1(k2_wellord1(k2_wellord1(sK2,X0_42),sK0)),sK1) = iProver_top ),
% 7.12/1.51      inference(global_propositional_subsumption,
% 7.12/1.51                [status(thm)],
% 7.12/1.51                [c_3535,c_14,c_198,c_3166]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_4259,plain,
% 7.12/1.51      ( r1_tarski(k3_relat_1(k2_wellord1(sK2,sK0)),sK1) = iProver_top ),
% 7.12/1.51      inference(superposition,[status(thm)],[c_1706,c_4250]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_4719,plain,
% 7.12/1.51      ( r1_tarski(X0_42,k3_relat_1(k2_wellord1(sK2,sK0))) != iProver_top
% 7.12/1.51      | r1_tarski(X0_42,sK1) = iProver_top ),
% 7.12/1.51      inference(superposition,[status(thm)],[c_4259,c_407]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_7182,plain,
% 7.12/1.51      ( r1_tarski(k2_relat_1(k2_wellord1(sK2,sK0)),sK1) = iProver_top ),
% 7.12/1.51      inference(superposition,[status(thm)],[c_6936,c_4719]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_18208,plain,
% 7.12/1.51      ( k8_relat_1(sK1,k2_wellord1(sK2,sK0)) = k2_wellord1(sK2,sK0)
% 7.12/1.51      | v1_relat_1(k2_wellord1(sK2,sK0)) != iProver_top ),
% 7.12/1.51      inference(superposition,[status(thm)],[c_7182,c_410]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_19913,plain,
% 7.12/1.51      ( k8_relat_1(sK1,k2_wellord1(sK2,sK0)) = k2_wellord1(sK2,sK0) ),
% 7.12/1.51      inference(global_propositional_subsumption,
% 7.12/1.51                [status(thm)],
% 7.12/1.51                [c_18208,c_14,c_198]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_752,plain,
% 7.12/1.51      ( k7_relat_1(k8_relat_1(X0_42,k2_wellord1(X0_41,X1_42)),X0_42) = k2_wellord1(k2_wellord1(X0_41,X1_42),X0_42)
% 7.12/1.51      | v1_relat_1(X0_41) != iProver_top ),
% 7.12/1.51      inference(superposition,[status(thm)],[c_412,c_413]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_3684,plain,
% 7.12/1.51      ( k7_relat_1(k8_relat_1(X0_42,k2_wellord1(sK2,X1_42)),X0_42) = k2_wellord1(k2_wellord1(sK2,X1_42),X0_42) ),
% 7.12/1.51      inference(superposition,[status(thm)],[c_418,c_752]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_19916,plain,
% 7.12/1.51      ( k2_wellord1(k2_wellord1(sK2,sK0),sK1) = k7_relat_1(k2_wellord1(sK2,sK0),sK1) ),
% 7.12/1.51      inference(superposition,[status(thm)],[c_19913,c_3684]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_6934,plain,
% 7.12/1.51      ( r1_tarski(k1_relat_1(k2_wellord1(sK2,X0_42)),k3_relat_1(k2_wellord1(sK2,X0_42))) = iProver_top ),
% 7.12/1.51      inference(superposition,[status(thm)],[c_6325,c_408]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_7130,plain,
% 7.12/1.51      ( r1_tarski(k1_relat_1(k2_wellord1(sK2,sK0)),sK1) = iProver_top ),
% 7.12/1.51      inference(superposition,[status(thm)],[c_6934,c_4719]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_7749,plain,
% 7.12/1.51      ( k7_relat_1(k2_wellord1(sK2,sK0),sK1) = k2_wellord1(sK2,sK0)
% 7.12/1.51      | v1_relat_1(k2_wellord1(sK2,sK0)) != iProver_top ),
% 7.12/1.51      inference(superposition,[status(thm)],[c_7130,c_411]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_11214,plain,
% 7.12/1.51      ( k7_relat_1(k2_wellord1(sK2,sK0),sK1) = k2_wellord1(sK2,sK0) ),
% 7.12/1.51      inference(global_propositional_subsumption,
% 7.12/1.51                [status(thm)],
% 7.12/1.51                [c_7749,c_14,c_198]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_19917,plain,
% 7.12/1.51      ( k2_wellord1(k2_wellord1(sK2,sK0),sK1) = k2_wellord1(sK2,sK0) ),
% 7.12/1.51      inference(light_normalisation,[status(thm)],[c_19916,c_11214]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_11,negated_conjecture,
% 7.12/1.51      ( k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) ),
% 7.12/1.51      inference(cnf_transformation,[],[f45]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_147,negated_conjecture,
% 7.12/1.51      ( k2_wellord1(sK2,sK0) != k2_wellord1(k2_wellord1(sK2,sK1),sK0) ),
% 7.12/1.51      inference(subtyping,[status(esa)],[c_11]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_1032,plain,
% 7.12/1.51      ( k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(sK2,sK0) ),
% 7.12/1.51      inference(demodulation,[status(thm)],[c_935,c_147]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(contradiction,plain,
% 7.12/1.51      ( $false ),
% 7.12/1.51      inference(minisat,[status(thm)],[c_19917,c_1032]) ).
% 7.12/1.51  
% 7.12/1.51  
% 7.12/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.12/1.51  
% 7.12/1.51  ------                               Statistics
% 7.12/1.51  
% 7.12/1.51  ------ General
% 7.12/1.51  
% 7.12/1.51  abstr_ref_over_cycles:                  0
% 7.12/1.51  abstr_ref_under_cycles:                 0
% 7.12/1.51  gc_basic_clause_elim:                   0
% 7.12/1.51  forced_gc_time:                         0
% 7.12/1.51  parsing_time:                           0.008
% 7.12/1.51  unif_index_cands_time:                  0.
% 7.12/1.51  unif_index_add_time:                    0.
% 7.12/1.51  orderings_time:                         0.
% 7.12/1.51  out_proof_time:                         0.009
% 7.12/1.51  total_time:                             0.666
% 7.12/1.51  num_of_symbols:                         44
% 7.12/1.51  num_of_terms:                           23568
% 7.12/1.51  
% 7.12/1.51  ------ Preprocessing
% 7.12/1.51  
% 7.12/1.51  num_of_splits:                          0
% 7.12/1.51  num_of_split_atoms:                     0
% 7.12/1.51  num_of_reused_defs:                     0
% 7.12/1.51  num_eq_ax_congr_red:                    10
% 7.12/1.51  num_of_sem_filtered_clauses:            1
% 7.12/1.51  num_of_subtypes:                        3
% 7.12/1.51  monotx_restored_types:                  0
% 7.12/1.51  sat_num_of_epr_types:                   0
% 7.12/1.51  sat_num_of_non_cyclic_types:            0
% 7.12/1.51  sat_guarded_non_collapsed_types:        1
% 7.12/1.51  num_pure_diseq_elim:                    0
% 7.12/1.51  simp_replaced_by:                       0
% 7.12/1.51  res_preprocessed:                       69
% 7.12/1.51  prep_upred:                             0
% 7.12/1.51  prep_unflattend:                        0
% 7.12/1.51  smt_new_axioms:                         0
% 7.12/1.51  pred_elim_cands:                        2
% 7.12/1.51  pred_elim:                              0
% 7.12/1.51  pred_elim_cl:                           0
% 7.12/1.51  pred_elim_cycles:                       1
% 7.12/1.51  merged_defs:                            0
% 7.12/1.51  merged_defs_ncl:                        0
% 7.12/1.51  bin_hyper_res:                          0
% 7.12/1.51  prep_cycles:                            3
% 7.12/1.51  pred_elim_time:                         0.
% 7.12/1.51  splitting_time:                         0.
% 7.12/1.51  sem_filter_time:                        0.
% 7.12/1.51  monotx_time:                            0.
% 7.12/1.51  subtype_inf_time:                       0.
% 7.12/1.51  
% 7.12/1.51  ------ Problem properties
% 7.12/1.51  
% 7.12/1.51  clauses:                                14
% 7.12/1.51  conjectures:                            3
% 7.12/1.51  epr:                                    3
% 7.12/1.51  horn:                                   14
% 7.12/1.51  ground:                                 3
% 7.12/1.51  unary:                                  5
% 7.12/1.51  binary:                                 6
% 7.12/1.51  lits:                                   26
% 7.12/1.51  lits_eq:                                7
% 7.12/1.51  fd_pure:                                0
% 7.12/1.51  fd_pseudo:                              0
% 7.12/1.51  fd_cond:                                0
% 7.12/1.51  fd_pseudo_cond:                         0
% 7.12/1.51  ac_symbols:                             0
% 7.12/1.51  
% 7.12/1.51  ------ Propositional Solver
% 7.12/1.51  
% 7.12/1.51  prop_solver_calls:                      26
% 7.12/1.51  prop_fast_solver_calls:                 528
% 7.12/1.51  smt_solver_calls:                       0
% 7.12/1.51  smt_fast_solver_calls:                  0
% 7.12/1.51  prop_num_of_clauses:                    6879
% 7.12/1.51  prop_preprocess_simplified:             10762
% 7.12/1.51  prop_fo_subsumed:                       11
% 7.12/1.51  prop_solver_time:                       0.
% 7.12/1.51  smt_solver_time:                        0.
% 7.12/1.51  smt_fast_solver_time:                   0.
% 7.12/1.51  prop_fast_solver_time:                  0.
% 7.12/1.51  prop_unsat_core_time:                   0.001
% 7.12/1.51  
% 7.12/1.51  ------ QBF
% 7.12/1.51  
% 7.12/1.51  qbf_q_res:                              0
% 7.12/1.51  qbf_num_tautologies:                    0
% 7.12/1.51  qbf_prep_cycles:                        0
% 7.12/1.51  
% 7.12/1.51  ------ BMC1
% 7.12/1.51  
% 7.12/1.51  bmc1_current_bound:                     -1
% 7.12/1.51  bmc1_last_solved_bound:                 -1
% 7.12/1.51  bmc1_unsat_core_size:                   -1
% 7.12/1.51  bmc1_unsat_core_parents_size:           -1
% 7.12/1.51  bmc1_merge_next_fun:                    0
% 7.12/1.51  bmc1_unsat_core_clauses_time:           0.
% 7.12/1.51  
% 7.12/1.51  ------ Instantiation
% 7.12/1.51  
% 7.12/1.51  inst_num_of_clauses:                    1691
% 7.12/1.51  inst_num_in_passive:                    290
% 7.12/1.51  inst_num_in_active:                     668
% 7.12/1.51  inst_num_in_unprocessed:                733
% 7.12/1.51  inst_num_of_loops:                      700
% 7.12/1.51  inst_num_of_learning_restarts:          0
% 7.12/1.51  inst_num_moves_active_passive:          29
% 7.12/1.51  inst_lit_activity:                      0
% 7.12/1.51  inst_lit_activity_moves:                0
% 7.12/1.51  inst_num_tautologies:                   0
% 7.12/1.51  inst_num_prop_implied:                  0
% 7.12/1.51  inst_num_existing_simplified:           0
% 7.12/1.51  inst_num_eq_res_simplified:             0
% 7.12/1.51  inst_num_child_elim:                    0
% 7.12/1.51  inst_num_of_dismatching_blockings:      1726
% 7.12/1.51  inst_num_of_non_proper_insts:           2180
% 7.12/1.51  inst_num_of_duplicates:                 0
% 7.12/1.51  inst_inst_num_from_inst_to_res:         0
% 7.12/1.51  inst_dismatching_checking_time:         0.
% 7.12/1.51  
% 7.12/1.51  ------ Resolution
% 7.12/1.51  
% 7.12/1.51  res_num_of_clauses:                     0
% 7.12/1.51  res_num_in_passive:                     0
% 7.12/1.51  res_num_in_active:                      0
% 7.12/1.51  res_num_of_loops:                       72
% 7.12/1.51  res_forward_subset_subsumed:            264
% 7.12/1.51  res_backward_subset_subsumed:           2
% 7.12/1.51  res_forward_subsumed:                   0
% 7.12/1.51  res_backward_subsumed:                  0
% 7.12/1.51  res_forward_subsumption_resolution:     0
% 7.12/1.51  res_backward_subsumption_resolution:    0
% 7.12/1.51  res_clause_to_clause_subsumption:       3697
% 7.12/1.51  res_orphan_elimination:                 0
% 7.12/1.51  res_tautology_del:                      309
% 7.12/1.51  res_num_eq_res_simplified:              0
% 7.12/1.51  res_num_sel_changes:                    0
% 7.12/1.51  res_moves_from_active_to_pass:          0
% 7.12/1.51  
% 7.12/1.51  ------ Superposition
% 7.12/1.51  
% 7.12/1.51  sup_time_total:                         0.
% 7.12/1.51  sup_time_generating:                    0.
% 7.12/1.51  sup_time_sim_full:                      0.
% 7.12/1.51  sup_time_sim_immed:                     0.
% 7.12/1.51  
% 7.12/1.51  sup_num_of_clauses:                     955
% 7.12/1.51  sup_num_in_active:                      138
% 7.12/1.51  sup_num_in_passive:                     817
% 7.12/1.51  sup_num_of_loops:                       139
% 7.12/1.51  sup_fw_superposition:                   1589
% 7.12/1.51  sup_bw_superposition:                   938
% 7.12/1.51  sup_immediate_simplified:               347
% 7.12/1.51  sup_given_eliminated:                   0
% 7.12/1.51  comparisons_done:                       0
% 7.12/1.51  comparisons_avoided:                    0
% 7.12/1.51  
% 7.12/1.51  ------ Simplifications
% 7.12/1.51  
% 7.12/1.51  
% 7.12/1.51  sim_fw_subset_subsumed:                 18
% 7.12/1.51  sim_bw_subset_subsumed:                 14
% 7.12/1.51  sim_fw_subsumed:                        63
% 7.12/1.51  sim_bw_subsumed:                        1
% 7.12/1.51  sim_fw_subsumption_res:                 0
% 7.12/1.51  sim_bw_subsumption_res:                 0
% 7.12/1.51  sim_tautology_del:                      24
% 7.12/1.51  sim_eq_tautology_del:                   34
% 7.12/1.51  sim_eq_res_simp:                        0
% 7.12/1.51  sim_fw_demodulated:                     67
% 7.12/1.51  sim_bw_demodulated:                     10
% 7.12/1.51  sim_light_normalised:                   237
% 7.12/1.51  sim_joinable_taut:                      0
% 7.12/1.51  sim_joinable_simp:                      0
% 7.12/1.51  sim_ac_normalised:                      0
% 7.12/1.51  sim_smt_subsumption:                    0
% 7.12/1.51  
%------------------------------------------------------------------------------
