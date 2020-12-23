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
% DateTime   : Thu Dec  3 11:51:42 EST 2020

% Result     : Theorem 2.29s
% Output     : CNFRefutation 2.29s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 311 expanded)
%              Number of clauses        :   55 ( 117 expanded)
%              Number of leaves         :   11 (  66 expanded)
%              Depth                    :   16
%              Number of atoms          :  150 ( 542 expanded)
%              Number of equality atoms :   80 ( 230 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f20,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f20])).

fof(f31,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,k10_relat_1(X2,X1))) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f30,f25])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f22,f25])).

fof(f33,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f23,f25])).

fof(f32,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_tarski(k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f29,f25])).

cnf(c_10,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_156,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_316,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_156])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_161,plain,
    ( ~ v1_relat_1(X0_40)
    | v1_relat_1(k7_relat_1(X0_40,X0_39)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_311,plain,
    ( v1_relat_1(X0_40) != iProver_top
    | v1_relat_1(k7_relat_1(X0_40,X0_39)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_161])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_159,plain,
    ( ~ v1_relat_1(X0_40)
    | k10_relat_1(X0_40,k2_relat_1(X0_40)) = k1_relat_1(X0_40) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_313,plain,
    ( k10_relat_1(X0_40,k2_relat_1(X0_40)) = k1_relat_1(X0_40)
    | v1_relat_1(X0_40) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_159])).

cnf(c_679,plain,
    ( k10_relat_1(k7_relat_1(X0_40,X0_39),k2_relat_1(k7_relat_1(X0_40,X0_39))) = k1_relat_1(k7_relat_1(X0_40,X0_39))
    | v1_relat_1(X0_40) != iProver_top ),
    inference(superposition,[status(thm)],[c_311,c_313])).

cnf(c_2000,plain,
    ( k10_relat_1(k7_relat_1(sK1,X0_39),k2_relat_1(k7_relat_1(sK1,X0_39))) = k1_relat_1(k7_relat_1(sK1,X0_39)) ),
    inference(superposition,[status(thm)],[c_316,c_679])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_160,plain,
    ( ~ v1_relat_1(X0_40)
    | k2_relat_1(k7_relat_1(X0_40,X0_39)) = k9_relat_1(X0_40,X0_39) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_312,plain,
    ( k2_relat_1(k7_relat_1(X0_40,X0_39)) = k9_relat_1(X0_40,X0_39)
    | v1_relat_1(X0_40) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_160])).

cnf(c_805,plain,
    ( k2_relat_1(k7_relat_1(sK1,X0_39)) = k9_relat_1(sK1,X0_39) ),
    inference(superposition,[status(thm)],[c_316,c_312])).

cnf(c_2007,plain,
    ( k10_relat_1(k7_relat_1(sK1,X0_39),k9_relat_1(sK1,X0_39)) = k1_relat_1(k7_relat_1(sK1,X0_39)) ),
    inference(light_normalisation,[status(thm)],[c_2000,c_805])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k2_tarski(X1,k10_relat_1(X0,X2))) = k10_relat_1(k7_relat_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_157,plain,
    ( ~ v1_relat_1(X0_40)
    | k1_setfam_1(k2_tarski(X0_39,k10_relat_1(X0_40,X0_41))) = k10_relat_1(k7_relat_1(X0_40,X0_39),X0_41) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_315,plain,
    ( k1_setfam_1(k2_tarski(X0_39,k10_relat_1(X0_40,X0_41))) = k10_relat_1(k7_relat_1(X0_40,X0_39),X0_41)
    | v1_relat_1(X0_40) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_157])).

cnf(c_1373,plain,
    ( k1_setfam_1(k2_tarski(X0_39,k10_relat_1(sK1,X0_41))) = k10_relat_1(k7_relat_1(sK1,X0_39),X0_41) ),
    inference(superposition,[status(thm)],[c_316,c_315])).

cnf(c_2,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_162,plain,
    ( k2_tarski(X0_39,X1_39) = k2_tarski(X1_39,X0_39) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_0,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_8,negated_conjecture,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_129,plain,
    ( k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != X0
    | k1_setfam_1(k2_tarski(X0,X1)) != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_8])).

cnf(c_130,plain,
    ( k1_setfam_1(k2_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),X0)) != sK0 ),
    inference(unflattening,[status(thm)],[c_129])).

cnf(c_154,plain,
    ( k1_setfam_1(k2_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),X0_39)) != sK0 ),
    inference(subtyping,[status(esa)],[c_130])).

cnf(c_393,plain,
    ( k1_setfam_1(k2_tarski(X0_39,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))) != sK0 ),
    inference(superposition,[status(thm)],[c_162,c_154])).

cnf(c_1535,plain,
    ( k10_relat_1(k7_relat_1(sK1,X0_39),k9_relat_1(sK1,sK0)) != sK0 ),
    inference(demodulation,[status(thm)],[c_1373,c_393])).

cnf(c_2905,plain,
    ( k1_relat_1(k7_relat_1(sK1,sK0)) != sK0 ),
    inference(superposition,[status(thm)],[c_2007,c_1535])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_9,negated_conjecture,
    ( r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_135,plain,
    ( k1_relat_1(sK1) != X0
    | k1_setfam_1(k2_tarski(X1,X0)) = X1
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_9])).

cnf(c_136,plain,
    ( k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1))) = sK0 ),
    inference(unflattening,[status(thm)],[c_135])).

cnf(c_153,plain,
    ( k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1))) = sK0 ),
    inference(subtyping,[status(esa)],[c_136])).

cnf(c_123,plain,
    ( X0 != X1
    | k1_setfam_1(k2_tarski(X1,X2)) != X3
    | k1_setfam_1(k2_tarski(X3,X0)) = X3 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_1])).

cnf(c_124,plain,
    ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_123])).

cnf(c_155,plain,
    ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0_39,X1_39)),X0_39)) = k1_setfam_1(k2_tarski(X0_39,X1_39)) ),
    inference(subtyping,[status(esa)],[c_124])).

cnf(c_434,plain,
    ( k1_setfam_1(k2_tarski(X0_39,k1_setfam_1(k2_tarski(X0_39,X1_39)))) = k1_setfam_1(k2_tarski(X0_39,X1_39)) ),
    inference(superposition,[status(thm)],[c_162,c_155])).

cnf(c_440,plain,
    ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0_39,X1_39)),k1_setfam_1(k2_tarski(X0_39,X1_39)))) = k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0_39,X1_39)),X0_39)) ),
    inference(superposition,[status(thm)],[c_155,c_155])).

cnf(c_442,plain,
    ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0_39,X1_39)),k1_setfam_1(k2_tarski(X0_39,X1_39)))) = k1_setfam_1(k2_tarski(X0_39,X1_39)) ),
    inference(light_normalisation,[status(thm)],[c_440,c_155])).

cnf(c_938,plain,
    ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0_39,X1_39)),k1_setfam_1(k2_tarski(X0_39,X1_39)))) = k1_setfam_1(k2_tarski(X0_39,k1_setfam_1(k2_tarski(X0_39,X1_39)))) ),
    inference(superposition,[status(thm)],[c_434,c_442])).

cnf(c_942,plain,
    ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0_39,X1_39)),k1_setfam_1(k2_tarski(X0_39,X1_39)))) = k1_setfam_1(k2_tarski(X1_39,X0_39)) ),
    inference(superposition,[status(thm)],[c_162,c_442])).

cnf(c_952,plain,
    ( k1_setfam_1(k2_tarski(X0_39,k1_setfam_1(k2_tarski(X0_39,X1_39)))) = k1_setfam_1(k2_tarski(X1_39,X0_39)) ),
    inference(light_normalisation,[status(thm)],[c_938,c_942])).

cnf(c_1121,plain,
    ( k1_setfam_1(k2_tarski(k1_relat_1(sK1),sK0)) = k1_setfam_1(k2_tarski(sK0,sK0)) ),
    inference(superposition,[status(thm)],[c_153,c_952])).

cnf(c_436,plain,
    ( k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1))) = k1_setfam_1(k2_tarski(sK0,sK0)) ),
    inference(superposition,[status(thm)],[c_153,c_155])).

cnf(c_448,plain,
    ( k1_setfam_1(k2_tarski(sK0,sK0)) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_436,c_153])).

cnf(c_1157,plain,
    ( k1_setfam_1(k2_tarski(k1_relat_1(sK1),sK0)) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_1121,c_448])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k2_tarski(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_158,plain,
    ( ~ v1_relat_1(X0_40)
    | k1_setfam_1(k2_tarski(k1_relat_1(X0_40),X0_39)) = k1_relat_1(k7_relat_1(X0_40,X0_39)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_314,plain,
    ( k1_setfam_1(k2_tarski(k1_relat_1(X0_40),X0_39)) = k1_relat_1(k7_relat_1(X0_40,X0_39))
    | v1_relat_1(X0_40) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_158])).

cnf(c_1162,plain,
    ( k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0_39)) = k1_relat_1(k7_relat_1(sK1,X0_39)) ),
    inference(superposition,[status(thm)],[c_316,c_314])).

cnf(c_1682,plain,
    ( k1_relat_1(k7_relat_1(sK1,sK0)) = sK0 ),
    inference(superposition,[status(thm)],[c_1157,c_1162])).

cnf(c_2908,plain,
    ( sK0 != sK0 ),
    inference(light_normalisation,[status(thm)],[c_2905,c_1682])).

cnf(c_2909,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_2908])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:20:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.29/1.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.29/1.03  
% 2.29/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.29/1.03  
% 2.29/1.03  ------  iProver source info
% 2.29/1.03  
% 2.29/1.03  git: date: 2020-06-30 10:37:57 +0100
% 2.29/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.29/1.03  git: non_committed_changes: false
% 2.29/1.03  git: last_make_outside_of_git: false
% 2.29/1.03  
% 2.29/1.03  ------ 
% 2.29/1.03  
% 2.29/1.03  ------ Input Options
% 2.29/1.03  
% 2.29/1.03  --out_options                           all
% 2.29/1.03  --tptp_safe_out                         true
% 2.29/1.03  --problem_path                          ""
% 2.29/1.03  --include_path                          ""
% 2.29/1.03  --clausifier                            res/vclausify_rel
% 2.29/1.03  --clausifier_options                    --mode clausify
% 2.29/1.03  --stdin                                 false
% 2.29/1.03  --stats_out                             all
% 2.29/1.03  
% 2.29/1.03  ------ General Options
% 2.29/1.03  
% 2.29/1.03  --fof                                   false
% 2.29/1.03  --time_out_real                         305.
% 2.29/1.03  --time_out_virtual                      -1.
% 2.29/1.03  --symbol_type_check                     false
% 2.29/1.03  --clausify_out                          false
% 2.29/1.03  --sig_cnt_out                           false
% 2.29/1.03  --trig_cnt_out                          false
% 2.29/1.03  --trig_cnt_out_tolerance                1.
% 2.29/1.03  --trig_cnt_out_sk_spl                   false
% 2.29/1.03  --abstr_cl_out                          false
% 2.29/1.03  
% 2.29/1.03  ------ Global Options
% 2.29/1.03  
% 2.29/1.03  --schedule                              default
% 2.29/1.03  --add_important_lit                     false
% 2.29/1.03  --prop_solver_per_cl                    1000
% 2.29/1.03  --min_unsat_core                        false
% 2.29/1.03  --soft_assumptions                      false
% 2.29/1.03  --soft_lemma_size                       3
% 2.29/1.03  --prop_impl_unit_size                   0
% 2.29/1.03  --prop_impl_unit                        []
% 2.29/1.03  --share_sel_clauses                     true
% 2.29/1.03  --reset_solvers                         false
% 2.29/1.03  --bc_imp_inh                            [conj_cone]
% 2.29/1.03  --conj_cone_tolerance                   3.
% 2.29/1.03  --extra_neg_conj                        none
% 2.29/1.03  --large_theory_mode                     true
% 2.29/1.03  --prolific_symb_bound                   200
% 2.29/1.03  --lt_threshold                          2000
% 2.29/1.03  --clause_weak_htbl                      true
% 2.29/1.03  --gc_record_bc_elim                     false
% 2.29/1.03  
% 2.29/1.03  ------ Preprocessing Options
% 2.29/1.03  
% 2.29/1.03  --preprocessing_flag                    true
% 2.29/1.03  --time_out_prep_mult                    0.1
% 2.29/1.03  --splitting_mode                        input
% 2.29/1.03  --splitting_grd                         true
% 2.29/1.03  --splitting_cvd                         false
% 2.29/1.03  --splitting_cvd_svl                     false
% 2.29/1.03  --splitting_nvd                         32
% 2.29/1.03  --sub_typing                            true
% 2.29/1.03  --prep_gs_sim                           true
% 2.29/1.03  --prep_unflatten                        true
% 2.29/1.03  --prep_res_sim                          true
% 2.29/1.03  --prep_upred                            true
% 2.29/1.03  --prep_sem_filter                       exhaustive
% 2.29/1.03  --prep_sem_filter_out                   false
% 2.29/1.03  --pred_elim                             true
% 2.29/1.03  --res_sim_input                         true
% 2.29/1.03  --eq_ax_congr_red                       true
% 2.29/1.03  --pure_diseq_elim                       true
% 2.29/1.03  --brand_transform                       false
% 2.29/1.03  --non_eq_to_eq                          false
% 2.29/1.03  --prep_def_merge                        true
% 2.29/1.03  --prep_def_merge_prop_impl              false
% 2.29/1.03  --prep_def_merge_mbd                    true
% 2.29/1.03  --prep_def_merge_tr_red                 false
% 2.29/1.03  --prep_def_merge_tr_cl                  false
% 2.29/1.03  --smt_preprocessing                     true
% 2.29/1.03  --smt_ac_axioms                         fast
% 2.29/1.03  --preprocessed_out                      false
% 2.29/1.03  --preprocessed_stats                    false
% 2.29/1.03  
% 2.29/1.03  ------ Abstraction refinement Options
% 2.29/1.03  
% 2.29/1.03  --abstr_ref                             []
% 2.29/1.03  --abstr_ref_prep                        false
% 2.29/1.03  --abstr_ref_until_sat                   false
% 2.29/1.03  --abstr_ref_sig_restrict                funpre
% 2.29/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.29/1.03  --abstr_ref_under                       []
% 2.29/1.03  
% 2.29/1.03  ------ SAT Options
% 2.29/1.03  
% 2.29/1.03  --sat_mode                              false
% 2.29/1.03  --sat_fm_restart_options                ""
% 2.29/1.03  --sat_gr_def                            false
% 2.29/1.03  --sat_epr_types                         true
% 2.29/1.03  --sat_non_cyclic_types                  false
% 2.29/1.03  --sat_finite_models                     false
% 2.29/1.03  --sat_fm_lemmas                         false
% 2.29/1.03  --sat_fm_prep                           false
% 2.29/1.03  --sat_fm_uc_incr                        true
% 2.29/1.03  --sat_out_model                         small
% 2.29/1.03  --sat_out_clauses                       false
% 2.29/1.03  
% 2.29/1.03  ------ QBF Options
% 2.29/1.03  
% 2.29/1.03  --qbf_mode                              false
% 2.29/1.03  --qbf_elim_univ                         false
% 2.29/1.03  --qbf_dom_inst                          none
% 2.29/1.03  --qbf_dom_pre_inst                      false
% 2.29/1.03  --qbf_sk_in                             false
% 2.29/1.03  --qbf_pred_elim                         true
% 2.29/1.03  --qbf_split                             512
% 2.29/1.03  
% 2.29/1.03  ------ BMC1 Options
% 2.29/1.03  
% 2.29/1.03  --bmc1_incremental                      false
% 2.29/1.03  --bmc1_axioms                           reachable_all
% 2.29/1.03  --bmc1_min_bound                        0
% 2.29/1.03  --bmc1_max_bound                        -1
% 2.29/1.03  --bmc1_max_bound_default                -1
% 2.29/1.03  --bmc1_symbol_reachability              true
% 2.29/1.03  --bmc1_property_lemmas                  false
% 2.29/1.03  --bmc1_k_induction                      false
% 2.29/1.03  --bmc1_non_equiv_states                 false
% 2.29/1.03  --bmc1_deadlock                         false
% 2.29/1.03  --bmc1_ucm                              false
% 2.29/1.03  --bmc1_add_unsat_core                   none
% 2.29/1.03  --bmc1_unsat_core_children              false
% 2.29/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.29/1.03  --bmc1_out_stat                         full
% 2.29/1.03  --bmc1_ground_init                      false
% 2.29/1.03  --bmc1_pre_inst_next_state              false
% 2.29/1.03  --bmc1_pre_inst_state                   false
% 2.29/1.03  --bmc1_pre_inst_reach_state             false
% 2.29/1.03  --bmc1_out_unsat_core                   false
% 2.29/1.03  --bmc1_aig_witness_out                  false
% 2.29/1.03  --bmc1_verbose                          false
% 2.29/1.03  --bmc1_dump_clauses_tptp                false
% 2.29/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.29/1.03  --bmc1_dump_file                        -
% 2.29/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.29/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.29/1.03  --bmc1_ucm_extend_mode                  1
% 2.29/1.03  --bmc1_ucm_init_mode                    2
% 2.29/1.03  --bmc1_ucm_cone_mode                    none
% 2.29/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.29/1.03  --bmc1_ucm_relax_model                  4
% 2.29/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.29/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.29/1.03  --bmc1_ucm_layered_model                none
% 2.29/1.03  --bmc1_ucm_max_lemma_size               10
% 2.29/1.03  
% 2.29/1.03  ------ AIG Options
% 2.29/1.03  
% 2.29/1.03  --aig_mode                              false
% 2.29/1.03  
% 2.29/1.03  ------ Instantiation Options
% 2.29/1.03  
% 2.29/1.03  --instantiation_flag                    true
% 2.29/1.03  --inst_sos_flag                         false
% 2.29/1.03  --inst_sos_phase                        true
% 2.29/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.29/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.29/1.03  --inst_lit_sel_side                     num_symb
% 2.29/1.03  --inst_solver_per_active                1400
% 2.29/1.03  --inst_solver_calls_frac                1.
% 2.29/1.03  --inst_passive_queue_type               priority_queues
% 2.29/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.29/1.03  --inst_passive_queues_freq              [25;2]
% 2.29/1.03  --inst_dismatching                      true
% 2.29/1.03  --inst_eager_unprocessed_to_passive     true
% 2.29/1.03  --inst_prop_sim_given                   true
% 2.29/1.03  --inst_prop_sim_new                     false
% 2.29/1.03  --inst_subs_new                         false
% 2.29/1.03  --inst_eq_res_simp                      false
% 2.29/1.03  --inst_subs_given                       false
% 2.29/1.03  --inst_orphan_elimination               true
% 2.29/1.03  --inst_learning_loop_flag               true
% 2.29/1.03  --inst_learning_start                   3000
% 2.29/1.03  --inst_learning_factor                  2
% 2.29/1.03  --inst_start_prop_sim_after_learn       3
% 2.29/1.03  --inst_sel_renew                        solver
% 2.29/1.03  --inst_lit_activity_flag                true
% 2.29/1.03  --inst_restr_to_given                   false
% 2.29/1.03  --inst_activity_threshold               500
% 2.29/1.03  --inst_out_proof                        true
% 2.29/1.03  
% 2.29/1.03  ------ Resolution Options
% 2.29/1.03  
% 2.29/1.03  --resolution_flag                       true
% 2.29/1.03  --res_lit_sel                           adaptive
% 2.29/1.03  --res_lit_sel_side                      none
% 2.29/1.03  --res_ordering                          kbo
% 2.29/1.03  --res_to_prop_solver                    active
% 2.29/1.03  --res_prop_simpl_new                    false
% 2.29/1.03  --res_prop_simpl_given                  true
% 2.29/1.03  --res_passive_queue_type                priority_queues
% 2.29/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.29/1.03  --res_passive_queues_freq               [15;5]
% 2.29/1.03  --res_forward_subs                      full
% 2.29/1.03  --res_backward_subs                     full
% 2.29/1.03  --res_forward_subs_resolution           true
% 2.29/1.03  --res_backward_subs_resolution          true
% 2.29/1.03  --res_orphan_elimination                true
% 2.29/1.03  --res_time_limit                        2.
% 2.29/1.03  --res_out_proof                         true
% 2.29/1.03  
% 2.29/1.03  ------ Superposition Options
% 2.29/1.03  
% 2.29/1.03  --superposition_flag                    true
% 2.29/1.03  --sup_passive_queue_type                priority_queues
% 2.29/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.29/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.29/1.03  --demod_completeness_check              fast
% 2.29/1.03  --demod_use_ground                      true
% 2.29/1.03  --sup_to_prop_solver                    passive
% 2.29/1.03  --sup_prop_simpl_new                    true
% 2.29/1.03  --sup_prop_simpl_given                  true
% 2.29/1.03  --sup_fun_splitting                     false
% 2.29/1.03  --sup_smt_interval                      50000
% 2.29/1.03  
% 2.29/1.03  ------ Superposition Simplification Setup
% 2.29/1.03  
% 2.29/1.03  --sup_indices_passive                   []
% 2.29/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.29/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.29/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.29/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.29/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.29/1.03  --sup_full_bw                           [BwDemod]
% 2.29/1.03  --sup_immed_triv                        [TrivRules]
% 2.29/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.29/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.29/1.03  --sup_immed_bw_main                     []
% 2.29/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.29/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.29/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.29/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.29/1.03  
% 2.29/1.03  ------ Combination Options
% 2.29/1.03  
% 2.29/1.03  --comb_res_mult                         3
% 2.29/1.03  --comb_sup_mult                         2
% 2.29/1.03  --comb_inst_mult                        10
% 2.29/1.03  
% 2.29/1.03  ------ Debug Options
% 2.29/1.03  
% 2.29/1.03  --dbg_backtrace                         false
% 2.29/1.03  --dbg_dump_prop_clauses                 false
% 2.29/1.03  --dbg_dump_prop_clauses_file            -
% 2.29/1.03  --dbg_out_stat                          false
% 2.29/1.03  ------ Parsing...
% 2.29/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.29/1.03  
% 2.29/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e 
% 2.29/1.03  
% 2.29/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.29/1.03  
% 2.29/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.29/1.03  ------ Proving...
% 2.29/1.03  ------ Problem Properties 
% 2.29/1.03  
% 2.29/1.03  
% 2.29/1.03  clauses                                 11
% 2.29/1.03  conjectures                             1
% 2.29/1.03  EPR                                     1
% 2.29/1.03  Horn                                    11
% 2.29/1.03  unary                                   5
% 2.29/1.03  binary                                  6
% 2.29/1.03  lits                                    17
% 2.29/1.03  lits eq                                 10
% 2.29/1.03  fd_pure                                 0
% 2.29/1.03  fd_pseudo                               0
% 2.29/1.03  fd_cond                                 0
% 2.29/1.03  fd_pseudo_cond                          0
% 2.29/1.03  AC symbols                              0
% 2.29/1.03  
% 2.29/1.03  ------ Schedule dynamic 5 is on 
% 2.29/1.03  
% 2.29/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.29/1.03  
% 2.29/1.03  
% 2.29/1.03  ------ 
% 2.29/1.03  Current options:
% 2.29/1.03  ------ 
% 2.29/1.03  
% 2.29/1.03  ------ Input Options
% 2.29/1.03  
% 2.29/1.03  --out_options                           all
% 2.29/1.03  --tptp_safe_out                         true
% 2.29/1.03  --problem_path                          ""
% 2.29/1.03  --include_path                          ""
% 2.29/1.03  --clausifier                            res/vclausify_rel
% 2.29/1.03  --clausifier_options                    --mode clausify
% 2.29/1.03  --stdin                                 false
% 2.29/1.03  --stats_out                             all
% 2.29/1.03  
% 2.29/1.03  ------ General Options
% 2.29/1.03  
% 2.29/1.03  --fof                                   false
% 2.29/1.03  --time_out_real                         305.
% 2.29/1.03  --time_out_virtual                      -1.
% 2.29/1.03  --symbol_type_check                     false
% 2.29/1.03  --clausify_out                          false
% 2.29/1.03  --sig_cnt_out                           false
% 2.29/1.03  --trig_cnt_out                          false
% 2.29/1.03  --trig_cnt_out_tolerance                1.
% 2.29/1.03  --trig_cnt_out_sk_spl                   false
% 2.29/1.03  --abstr_cl_out                          false
% 2.29/1.03  
% 2.29/1.03  ------ Global Options
% 2.29/1.03  
% 2.29/1.03  --schedule                              default
% 2.29/1.03  --add_important_lit                     false
% 2.29/1.03  --prop_solver_per_cl                    1000
% 2.29/1.03  --min_unsat_core                        false
% 2.29/1.03  --soft_assumptions                      false
% 2.29/1.03  --soft_lemma_size                       3
% 2.29/1.03  --prop_impl_unit_size                   0
% 2.29/1.03  --prop_impl_unit                        []
% 2.29/1.03  --share_sel_clauses                     true
% 2.29/1.03  --reset_solvers                         false
% 2.29/1.03  --bc_imp_inh                            [conj_cone]
% 2.29/1.03  --conj_cone_tolerance                   3.
% 2.29/1.03  --extra_neg_conj                        none
% 2.29/1.03  --large_theory_mode                     true
% 2.29/1.03  --prolific_symb_bound                   200
% 2.29/1.03  --lt_threshold                          2000
% 2.29/1.03  --clause_weak_htbl                      true
% 2.29/1.03  --gc_record_bc_elim                     false
% 2.29/1.03  
% 2.29/1.03  ------ Preprocessing Options
% 2.29/1.03  
% 2.29/1.03  --preprocessing_flag                    true
% 2.29/1.03  --time_out_prep_mult                    0.1
% 2.29/1.03  --splitting_mode                        input
% 2.29/1.03  --splitting_grd                         true
% 2.29/1.03  --splitting_cvd                         false
% 2.29/1.03  --splitting_cvd_svl                     false
% 2.29/1.03  --splitting_nvd                         32
% 2.29/1.03  --sub_typing                            true
% 2.29/1.03  --prep_gs_sim                           true
% 2.29/1.03  --prep_unflatten                        true
% 2.29/1.03  --prep_res_sim                          true
% 2.29/1.03  --prep_upred                            true
% 2.29/1.03  --prep_sem_filter                       exhaustive
% 2.29/1.03  --prep_sem_filter_out                   false
% 2.29/1.03  --pred_elim                             true
% 2.29/1.03  --res_sim_input                         true
% 2.29/1.03  --eq_ax_congr_red                       true
% 2.29/1.03  --pure_diseq_elim                       true
% 2.29/1.03  --brand_transform                       false
% 2.29/1.03  --non_eq_to_eq                          false
% 2.29/1.03  --prep_def_merge                        true
% 2.29/1.03  --prep_def_merge_prop_impl              false
% 2.29/1.03  --prep_def_merge_mbd                    true
% 2.29/1.03  --prep_def_merge_tr_red                 false
% 2.29/1.03  --prep_def_merge_tr_cl                  false
% 2.29/1.03  --smt_preprocessing                     true
% 2.29/1.03  --smt_ac_axioms                         fast
% 2.29/1.03  --preprocessed_out                      false
% 2.29/1.03  --preprocessed_stats                    false
% 2.29/1.03  
% 2.29/1.03  ------ Abstraction refinement Options
% 2.29/1.03  
% 2.29/1.03  --abstr_ref                             []
% 2.29/1.03  --abstr_ref_prep                        false
% 2.29/1.03  --abstr_ref_until_sat                   false
% 2.29/1.03  --abstr_ref_sig_restrict                funpre
% 2.29/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.29/1.03  --abstr_ref_under                       []
% 2.29/1.03  
% 2.29/1.03  ------ SAT Options
% 2.29/1.03  
% 2.29/1.03  --sat_mode                              false
% 2.29/1.03  --sat_fm_restart_options                ""
% 2.29/1.03  --sat_gr_def                            false
% 2.29/1.03  --sat_epr_types                         true
% 2.29/1.03  --sat_non_cyclic_types                  false
% 2.29/1.03  --sat_finite_models                     false
% 2.29/1.03  --sat_fm_lemmas                         false
% 2.29/1.03  --sat_fm_prep                           false
% 2.29/1.03  --sat_fm_uc_incr                        true
% 2.29/1.03  --sat_out_model                         small
% 2.29/1.03  --sat_out_clauses                       false
% 2.29/1.03  
% 2.29/1.03  ------ QBF Options
% 2.29/1.03  
% 2.29/1.03  --qbf_mode                              false
% 2.29/1.03  --qbf_elim_univ                         false
% 2.29/1.03  --qbf_dom_inst                          none
% 2.29/1.03  --qbf_dom_pre_inst                      false
% 2.29/1.03  --qbf_sk_in                             false
% 2.29/1.03  --qbf_pred_elim                         true
% 2.29/1.03  --qbf_split                             512
% 2.29/1.03  
% 2.29/1.03  ------ BMC1 Options
% 2.29/1.03  
% 2.29/1.03  --bmc1_incremental                      false
% 2.29/1.03  --bmc1_axioms                           reachable_all
% 2.29/1.03  --bmc1_min_bound                        0
% 2.29/1.03  --bmc1_max_bound                        -1
% 2.29/1.03  --bmc1_max_bound_default                -1
% 2.29/1.03  --bmc1_symbol_reachability              true
% 2.29/1.03  --bmc1_property_lemmas                  false
% 2.29/1.03  --bmc1_k_induction                      false
% 2.29/1.03  --bmc1_non_equiv_states                 false
% 2.29/1.03  --bmc1_deadlock                         false
% 2.29/1.03  --bmc1_ucm                              false
% 2.29/1.03  --bmc1_add_unsat_core                   none
% 2.29/1.03  --bmc1_unsat_core_children              false
% 2.29/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.29/1.03  --bmc1_out_stat                         full
% 2.29/1.03  --bmc1_ground_init                      false
% 2.29/1.03  --bmc1_pre_inst_next_state              false
% 2.29/1.03  --bmc1_pre_inst_state                   false
% 2.29/1.03  --bmc1_pre_inst_reach_state             false
% 2.29/1.03  --bmc1_out_unsat_core                   false
% 2.29/1.03  --bmc1_aig_witness_out                  false
% 2.29/1.03  --bmc1_verbose                          false
% 2.29/1.03  --bmc1_dump_clauses_tptp                false
% 2.29/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.29/1.03  --bmc1_dump_file                        -
% 2.29/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.29/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.29/1.03  --bmc1_ucm_extend_mode                  1
% 2.29/1.03  --bmc1_ucm_init_mode                    2
% 2.29/1.03  --bmc1_ucm_cone_mode                    none
% 2.29/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.29/1.03  --bmc1_ucm_relax_model                  4
% 2.29/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.29/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.29/1.03  --bmc1_ucm_layered_model                none
% 2.29/1.03  --bmc1_ucm_max_lemma_size               10
% 2.29/1.03  
% 2.29/1.03  ------ AIG Options
% 2.29/1.03  
% 2.29/1.03  --aig_mode                              false
% 2.29/1.03  
% 2.29/1.03  ------ Instantiation Options
% 2.29/1.03  
% 2.29/1.03  --instantiation_flag                    true
% 2.29/1.03  --inst_sos_flag                         false
% 2.29/1.03  --inst_sos_phase                        true
% 2.29/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.29/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.29/1.03  --inst_lit_sel_side                     none
% 2.29/1.03  --inst_solver_per_active                1400
% 2.29/1.03  --inst_solver_calls_frac                1.
% 2.29/1.03  --inst_passive_queue_type               priority_queues
% 2.29/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.29/1.03  --inst_passive_queues_freq              [25;2]
% 2.29/1.03  --inst_dismatching                      true
% 2.29/1.03  --inst_eager_unprocessed_to_passive     true
% 2.29/1.03  --inst_prop_sim_given                   true
% 2.29/1.03  --inst_prop_sim_new                     false
% 2.29/1.03  --inst_subs_new                         false
% 2.29/1.03  --inst_eq_res_simp                      false
% 2.29/1.03  --inst_subs_given                       false
% 2.29/1.03  --inst_orphan_elimination               true
% 2.29/1.03  --inst_learning_loop_flag               true
% 2.29/1.03  --inst_learning_start                   3000
% 2.29/1.03  --inst_learning_factor                  2
% 2.29/1.03  --inst_start_prop_sim_after_learn       3
% 2.29/1.03  --inst_sel_renew                        solver
% 2.29/1.03  --inst_lit_activity_flag                true
% 2.29/1.03  --inst_restr_to_given                   false
% 2.29/1.03  --inst_activity_threshold               500
% 2.29/1.03  --inst_out_proof                        true
% 2.29/1.03  
% 2.29/1.03  ------ Resolution Options
% 2.29/1.03  
% 2.29/1.03  --resolution_flag                       false
% 2.29/1.03  --res_lit_sel                           adaptive
% 2.29/1.03  --res_lit_sel_side                      none
% 2.29/1.03  --res_ordering                          kbo
% 2.29/1.03  --res_to_prop_solver                    active
% 2.29/1.03  --res_prop_simpl_new                    false
% 2.29/1.03  --res_prop_simpl_given                  true
% 2.29/1.03  --res_passive_queue_type                priority_queues
% 2.29/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.29/1.03  --res_passive_queues_freq               [15;5]
% 2.29/1.03  --res_forward_subs                      full
% 2.29/1.03  --res_backward_subs                     full
% 2.29/1.03  --res_forward_subs_resolution           true
% 2.29/1.03  --res_backward_subs_resolution          true
% 2.29/1.03  --res_orphan_elimination                true
% 2.29/1.03  --res_time_limit                        2.
% 2.29/1.03  --res_out_proof                         true
% 2.29/1.03  
% 2.29/1.03  ------ Superposition Options
% 2.29/1.03  
% 2.29/1.03  --superposition_flag                    true
% 2.29/1.03  --sup_passive_queue_type                priority_queues
% 2.29/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.29/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.29/1.03  --demod_completeness_check              fast
% 2.29/1.03  --demod_use_ground                      true
% 2.29/1.03  --sup_to_prop_solver                    passive
% 2.29/1.03  --sup_prop_simpl_new                    true
% 2.29/1.03  --sup_prop_simpl_given                  true
% 2.29/1.03  --sup_fun_splitting                     false
% 2.29/1.03  --sup_smt_interval                      50000
% 2.29/1.03  
% 2.29/1.03  ------ Superposition Simplification Setup
% 2.29/1.03  
% 2.29/1.03  --sup_indices_passive                   []
% 2.29/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.29/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.29/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.29/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.29/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.29/1.03  --sup_full_bw                           [BwDemod]
% 2.29/1.03  --sup_immed_triv                        [TrivRules]
% 2.29/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.29/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.29/1.03  --sup_immed_bw_main                     []
% 2.29/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.29/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.29/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.29/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.29/1.03  
% 2.29/1.03  ------ Combination Options
% 2.29/1.03  
% 2.29/1.03  --comb_res_mult                         3
% 2.29/1.03  --comb_sup_mult                         2
% 2.29/1.03  --comb_inst_mult                        10
% 2.29/1.03  
% 2.29/1.03  ------ Debug Options
% 2.29/1.03  
% 2.29/1.03  --dbg_backtrace                         false
% 2.29/1.03  --dbg_dump_prop_clauses                 false
% 2.29/1.03  --dbg_dump_prop_clauses_file            -
% 2.29/1.03  --dbg_out_stat                          false
% 2.29/1.03  
% 2.29/1.03  
% 2.29/1.03  
% 2.29/1.03  
% 2.29/1.03  ------ Proving...
% 2.29/1.03  
% 2.29/1.03  
% 2.29/1.03  % SZS status Theorem for theBenchmark.p
% 2.29/1.03  
% 2.29/1.03   Resolution empty clause
% 2.29/1.03  
% 2.29/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 2.29/1.03  
% 2.29/1.03  fof(f10,conjecture,(
% 2.29/1.03    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 2.29/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.29/1.03  
% 2.29/1.03  fof(f11,negated_conjecture,(
% 2.29/1.03    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 2.29/1.03    inference(negated_conjecture,[],[f10])).
% 2.29/1.03  
% 2.29/1.03  fof(f18,plain,(
% 2.29/1.03    ? [X0,X1] : ((~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 2.29/1.03    inference(ennf_transformation,[],[f11])).
% 2.29/1.03  
% 2.29/1.03  fof(f19,plain,(
% 2.29/1.03    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 2.29/1.03    inference(flattening,[],[f18])).
% 2.29/1.03  
% 2.29/1.03  fof(f20,plain,(
% 2.29/1.03    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 2.29/1.03    introduced(choice_axiom,[])).
% 2.29/1.03  
% 2.29/1.03  fof(f21,plain,(
% 2.29/1.03    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1)),
% 2.29/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f20])).
% 2.29/1.03  
% 2.29/1.03  fof(f31,plain,(
% 2.29/1.03    v1_relat_1(sK1)),
% 2.29/1.03    inference(cnf_transformation,[],[f21])).
% 2.29/1.03  
% 2.29/1.03  fof(f5,axiom,(
% 2.29/1.03    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 2.29/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.29/1.03  
% 2.29/1.03  fof(f13,plain,(
% 2.29/1.03    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 2.29/1.03    inference(ennf_transformation,[],[f5])).
% 2.29/1.03  
% 2.29/1.03  fof(f26,plain,(
% 2.29/1.03    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 2.29/1.03    inference(cnf_transformation,[],[f13])).
% 2.29/1.03  
% 2.29/1.03  fof(f7,axiom,(
% 2.29/1.03    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 2.29/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.29/1.03  
% 2.29/1.03  fof(f15,plain,(
% 2.29/1.03    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 2.29/1.03    inference(ennf_transformation,[],[f7])).
% 2.29/1.03  
% 2.29/1.03  fof(f28,plain,(
% 2.29/1.03    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.29/1.03    inference(cnf_transformation,[],[f15])).
% 2.29/1.03  
% 2.29/1.03  fof(f6,axiom,(
% 2.29/1.03    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 2.29/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.29/1.03  
% 2.29/1.03  fof(f14,plain,(
% 2.29/1.03    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.29/1.03    inference(ennf_transformation,[],[f6])).
% 2.29/1.03  
% 2.29/1.03  fof(f27,plain,(
% 2.29/1.03    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.29/1.03    inference(cnf_transformation,[],[f14])).
% 2.29/1.03  
% 2.29/1.03  fof(f9,axiom,(
% 2.29/1.03    ! [X0,X1,X2] : (v1_relat_1(X2) => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1))),
% 2.29/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.29/1.03  
% 2.29/1.03  fof(f17,plain,(
% 2.29/1.03    ! [X0,X1,X2] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 2.29/1.03    inference(ennf_transformation,[],[f9])).
% 2.29/1.03  
% 2.29/1.03  fof(f30,plain,(
% 2.29/1.03    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 2.29/1.03    inference(cnf_transformation,[],[f17])).
% 2.29/1.03  
% 2.29/1.03  fof(f4,axiom,(
% 2.29/1.03    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.29/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.29/1.03  
% 2.29/1.03  fof(f25,plain,(
% 2.29/1.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.29/1.03    inference(cnf_transformation,[],[f4])).
% 2.29/1.03  
% 2.29/1.03  fof(f37,plain,(
% 2.29/1.03    ( ! [X2,X0,X1] : (k1_setfam_1(k2_tarski(X0,k10_relat_1(X2,X1))) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 2.29/1.03    inference(definition_unfolding,[],[f30,f25])).
% 2.29/1.03  
% 2.29/1.03  fof(f3,axiom,(
% 2.29/1.03    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.29/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.29/1.03  
% 2.29/1.03  fof(f24,plain,(
% 2.29/1.03    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.29/1.03    inference(cnf_transformation,[],[f3])).
% 2.29/1.03  
% 2.29/1.03  fof(f1,axiom,(
% 2.29/1.03    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 2.29/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.29/1.03  
% 2.29/1.03  fof(f22,plain,(
% 2.29/1.03    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.29/1.03    inference(cnf_transformation,[],[f1])).
% 2.29/1.03  
% 2.29/1.03  fof(f34,plain,(
% 2.29/1.03    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) )),
% 2.29/1.03    inference(definition_unfolding,[],[f22,f25])).
% 2.29/1.03  
% 2.29/1.03  fof(f33,plain,(
% 2.29/1.03    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 2.29/1.03    inference(cnf_transformation,[],[f21])).
% 2.29/1.03  
% 2.29/1.03  fof(f2,axiom,(
% 2.29/1.03    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.29/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.29/1.03  
% 2.29/1.03  fof(f12,plain,(
% 2.29/1.03    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.29/1.03    inference(ennf_transformation,[],[f2])).
% 2.29/1.03  
% 2.29/1.03  fof(f23,plain,(
% 2.29/1.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.29/1.03    inference(cnf_transformation,[],[f12])).
% 2.29/1.03  
% 2.29/1.03  fof(f35,plain,(
% 2.29/1.03    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 2.29/1.03    inference(definition_unfolding,[],[f23,f25])).
% 2.29/1.03  
% 2.29/1.03  fof(f32,plain,(
% 2.29/1.03    r1_tarski(sK0,k1_relat_1(sK1))),
% 2.29/1.03    inference(cnf_transformation,[],[f21])).
% 2.29/1.03  
% 2.29/1.03  fof(f8,axiom,(
% 2.29/1.03    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)))),
% 2.29/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.29/1.03  
% 2.29/1.03  fof(f16,plain,(
% 2.29/1.03    ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 2.29/1.03    inference(ennf_transformation,[],[f8])).
% 2.29/1.03  
% 2.29/1.03  fof(f29,plain,(
% 2.29/1.03    ( ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 2.29/1.03    inference(cnf_transformation,[],[f16])).
% 2.29/1.03  
% 2.29/1.03  fof(f36,plain,(
% 2.29/1.03    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 2.29/1.03    inference(definition_unfolding,[],[f29,f25])).
% 2.29/1.03  
% 2.29/1.03  cnf(c_10,negated_conjecture,
% 2.29/1.03      ( v1_relat_1(sK1) ),
% 2.29/1.03      inference(cnf_transformation,[],[f31]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_156,negated_conjecture,
% 2.29/1.03      ( v1_relat_1(sK1) ),
% 2.29/1.03      inference(subtyping,[status(esa)],[c_10]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_316,plain,
% 2.29/1.03      ( v1_relat_1(sK1) = iProver_top ),
% 2.29/1.03      inference(predicate_to_equality,[status(thm)],[c_156]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_3,plain,
% 2.29/1.03      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 2.29/1.03      inference(cnf_transformation,[],[f26]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_161,plain,
% 2.29/1.03      ( ~ v1_relat_1(X0_40) | v1_relat_1(k7_relat_1(X0_40,X0_39)) ),
% 2.29/1.03      inference(subtyping,[status(esa)],[c_3]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_311,plain,
% 2.29/1.03      ( v1_relat_1(X0_40) != iProver_top
% 2.29/1.03      | v1_relat_1(k7_relat_1(X0_40,X0_39)) = iProver_top ),
% 2.29/1.03      inference(predicate_to_equality,[status(thm)],[c_161]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_5,plain,
% 2.29/1.03      ( ~ v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 2.29/1.03      inference(cnf_transformation,[],[f28]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_159,plain,
% 2.29/1.03      ( ~ v1_relat_1(X0_40)
% 2.29/1.03      | k10_relat_1(X0_40,k2_relat_1(X0_40)) = k1_relat_1(X0_40) ),
% 2.29/1.03      inference(subtyping,[status(esa)],[c_5]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_313,plain,
% 2.29/1.03      ( k10_relat_1(X0_40,k2_relat_1(X0_40)) = k1_relat_1(X0_40)
% 2.29/1.03      | v1_relat_1(X0_40) != iProver_top ),
% 2.29/1.03      inference(predicate_to_equality,[status(thm)],[c_159]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_679,plain,
% 2.29/1.03      ( k10_relat_1(k7_relat_1(X0_40,X0_39),k2_relat_1(k7_relat_1(X0_40,X0_39))) = k1_relat_1(k7_relat_1(X0_40,X0_39))
% 2.29/1.03      | v1_relat_1(X0_40) != iProver_top ),
% 2.29/1.03      inference(superposition,[status(thm)],[c_311,c_313]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_2000,plain,
% 2.29/1.03      ( k10_relat_1(k7_relat_1(sK1,X0_39),k2_relat_1(k7_relat_1(sK1,X0_39))) = k1_relat_1(k7_relat_1(sK1,X0_39)) ),
% 2.29/1.03      inference(superposition,[status(thm)],[c_316,c_679]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_4,plain,
% 2.29/1.03      ( ~ v1_relat_1(X0) | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 2.29/1.03      inference(cnf_transformation,[],[f27]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_160,plain,
% 2.29/1.03      ( ~ v1_relat_1(X0_40)
% 2.29/1.03      | k2_relat_1(k7_relat_1(X0_40,X0_39)) = k9_relat_1(X0_40,X0_39) ),
% 2.29/1.03      inference(subtyping,[status(esa)],[c_4]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_312,plain,
% 2.29/1.03      ( k2_relat_1(k7_relat_1(X0_40,X0_39)) = k9_relat_1(X0_40,X0_39)
% 2.29/1.03      | v1_relat_1(X0_40) != iProver_top ),
% 2.29/1.03      inference(predicate_to_equality,[status(thm)],[c_160]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_805,plain,
% 2.29/1.03      ( k2_relat_1(k7_relat_1(sK1,X0_39)) = k9_relat_1(sK1,X0_39) ),
% 2.29/1.03      inference(superposition,[status(thm)],[c_316,c_312]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_2007,plain,
% 2.29/1.03      ( k10_relat_1(k7_relat_1(sK1,X0_39),k9_relat_1(sK1,X0_39)) = k1_relat_1(k7_relat_1(sK1,X0_39)) ),
% 2.29/1.03      inference(light_normalisation,[status(thm)],[c_2000,c_805]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_7,plain,
% 2.29/1.03      ( ~ v1_relat_1(X0)
% 2.29/1.03      | k1_setfam_1(k2_tarski(X1,k10_relat_1(X0,X2))) = k10_relat_1(k7_relat_1(X0,X1),X2) ),
% 2.29/1.03      inference(cnf_transformation,[],[f37]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_157,plain,
% 2.29/1.03      ( ~ v1_relat_1(X0_40)
% 2.29/1.03      | k1_setfam_1(k2_tarski(X0_39,k10_relat_1(X0_40,X0_41))) = k10_relat_1(k7_relat_1(X0_40,X0_39),X0_41) ),
% 2.29/1.03      inference(subtyping,[status(esa)],[c_7]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_315,plain,
% 2.29/1.03      ( k1_setfam_1(k2_tarski(X0_39,k10_relat_1(X0_40,X0_41))) = k10_relat_1(k7_relat_1(X0_40,X0_39),X0_41)
% 2.29/1.03      | v1_relat_1(X0_40) != iProver_top ),
% 2.29/1.03      inference(predicate_to_equality,[status(thm)],[c_157]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_1373,plain,
% 2.29/1.03      ( k1_setfam_1(k2_tarski(X0_39,k10_relat_1(sK1,X0_41))) = k10_relat_1(k7_relat_1(sK1,X0_39),X0_41) ),
% 2.29/1.03      inference(superposition,[status(thm)],[c_316,c_315]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_2,plain,
% 2.29/1.03      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 2.29/1.03      inference(cnf_transformation,[],[f24]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_162,plain,
% 2.29/1.03      ( k2_tarski(X0_39,X1_39) = k2_tarski(X1_39,X0_39) ),
% 2.29/1.03      inference(subtyping,[status(esa)],[c_2]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_0,plain,
% 2.29/1.03      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
% 2.29/1.03      inference(cnf_transformation,[],[f34]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_8,negated_conjecture,
% 2.29/1.03      ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
% 2.29/1.03      inference(cnf_transformation,[],[f33]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_129,plain,
% 2.29/1.03      ( k10_relat_1(sK1,k9_relat_1(sK1,sK0)) != X0
% 2.29/1.03      | k1_setfam_1(k2_tarski(X0,X1)) != sK0 ),
% 2.29/1.03      inference(resolution_lifted,[status(thm)],[c_0,c_8]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_130,plain,
% 2.29/1.03      ( k1_setfam_1(k2_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),X0)) != sK0 ),
% 2.29/1.03      inference(unflattening,[status(thm)],[c_129]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_154,plain,
% 2.29/1.03      ( k1_setfam_1(k2_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),X0_39)) != sK0 ),
% 2.29/1.03      inference(subtyping,[status(esa)],[c_130]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_393,plain,
% 2.29/1.03      ( k1_setfam_1(k2_tarski(X0_39,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))) != sK0 ),
% 2.29/1.03      inference(superposition,[status(thm)],[c_162,c_154]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_1535,plain,
% 2.29/1.03      ( k10_relat_1(k7_relat_1(sK1,X0_39),k9_relat_1(sK1,sK0)) != sK0 ),
% 2.29/1.03      inference(demodulation,[status(thm)],[c_1373,c_393]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_2905,plain,
% 2.29/1.03      ( k1_relat_1(k7_relat_1(sK1,sK0)) != sK0 ),
% 2.29/1.03      inference(superposition,[status(thm)],[c_2007,c_1535]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_1,plain,
% 2.29/1.03      ( ~ r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0 ),
% 2.29/1.03      inference(cnf_transformation,[],[f35]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_9,negated_conjecture,
% 2.29/1.03      ( r1_tarski(sK0,k1_relat_1(sK1)) ),
% 2.29/1.03      inference(cnf_transformation,[],[f32]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_135,plain,
% 2.29/1.03      ( k1_relat_1(sK1) != X0
% 2.29/1.03      | k1_setfam_1(k2_tarski(X1,X0)) = X1
% 2.29/1.03      | sK0 != X1 ),
% 2.29/1.03      inference(resolution_lifted,[status(thm)],[c_1,c_9]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_136,plain,
% 2.29/1.03      ( k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1))) = sK0 ),
% 2.29/1.03      inference(unflattening,[status(thm)],[c_135]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_153,plain,
% 2.29/1.03      ( k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1))) = sK0 ),
% 2.29/1.03      inference(subtyping,[status(esa)],[c_136]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_123,plain,
% 2.29/1.03      ( X0 != X1
% 2.29/1.03      | k1_setfam_1(k2_tarski(X1,X2)) != X3
% 2.29/1.03      | k1_setfam_1(k2_tarski(X3,X0)) = X3 ),
% 2.29/1.03      inference(resolution_lifted,[status(thm)],[c_0,c_1]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_124,plain,
% 2.29/1.03      ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) = k1_setfam_1(k2_tarski(X0,X1)) ),
% 2.29/1.03      inference(unflattening,[status(thm)],[c_123]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_155,plain,
% 2.29/1.03      ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0_39,X1_39)),X0_39)) = k1_setfam_1(k2_tarski(X0_39,X1_39)) ),
% 2.29/1.03      inference(subtyping,[status(esa)],[c_124]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_434,plain,
% 2.29/1.03      ( k1_setfam_1(k2_tarski(X0_39,k1_setfam_1(k2_tarski(X0_39,X1_39)))) = k1_setfam_1(k2_tarski(X0_39,X1_39)) ),
% 2.29/1.03      inference(superposition,[status(thm)],[c_162,c_155]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_440,plain,
% 2.29/1.03      ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0_39,X1_39)),k1_setfam_1(k2_tarski(X0_39,X1_39)))) = k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0_39,X1_39)),X0_39)) ),
% 2.29/1.03      inference(superposition,[status(thm)],[c_155,c_155]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_442,plain,
% 2.29/1.03      ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0_39,X1_39)),k1_setfam_1(k2_tarski(X0_39,X1_39)))) = k1_setfam_1(k2_tarski(X0_39,X1_39)) ),
% 2.29/1.03      inference(light_normalisation,[status(thm)],[c_440,c_155]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_938,plain,
% 2.29/1.03      ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0_39,X1_39)),k1_setfam_1(k2_tarski(X0_39,X1_39)))) = k1_setfam_1(k2_tarski(X0_39,k1_setfam_1(k2_tarski(X0_39,X1_39)))) ),
% 2.29/1.03      inference(superposition,[status(thm)],[c_434,c_442]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_942,plain,
% 2.29/1.03      ( k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0_39,X1_39)),k1_setfam_1(k2_tarski(X0_39,X1_39)))) = k1_setfam_1(k2_tarski(X1_39,X0_39)) ),
% 2.29/1.03      inference(superposition,[status(thm)],[c_162,c_442]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_952,plain,
% 2.29/1.03      ( k1_setfam_1(k2_tarski(X0_39,k1_setfam_1(k2_tarski(X0_39,X1_39)))) = k1_setfam_1(k2_tarski(X1_39,X0_39)) ),
% 2.29/1.03      inference(light_normalisation,[status(thm)],[c_938,c_942]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_1121,plain,
% 2.29/1.03      ( k1_setfam_1(k2_tarski(k1_relat_1(sK1),sK0)) = k1_setfam_1(k2_tarski(sK0,sK0)) ),
% 2.29/1.03      inference(superposition,[status(thm)],[c_153,c_952]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_436,plain,
% 2.29/1.03      ( k1_setfam_1(k2_tarski(sK0,k1_relat_1(sK1))) = k1_setfam_1(k2_tarski(sK0,sK0)) ),
% 2.29/1.03      inference(superposition,[status(thm)],[c_153,c_155]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_448,plain,
% 2.29/1.03      ( k1_setfam_1(k2_tarski(sK0,sK0)) = sK0 ),
% 2.29/1.03      inference(light_normalisation,[status(thm)],[c_436,c_153]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_1157,plain,
% 2.29/1.03      ( k1_setfam_1(k2_tarski(k1_relat_1(sK1),sK0)) = sK0 ),
% 2.29/1.03      inference(light_normalisation,[status(thm)],[c_1121,c_448]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_6,plain,
% 2.29/1.03      ( ~ v1_relat_1(X0)
% 2.29/1.03      | k1_setfam_1(k2_tarski(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
% 2.29/1.03      inference(cnf_transformation,[],[f36]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_158,plain,
% 2.29/1.03      ( ~ v1_relat_1(X0_40)
% 2.29/1.03      | k1_setfam_1(k2_tarski(k1_relat_1(X0_40),X0_39)) = k1_relat_1(k7_relat_1(X0_40,X0_39)) ),
% 2.29/1.03      inference(subtyping,[status(esa)],[c_6]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_314,plain,
% 2.29/1.03      ( k1_setfam_1(k2_tarski(k1_relat_1(X0_40),X0_39)) = k1_relat_1(k7_relat_1(X0_40,X0_39))
% 2.29/1.03      | v1_relat_1(X0_40) != iProver_top ),
% 2.29/1.03      inference(predicate_to_equality,[status(thm)],[c_158]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_1162,plain,
% 2.29/1.03      ( k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0_39)) = k1_relat_1(k7_relat_1(sK1,X0_39)) ),
% 2.29/1.03      inference(superposition,[status(thm)],[c_316,c_314]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_1682,plain,
% 2.29/1.03      ( k1_relat_1(k7_relat_1(sK1,sK0)) = sK0 ),
% 2.29/1.03      inference(superposition,[status(thm)],[c_1157,c_1162]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_2908,plain,
% 2.29/1.03      ( sK0 != sK0 ),
% 2.29/1.03      inference(light_normalisation,[status(thm)],[c_2905,c_1682]) ).
% 2.29/1.03  
% 2.29/1.03  cnf(c_2909,plain,
% 2.29/1.03      ( $false ),
% 2.29/1.03      inference(equality_resolution_simp,[status(thm)],[c_2908]) ).
% 2.29/1.03  
% 2.29/1.03  
% 2.29/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 2.29/1.03  
% 2.29/1.03  ------                               Statistics
% 2.29/1.03  
% 2.29/1.03  ------ General
% 2.29/1.03  
% 2.29/1.03  abstr_ref_over_cycles:                  0
% 2.29/1.03  abstr_ref_under_cycles:                 0
% 2.29/1.03  gc_basic_clause_elim:                   0
% 2.29/1.03  forced_gc_time:                         0
% 2.29/1.03  parsing_time:                           0.006
% 2.29/1.03  unif_index_cands_time:                  0.
% 2.29/1.03  unif_index_add_time:                    0.
% 2.29/1.03  orderings_time:                         0.
% 2.29/1.03  out_proof_time:                         0.008
% 2.29/1.03  total_time:                             0.144
% 2.29/1.03  num_of_symbols:                         43
% 2.29/1.03  num_of_terms:                           3117
% 2.29/1.03  
% 2.29/1.03  ------ Preprocessing
% 2.29/1.03  
% 2.29/1.03  num_of_splits:                          0
% 2.29/1.03  num_of_split_atoms:                     0
% 2.29/1.03  num_of_reused_defs:                     0
% 2.29/1.03  num_eq_ax_congr_red:                    4
% 2.29/1.03  num_of_sem_filtered_clauses:            1
% 2.29/1.03  num_of_subtypes:                        4
% 2.29/1.03  monotx_restored_types:                  0
% 2.29/1.03  sat_num_of_epr_types:                   0
% 2.29/1.03  sat_num_of_non_cyclic_types:            0
% 2.29/1.03  sat_guarded_non_collapsed_types:        0
% 2.29/1.03  num_pure_diseq_elim:                    0
% 2.29/1.03  simp_replaced_by:                       0
% 2.29/1.03  res_preprocessed:                       62
% 2.29/1.03  prep_upred:                             0
% 2.29/1.03  prep_unflattend:                        5
% 2.29/1.03  smt_new_axioms:                         0
% 2.29/1.03  pred_elim_cands:                        2
% 2.29/1.03  pred_elim:                              1
% 2.29/1.03  pred_elim_cl:                           0
% 2.29/1.03  pred_elim_cycles:                       2
% 2.29/1.03  merged_defs:                            0
% 2.29/1.03  merged_defs_ncl:                        0
% 2.29/1.03  bin_hyper_res:                          0
% 2.29/1.03  prep_cycles:                            3
% 2.29/1.03  pred_elim_time:                         0.001
% 2.29/1.03  splitting_time:                         0.
% 2.29/1.03  sem_filter_time:                        0.
% 2.29/1.03  monotx_time:                            0.
% 2.29/1.03  subtype_inf_time:                       0.
% 2.29/1.03  
% 2.29/1.03  ------ Problem properties
% 2.29/1.03  
% 2.29/1.03  clauses:                                11
% 2.29/1.03  conjectures:                            1
% 2.29/1.03  epr:                                    1
% 2.29/1.03  horn:                                   11
% 2.29/1.03  ground:                                 3
% 2.29/1.03  unary:                                  5
% 2.29/1.03  binary:                                 6
% 2.29/1.03  lits:                                   17
% 2.29/1.03  lits_eq:                                10
% 2.29/1.03  fd_pure:                                0
% 2.29/1.03  fd_pseudo:                              0
% 2.29/1.03  fd_cond:                                0
% 2.29/1.03  fd_pseudo_cond:                         0
% 2.29/1.03  ac_symbols:                             0
% 2.29/1.03  
% 2.29/1.03  ------ Propositional Solver
% 2.29/1.03  
% 2.29/1.03  prop_solver_calls:                      26
% 2.29/1.03  prop_fast_solver_calls:                 280
% 2.29/1.03  smt_solver_calls:                       0
% 2.29/1.03  smt_fast_solver_calls:                  0
% 2.29/1.03  prop_num_of_clauses:                    856
% 2.29/1.03  prop_preprocess_simplified:             2829
% 2.29/1.03  prop_fo_subsumed:                       0
% 2.29/1.03  prop_solver_time:                       0.
% 2.29/1.03  smt_solver_time:                        0.
% 2.29/1.03  smt_fast_solver_time:                   0.
% 2.29/1.03  prop_fast_solver_time:                  0.
% 2.29/1.03  prop_unsat_core_time:                   0.
% 2.29/1.03  
% 2.29/1.03  ------ QBF
% 2.29/1.03  
% 2.29/1.03  qbf_q_res:                              0
% 2.29/1.03  qbf_num_tautologies:                    0
% 2.29/1.03  qbf_prep_cycles:                        0
% 2.29/1.03  
% 2.29/1.03  ------ BMC1
% 2.29/1.03  
% 2.29/1.03  bmc1_current_bound:                     -1
% 2.29/1.03  bmc1_last_solved_bound:                 -1
% 2.29/1.03  bmc1_unsat_core_size:                   -1
% 2.29/1.03  bmc1_unsat_core_parents_size:           -1
% 2.29/1.03  bmc1_merge_next_fun:                    0
% 2.29/1.03  bmc1_unsat_core_clauses_time:           0.
% 2.29/1.03  
% 2.29/1.03  ------ Instantiation
% 2.29/1.03  
% 2.29/1.03  inst_num_of_clauses:                    439
% 2.29/1.03  inst_num_in_passive:                    223
% 2.29/1.03  inst_num_in_active:                     214
% 2.29/1.03  inst_num_in_unprocessed:                2
% 2.29/1.03  inst_num_of_loops:                      220
% 2.29/1.03  inst_num_of_learning_restarts:          0
% 2.29/1.03  inst_num_moves_active_passive:          1
% 2.29/1.03  inst_lit_activity:                      0
% 2.29/1.03  inst_lit_activity_moves:                0
% 2.29/1.03  inst_num_tautologies:                   0
% 2.29/1.03  inst_num_prop_implied:                  0
% 2.29/1.03  inst_num_existing_simplified:           0
% 2.29/1.03  inst_num_eq_res_simplified:             0
% 2.29/1.03  inst_num_child_elim:                    0
% 2.29/1.03  inst_num_of_dismatching_blockings:      266
% 2.29/1.03  inst_num_of_non_proper_insts:           441
% 2.29/1.03  inst_num_of_duplicates:                 0
% 2.29/1.03  inst_inst_num_from_inst_to_res:         0
% 2.29/1.03  inst_dismatching_checking_time:         0.
% 2.29/1.03  
% 2.29/1.03  ------ Resolution
% 2.29/1.03  
% 2.29/1.03  res_num_of_clauses:                     0
% 2.29/1.03  res_num_in_passive:                     0
% 2.29/1.03  res_num_in_active:                      0
% 2.29/1.03  res_num_of_loops:                       65
% 2.29/1.03  res_forward_subset_subsumed:            127
% 2.29/1.03  res_backward_subset_subsumed:           0
% 2.29/1.03  res_forward_subsumed:                   0
% 2.29/1.03  res_backward_subsumed:                  0
% 2.29/1.03  res_forward_subsumption_resolution:     0
% 2.29/1.03  res_backward_subsumption_resolution:    0
% 2.29/1.03  res_clause_to_clause_subsumption:       483
% 2.29/1.03  res_orphan_elimination:                 0
% 2.29/1.03  res_tautology_del:                      115
% 2.29/1.03  res_num_eq_res_simplified:              1
% 2.29/1.03  res_num_sel_changes:                    0
% 2.29/1.03  res_moves_from_active_to_pass:          0
% 2.29/1.03  
% 2.29/1.03  ------ Superposition
% 2.29/1.03  
% 2.29/1.03  sup_time_total:                         0.
% 2.29/1.03  sup_time_generating:                    0.
% 2.29/1.03  sup_time_sim_full:                      0.
% 2.29/1.03  sup_time_sim_immed:                     0.
% 2.29/1.03  
% 2.29/1.03  sup_num_of_clauses:                     70
% 2.29/1.03  sup_num_in_active:                      40
% 2.29/1.03  sup_num_in_passive:                     30
% 2.29/1.03  sup_num_of_loops:                       42
% 2.29/1.03  sup_fw_superposition:                   232
% 2.29/1.03  sup_bw_superposition:                   197
% 2.29/1.03  sup_immediate_simplified:               125
% 2.29/1.03  sup_given_eliminated:                   0
% 2.29/1.03  comparisons_done:                       0
% 2.29/1.03  comparisons_avoided:                    0
% 2.29/1.03  
% 2.29/1.03  ------ Simplifications
% 2.29/1.03  
% 2.29/1.03  
% 2.29/1.03  sim_fw_subset_subsumed:                 0
% 2.29/1.03  sim_bw_subset_subsumed:                 0
% 2.29/1.03  sim_fw_subsumed:                        12
% 2.29/1.03  sim_bw_subsumed:                        0
% 2.29/1.03  sim_fw_subsumption_res:                 0
% 2.29/1.03  sim_bw_subsumption_res:                 0
% 2.29/1.03  sim_tautology_del:                      0
% 2.29/1.03  sim_eq_tautology_del:                   28
% 2.29/1.03  sim_eq_res_simp:                        1
% 2.29/1.03  sim_fw_demodulated:                     15
% 2.29/1.03  sim_bw_demodulated:                     6
% 2.29/1.03  sim_light_normalised:                   100
% 2.29/1.03  sim_joinable_taut:                      0
% 2.29/1.03  sim_joinable_simp:                      0
% 2.29/1.03  sim_ac_normalised:                      0
% 2.29/1.03  sim_smt_subsumption:                    0
% 2.29/1.03  
%------------------------------------------------------------------------------
