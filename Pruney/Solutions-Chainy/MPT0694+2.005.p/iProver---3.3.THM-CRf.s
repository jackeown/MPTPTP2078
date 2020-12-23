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
% DateTime   : Thu Dec  3 11:51:56 EST 2020

% Result     : Theorem 35.44s
% Output     : CNFRefutation 35.44s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 311 expanded)
%              Number of clauses        :   92 ( 132 expanded)
%              Number of leaves         :   19 (  66 expanded)
%              Depth                    :   14
%              Number of atoms          :  318 ( 668 expanded)
%              Number of equality atoms :  151 ( 243 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f28,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f28])).

fof(f43,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f34,f33])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(X2,X1))) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f41,f46])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f30,f46])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)
          | ~ r1_tarski(X1,X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f31,f46])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f49,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f32,f33,f33])).

fof(f45,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) ),
    inference(cnf_transformation,[],[f29])).

fof(f51,plain,(
    ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1))) ),
    inference(definition_unfolding,[],[f45,f46,f46])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f44,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_13,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_241,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_513,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_241])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k1_enumset1(X1,X1,k10_relat_1(X0,X2))) = k10_relat_1(k7_relat_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_245,plain,
    ( ~ v1_relat_1(X0_40)
    | k1_setfam_1(k1_enumset1(X0_41,X0_41,k10_relat_1(X0_40,X1_41))) = k10_relat_1(k7_relat_1(X0_40,X0_41),X1_41) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_509,plain,
    ( k1_setfam_1(k1_enumset1(X0_41,X0_41,k10_relat_1(X0_40,X1_41))) = k10_relat_1(k7_relat_1(X0_40,X0_41),X1_41)
    | v1_relat_1(X0_40) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_245])).

cnf(c_960,plain,
    ( k1_setfam_1(k1_enumset1(X0_41,X0_41,k10_relat_1(sK2,X1_41))) = k10_relat_1(k7_relat_1(sK2,X0_41),X1_41) ),
    inference(superposition,[status(thm)],[c_513,c_509])).

cnf(c_0,plain,
    ( r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_253,plain,
    ( r1_tarski(k1_setfam_1(k1_enumset1(X0_41,X0_41,X1_41)),X0_41) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_502,plain,
    ( r1_tarski(k1_setfam_1(k1_enumset1(X0_41,X0_41,X1_41)),X0_41) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_253])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X2)
    | k9_relat_1(k7_relat_1(X2,X1),X0) = k9_relat_1(X2,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_248,plain,
    ( ~ r1_tarski(X0_41,X1_41)
    | ~ v1_relat_1(X0_40)
    | k9_relat_1(k7_relat_1(X0_40,X1_41),X0_41) = k9_relat_1(X0_40,X0_41) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_506,plain,
    ( k9_relat_1(k7_relat_1(X0_40,X0_41),X1_41) = k9_relat_1(X0_40,X1_41)
    | r1_tarski(X1_41,X0_41) != iProver_top
    | v1_relat_1(X0_40) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_248])).

cnf(c_1239,plain,
    ( k9_relat_1(k7_relat_1(X0_40,X0_41),k1_setfam_1(k1_enumset1(X0_41,X0_41,X1_41))) = k9_relat_1(X0_40,k1_setfam_1(k1_enumset1(X0_41,X0_41,X1_41)))
    | v1_relat_1(X0_40) != iProver_top ),
    inference(superposition,[status(thm)],[c_502,c_506])).

cnf(c_2955,plain,
    ( k9_relat_1(k7_relat_1(sK2,X0_41),k1_setfam_1(k1_enumset1(X0_41,X0_41,X1_41))) = k9_relat_1(sK2,k1_setfam_1(k1_enumset1(X0_41,X0_41,X1_41))) ),
    inference(superposition,[status(thm)],[c_513,c_1239])).

cnf(c_2961,plain,
    ( k9_relat_1(sK2,k1_setfam_1(k1_enumset1(X0_41,X0_41,k10_relat_1(sK2,X1_41)))) = k9_relat_1(k7_relat_1(sK2,X0_41),k10_relat_1(k7_relat_1(sK2,X0_41),X1_41)) ),
    inference(superposition,[status(thm)],[c_960,c_2955])).

cnf(c_2975,plain,
    ( k9_relat_1(k7_relat_1(sK2,X0_41),k10_relat_1(k7_relat_1(sK2,X0_41),X1_41)) = k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X0_41),X1_41)) ),
    inference(light_normalisation,[status(thm)],[c_2961,c_960])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_250,plain,
    ( ~ v1_relat_1(X0_40)
    | v1_relat_1(k7_relat_1(X0_40,X0_41)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_504,plain,
    ( v1_relat_1(X0_40) != iProver_top
    | v1_relat_1(k7_relat_1(X0_40,X0_41)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_250])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_249,plain,
    ( ~ v1_relat_1(X0_40)
    | k2_relat_1(k7_relat_1(X0_40,X0_41)) = k9_relat_1(X0_40,X0_41) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_505,plain,
    ( k2_relat_1(k7_relat_1(X0_40,X0_41)) = k9_relat_1(X0_40,X0_41)
    | v1_relat_1(X0_40) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_249])).

cnf(c_824,plain,
    ( k2_relat_1(k7_relat_1(k7_relat_1(X0_40,X0_41),X1_41)) = k9_relat_1(k7_relat_1(X0_40,X0_41),X1_41)
    | v1_relat_1(X0_40) != iProver_top ),
    inference(superposition,[status(thm)],[c_504,c_505])).

cnf(c_1338,plain,
    ( k2_relat_1(k7_relat_1(k7_relat_1(sK2,X0_41),X1_41)) = k9_relat_1(k7_relat_1(sK2,X0_41),X1_41) ),
    inference(superposition,[status(thm)],[c_513,c_824])).

cnf(c_6,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(X0,X1)),k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_247,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(X0_40,X0_41)),k2_relat_1(X0_40))
    | ~ v1_relat_1(X0_40) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_507,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(X0_40,X0_41)),k2_relat_1(X0_40)) = iProver_top
    | v1_relat_1(X0_40) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_247])).

cnf(c_1439,plain,
    ( r1_tarski(k9_relat_1(k7_relat_1(sK2,X0_41),X1_41),k2_relat_1(k7_relat_1(sK2,X0_41))) = iProver_top
    | v1_relat_1(k7_relat_1(sK2,X0_41)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1338,c_507])).

cnf(c_823,plain,
    ( k2_relat_1(k7_relat_1(sK2,X0_41)) = k9_relat_1(sK2,X0_41) ),
    inference(superposition,[status(thm)],[c_513,c_505])).

cnf(c_1440,plain,
    ( r1_tarski(k9_relat_1(k7_relat_1(sK2,X0_41),X1_41),k9_relat_1(sK2,X0_41)) = iProver_top
    | v1_relat_1(k7_relat_1(sK2,X0_41)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1439,c_823])).

cnf(c_3100,plain,
    ( r1_tarski(k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X0_41),X1_41)),k9_relat_1(sK2,X0_41)) = iProver_top
    | v1_relat_1(k7_relat_1(sK2,X0_41)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2975,c_1440])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_setfam_1(k1_enumset1(X2,X2,X1))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_252,plain,
    ( ~ r1_tarski(X0_41,X1_41)
    | ~ r1_tarski(X0_41,X2_41)
    | r1_tarski(X0_41,k1_setfam_1(k1_enumset1(X2_41,X2_41,X1_41))) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_503,plain,
    ( r1_tarski(X0_41,X1_41) != iProver_top
    | r1_tarski(X0_41,X2_41) != iProver_top
    | r1_tarski(X0_41,k1_setfam_1(k1_enumset1(X2_41,X2_41,X1_41))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_252])).

cnf(c_2,plain,
    ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_251,plain,
    ( k1_enumset1(X0_41,X0_41,X1_41) = k1_enumset1(X1_41,X1_41,X0_41) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_11,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_243,negated_conjecture,
    ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1))) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_511,plain,
    ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_243])).

cnf(c_629,plain,
    ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_251,c_511])).

cnf(c_1023,plain,
    ( r1_tarski(k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1)),k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_960,c_629])).

cnf(c_1234,plain,
    ( r1_tarski(k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1)),k9_relat_1(sK2,sK0)) != iProver_top
    | r1_tarski(k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1)),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_503,c_1023])).

cnf(c_105271,plain,
    ( r1_tarski(k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1)),sK1) != iProver_top
    | v1_relat_1(k7_relat_1(sK2,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3100,c_1234])).

cnf(c_262,plain,
    ( ~ r1_tarski(X0_41,X1_41)
    | r1_tarski(X2_41,X3_41)
    | X2_41 != X0_41
    | X3_41 != X1_41 ),
    theory(equality)).

cnf(c_2532,plain,
    ( r1_tarski(X0_41,X1_41)
    | ~ r1_tarski(k1_setfam_1(k1_enumset1(X2_41,X2_41,X3_41)),X2_41)
    | X1_41 != X2_41
    | X0_41 != k1_setfam_1(k1_enumset1(X2_41,X2_41,X3_41)) ),
    inference(instantiation,[status(thm)],[c_262])).

cnf(c_27747,plain,
    ( r1_tarski(k10_relat_1(k7_relat_1(sK2,sK0),sK1),X0_41)
    | ~ r1_tarski(k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1))),sK0)
    | X0_41 != sK0
    | k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1))) ),
    inference(instantiation,[status(thm)],[c_2532])).

cnf(c_27749,plain,
    ( r1_tarski(k10_relat_1(k7_relat_1(sK2,sK0),sK1),sK0)
    | ~ r1_tarski(k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1))),sK0)
    | k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_27747])).

cnf(c_659,plain,
    ( ~ r1_tarski(X0_41,X1_41)
    | r1_tarski(X2_41,sK1)
    | X2_41 != X0_41
    | sK1 != X1_41 ),
    inference(instantiation,[status(thm)],[c_262])).

cnf(c_790,plain,
    ( ~ r1_tarski(X0_41,sK1)
    | r1_tarski(X1_41,sK1)
    | X1_41 != X0_41
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_659])).

cnf(c_1044,plain,
    ( r1_tarski(X0_41,sK1)
    | ~ r1_tarski(k9_relat_1(X0_40,k10_relat_1(X0_40,sK1)),sK1)
    | X0_41 != k9_relat_1(X0_40,k10_relat_1(X0_40,sK1))
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_790])).

cnf(c_1964,plain,
    ( r1_tarski(k9_relat_1(X0_40,X0_41),sK1)
    | ~ r1_tarski(k9_relat_1(X1_40,k10_relat_1(X1_40,sK1)),sK1)
    | k9_relat_1(X0_40,X0_41) != k9_relat_1(X1_40,k10_relat_1(X1_40,sK1))
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1044])).

cnf(c_10712,plain,
    ( r1_tarski(k9_relat_1(X0_40,k10_relat_1(k7_relat_1(sK2,sK0),sK1)),sK1)
    | ~ r1_tarski(k9_relat_1(k7_relat_1(sK2,sK0),k10_relat_1(k7_relat_1(sK2,sK0),sK1)),sK1)
    | k9_relat_1(X0_40,k10_relat_1(k7_relat_1(sK2,sK0),sK1)) != k9_relat_1(k7_relat_1(sK2,sK0),k10_relat_1(k7_relat_1(sK2,sK0),sK1))
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1964])).

cnf(c_10714,plain,
    ( k9_relat_1(X0_40,k10_relat_1(k7_relat_1(sK2,sK0),sK1)) != k9_relat_1(k7_relat_1(sK2,sK0),k10_relat_1(k7_relat_1(sK2,sK0),sK1))
    | sK1 != sK1
    | r1_tarski(k9_relat_1(X0_40,k10_relat_1(k7_relat_1(sK2,sK0),sK1)),sK1) = iProver_top
    | r1_tarski(k9_relat_1(k7_relat_1(sK2,sK0),k10_relat_1(k7_relat_1(sK2,sK0),sK1)),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10712])).

cnf(c_10716,plain,
    ( k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1)) != k9_relat_1(k7_relat_1(sK2,sK0),k10_relat_1(k7_relat_1(sK2,sK0),sK1))
    | sK1 != sK1
    | r1_tarski(k9_relat_1(k7_relat_1(sK2,sK0),k10_relat_1(k7_relat_1(sK2,sK0),sK1)),sK1) != iProver_top
    | r1_tarski(k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1)),sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_10714])).

cnf(c_258,plain,
    ( X0_41 != X1_41
    | X2_41 != X1_41
    | X2_41 = X0_41 ),
    theory(equality)).

cnf(c_1008,plain,
    ( X0_41 != X1_41
    | X0_41 = k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))
    | k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1))) != X1_41 ),
    inference(instantiation,[status(thm)],[c_258])).

cnf(c_1860,plain,
    ( X0_41 != k10_relat_1(k7_relat_1(sK2,sK0),sK1)
    | X0_41 = k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))
    | k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1))) != k10_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    inference(instantiation,[status(thm)],[c_1008])).

cnf(c_3854,plain,
    ( k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k10_relat_1(k7_relat_1(sK2,sK0),sK1)
    | k10_relat_1(k7_relat_1(sK2,sK0),sK1) = k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))
    | k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1))) != k10_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    inference(instantiation,[status(thm)],[c_1860])).

cnf(c_1293,plain,
    ( X0_41 != X1_41
    | X0_41 = k9_relat_1(X0_40,k10_relat_1(k7_relat_1(sK2,sK0),sK1))
    | k9_relat_1(X0_40,k10_relat_1(k7_relat_1(sK2,sK0),sK1)) != X1_41 ),
    inference(instantiation,[status(thm)],[c_258])).

cnf(c_1622,plain,
    ( X0_41 != k9_relat_1(X0_40,k10_relat_1(k7_relat_1(sK2,sK0),sK1))
    | X0_41 = k9_relat_1(k7_relat_1(X0_40,X1_41),k10_relat_1(k7_relat_1(sK2,sK0),sK1))
    | k9_relat_1(k7_relat_1(X0_40,X1_41),k10_relat_1(k7_relat_1(sK2,sK0),sK1)) != k9_relat_1(X0_40,k10_relat_1(k7_relat_1(sK2,sK0),sK1)) ),
    inference(instantiation,[status(thm)],[c_1293])).

cnf(c_3589,plain,
    ( k9_relat_1(X0_40,k10_relat_1(k7_relat_1(sK2,sK0),sK1)) != k9_relat_1(X0_40,k10_relat_1(k7_relat_1(sK2,sK0),sK1))
    | k9_relat_1(X0_40,k10_relat_1(k7_relat_1(sK2,sK0),sK1)) = k9_relat_1(k7_relat_1(X0_40,X0_41),k10_relat_1(k7_relat_1(sK2,sK0),sK1))
    | k9_relat_1(k7_relat_1(X0_40,X0_41),k10_relat_1(k7_relat_1(sK2,sK0),sK1)) != k9_relat_1(X0_40,k10_relat_1(k7_relat_1(sK2,sK0),sK1)) ),
    inference(instantiation,[status(thm)],[c_1622])).

cnf(c_3590,plain,
    ( k9_relat_1(k7_relat_1(sK2,sK0),k10_relat_1(k7_relat_1(sK2,sK0),sK1)) != k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1))
    | k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1)) = k9_relat_1(k7_relat_1(sK2,sK0),k10_relat_1(k7_relat_1(sK2,sK0),sK1))
    | k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1)) != k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1)) ),
    inference(instantiation,[status(thm)],[c_3589])).

cnf(c_265,plain,
    ( X0_41 != X1_41
    | k9_relat_1(X0_40,X0_41) = k9_relat_1(X1_40,X1_41)
    | X0_40 != X1_40 ),
    theory(equality)).

cnf(c_1632,plain,
    ( X0_41 != k10_relat_1(k7_relat_1(sK2,sK0),sK1)
    | k9_relat_1(X0_40,X0_41) = k9_relat_1(X1_40,k10_relat_1(k7_relat_1(sK2,sK0),sK1))
    | X0_40 != X1_40 ),
    inference(instantiation,[status(thm)],[c_265])).

cnf(c_3485,plain,
    ( k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k10_relat_1(k7_relat_1(sK2,sK0),sK1)
    | k9_relat_1(X0_40,k10_relat_1(k7_relat_1(sK2,sK0),sK1)) = k9_relat_1(X1_40,k10_relat_1(k7_relat_1(sK2,sK0),sK1))
    | X0_40 != X1_40 ),
    inference(instantiation,[status(thm)],[c_1632])).

cnf(c_3486,plain,
    ( k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k10_relat_1(k7_relat_1(sK2,sK0),sK1)
    | k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1)) = k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1))
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_3485])).

cnf(c_256,plain,
    ( X0_41 = X0_41 ),
    theory(equality)).

cnf(c_3473,plain,
    ( k10_relat_1(k7_relat_1(sK2,sK0),sK1) = k10_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    inference(instantiation,[status(thm)],[c_256])).

cnf(c_1614,plain,
    ( ~ r1_tarski(k10_relat_1(k7_relat_1(sK2,sK0),sK1),X0_41)
    | ~ v1_relat_1(X0_40)
    | k9_relat_1(k7_relat_1(X0_40,X0_41),k10_relat_1(k7_relat_1(sK2,sK0),sK1)) = k9_relat_1(X0_40,k10_relat_1(k7_relat_1(sK2,sK0),sK1)) ),
    inference(instantiation,[status(thm)],[c_248])).

cnf(c_1616,plain,
    ( ~ r1_tarski(k10_relat_1(k7_relat_1(sK2,sK0),sK1),sK0)
    | ~ v1_relat_1(sK2)
    | k9_relat_1(k7_relat_1(sK2,sK0),k10_relat_1(k7_relat_1(sK2,sK0),sK1)) = k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1)) ),
    inference(instantiation,[status(thm)],[c_1614])).

cnf(c_10,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_244,plain,
    ( r1_tarski(k9_relat_1(X0_40,k10_relat_1(X0_40,X0_41)),X0_41)
    | ~ v1_funct_1(X0_40)
    | ~ v1_relat_1(X0_40) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_770,plain,
    ( r1_tarski(k9_relat_1(X0_40,k10_relat_1(X0_40,sK1)),sK1)
    | ~ v1_funct_1(X0_40)
    | ~ v1_relat_1(X0_40) ),
    inference(instantiation,[status(thm)],[c_244])).

cnf(c_1313,plain,
    ( r1_tarski(k9_relat_1(k7_relat_1(sK2,sK0),k10_relat_1(k7_relat_1(sK2,sK0),sK1)),sK1)
    | ~ v1_funct_1(k7_relat_1(sK2,sK0))
    | ~ v1_relat_1(k7_relat_1(sK2,sK0)) ),
    inference(instantiation,[status(thm)],[c_770])).

cnf(c_1314,plain,
    ( r1_tarski(k9_relat_1(k7_relat_1(sK2,sK0),k10_relat_1(k7_relat_1(sK2,sK0),sK1)),sK1) = iProver_top
    | v1_funct_1(k7_relat_1(sK2,sK0)) != iProver_top
    | v1_relat_1(k7_relat_1(sK2,sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1313])).

cnf(c_1141,plain,
    ( r1_tarski(k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1))),sK0) ),
    inference(instantiation,[status(thm)],[c_253])).

cnf(c_902,plain,
    ( ~ v1_relat_1(sK2)
    | k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1))) = k10_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    inference(instantiation,[status(thm)],[c_245])).

cnf(c_595,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_256])).

cnf(c_7,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k7_relat_1(X0,X1))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_246,plain,
    ( ~ v1_funct_1(X0_40)
    | v1_funct_1(k7_relat_1(X0_40,X0_41))
    | ~ v1_relat_1(X0_40) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_299,plain,
    ( v1_funct_1(X0_40) != iProver_top
    | v1_funct_1(k7_relat_1(X0_40,X0_41)) = iProver_top
    | v1_relat_1(X0_40) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_246])).

cnf(c_301,plain,
    ( v1_funct_1(k7_relat_1(sK2,sK0)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_299])).

cnf(c_287,plain,
    ( v1_relat_1(X0_40) != iProver_top
    | v1_relat_1(k7_relat_1(X0_40,X0_41)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_250])).

cnf(c_289,plain,
    ( v1_relat_1(k7_relat_1(sK2,sK0)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_287])).

cnf(c_278,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_256])).

cnf(c_255,plain,
    ( X0_40 = X0_40 ),
    theory(equality)).

cnf(c_277,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_255])).

cnf(c_12,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_15,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_14,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_105271,c_27749,c_10716,c_3854,c_3590,c_3486,c_3473,c_1616,c_1314,c_1141,c_902,c_595,c_301,c_289,c_278,c_277,c_15,c_14,c_13])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:51:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 35.44/4.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 35.44/4.98  
% 35.44/4.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 35.44/4.98  
% 35.44/4.98  ------  iProver source info
% 35.44/4.98  
% 35.44/4.98  git: date: 2020-06-30 10:37:57 +0100
% 35.44/4.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 35.44/4.98  git: non_committed_changes: false
% 35.44/4.98  git: last_make_outside_of_git: false
% 35.44/4.98  
% 35.44/4.98  ------ 
% 35.44/4.98  
% 35.44/4.98  ------ Input Options
% 35.44/4.98  
% 35.44/4.98  --out_options                           all
% 35.44/4.98  --tptp_safe_out                         true
% 35.44/4.98  --problem_path                          ""
% 35.44/4.98  --include_path                          ""
% 35.44/4.98  --clausifier                            res/vclausify_rel
% 35.44/4.98  --clausifier_options                    ""
% 35.44/4.98  --stdin                                 false
% 35.44/4.98  --stats_out                             all
% 35.44/4.98  
% 35.44/4.98  ------ General Options
% 35.44/4.98  
% 35.44/4.98  --fof                                   false
% 35.44/4.98  --time_out_real                         305.
% 35.44/4.98  --time_out_virtual                      -1.
% 35.44/4.98  --symbol_type_check                     false
% 35.44/4.98  --clausify_out                          false
% 35.44/4.98  --sig_cnt_out                           false
% 35.44/4.98  --trig_cnt_out                          false
% 35.44/4.98  --trig_cnt_out_tolerance                1.
% 35.44/4.98  --trig_cnt_out_sk_spl                   false
% 35.44/4.98  --abstr_cl_out                          false
% 35.44/4.98  
% 35.44/4.98  ------ Global Options
% 35.44/4.98  
% 35.44/4.98  --schedule                              default
% 35.44/4.98  --add_important_lit                     false
% 35.44/4.98  --prop_solver_per_cl                    1000
% 35.44/4.98  --min_unsat_core                        false
% 35.44/4.98  --soft_assumptions                      false
% 35.44/4.98  --soft_lemma_size                       3
% 35.44/4.98  --prop_impl_unit_size                   0
% 35.44/4.98  --prop_impl_unit                        []
% 35.44/4.98  --share_sel_clauses                     true
% 35.44/4.98  --reset_solvers                         false
% 35.44/4.98  --bc_imp_inh                            [conj_cone]
% 35.44/4.98  --conj_cone_tolerance                   3.
% 35.44/4.98  --extra_neg_conj                        none
% 35.44/4.98  --large_theory_mode                     true
% 35.44/4.98  --prolific_symb_bound                   200
% 35.44/4.98  --lt_threshold                          2000
% 35.44/4.98  --clause_weak_htbl                      true
% 35.44/4.98  --gc_record_bc_elim                     false
% 35.44/4.98  
% 35.44/4.98  ------ Preprocessing Options
% 35.44/4.98  
% 35.44/4.98  --preprocessing_flag                    true
% 35.44/4.98  --time_out_prep_mult                    0.1
% 35.44/4.98  --splitting_mode                        input
% 35.44/4.98  --splitting_grd                         true
% 35.44/4.98  --splitting_cvd                         false
% 35.44/4.98  --splitting_cvd_svl                     false
% 35.44/4.98  --splitting_nvd                         32
% 35.44/4.98  --sub_typing                            true
% 35.44/4.98  --prep_gs_sim                           true
% 35.44/4.98  --prep_unflatten                        true
% 35.44/4.98  --prep_res_sim                          true
% 35.44/4.98  --prep_upred                            true
% 35.44/4.98  --prep_sem_filter                       exhaustive
% 35.44/4.98  --prep_sem_filter_out                   false
% 35.44/4.98  --pred_elim                             true
% 35.44/4.98  --res_sim_input                         true
% 35.44/4.98  --eq_ax_congr_red                       true
% 35.44/4.98  --pure_diseq_elim                       true
% 35.44/4.98  --brand_transform                       false
% 35.44/4.98  --non_eq_to_eq                          false
% 35.44/4.98  --prep_def_merge                        true
% 35.44/4.98  --prep_def_merge_prop_impl              false
% 35.44/4.98  --prep_def_merge_mbd                    true
% 35.44/4.98  --prep_def_merge_tr_red                 false
% 35.44/4.98  --prep_def_merge_tr_cl                  false
% 35.44/4.98  --smt_preprocessing                     true
% 35.44/4.98  --smt_ac_axioms                         fast
% 35.44/4.98  --preprocessed_out                      false
% 35.44/4.98  --preprocessed_stats                    false
% 35.44/4.98  
% 35.44/4.98  ------ Abstraction refinement Options
% 35.44/4.98  
% 35.44/4.98  --abstr_ref                             []
% 35.44/4.98  --abstr_ref_prep                        false
% 35.44/4.98  --abstr_ref_until_sat                   false
% 35.44/4.98  --abstr_ref_sig_restrict                funpre
% 35.44/4.98  --abstr_ref_af_restrict_to_split_sk     false
% 35.44/4.98  --abstr_ref_under                       []
% 35.44/4.98  
% 35.44/4.98  ------ SAT Options
% 35.44/4.98  
% 35.44/4.98  --sat_mode                              false
% 35.44/4.98  --sat_fm_restart_options                ""
% 35.44/4.98  --sat_gr_def                            false
% 35.44/4.98  --sat_epr_types                         true
% 35.44/4.98  --sat_non_cyclic_types                  false
% 35.44/4.98  --sat_finite_models                     false
% 35.44/4.98  --sat_fm_lemmas                         false
% 35.44/4.98  --sat_fm_prep                           false
% 35.44/4.98  --sat_fm_uc_incr                        true
% 35.44/4.98  --sat_out_model                         small
% 35.44/4.98  --sat_out_clauses                       false
% 35.44/4.98  
% 35.44/4.98  ------ QBF Options
% 35.44/4.98  
% 35.44/4.98  --qbf_mode                              false
% 35.44/4.98  --qbf_elim_univ                         false
% 35.44/4.98  --qbf_dom_inst                          none
% 35.44/4.98  --qbf_dom_pre_inst                      false
% 35.44/4.98  --qbf_sk_in                             false
% 35.44/4.98  --qbf_pred_elim                         true
% 35.44/4.98  --qbf_split                             512
% 35.44/4.98  
% 35.44/4.98  ------ BMC1 Options
% 35.44/4.98  
% 35.44/4.98  --bmc1_incremental                      false
% 35.44/4.98  --bmc1_axioms                           reachable_all
% 35.44/4.98  --bmc1_min_bound                        0
% 35.44/4.98  --bmc1_max_bound                        -1
% 35.44/4.98  --bmc1_max_bound_default                -1
% 35.44/4.98  --bmc1_symbol_reachability              true
% 35.44/4.98  --bmc1_property_lemmas                  false
% 35.44/4.98  --bmc1_k_induction                      false
% 35.44/4.98  --bmc1_non_equiv_states                 false
% 35.44/4.98  --bmc1_deadlock                         false
% 35.44/4.98  --bmc1_ucm                              false
% 35.44/4.98  --bmc1_add_unsat_core                   none
% 35.44/4.98  --bmc1_unsat_core_children              false
% 35.44/4.98  --bmc1_unsat_core_extrapolate_axioms    false
% 35.44/4.98  --bmc1_out_stat                         full
% 35.44/4.98  --bmc1_ground_init                      false
% 35.44/4.98  --bmc1_pre_inst_next_state              false
% 35.44/4.98  --bmc1_pre_inst_state                   false
% 35.44/4.98  --bmc1_pre_inst_reach_state             false
% 35.44/4.98  --bmc1_out_unsat_core                   false
% 35.44/4.98  --bmc1_aig_witness_out                  false
% 35.44/4.98  --bmc1_verbose                          false
% 35.44/4.98  --bmc1_dump_clauses_tptp                false
% 35.44/4.98  --bmc1_dump_unsat_core_tptp             false
% 35.44/4.98  --bmc1_dump_file                        -
% 35.44/4.98  --bmc1_ucm_expand_uc_limit              128
% 35.44/4.98  --bmc1_ucm_n_expand_iterations          6
% 35.44/4.98  --bmc1_ucm_extend_mode                  1
% 35.44/4.98  --bmc1_ucm_init_mode                    2
% 35.44/4.98  --bmc1_ucm_cone_mode                    none
% 35.44/4.98  --bmc1_ucm_reduced_relation_type        0
% 35.44/4.98  --bmc1_ucm_relax_model                  4
% 35.44/4.98  --bmc1_ucm_full_tr_after_sat            true
% 35.44/4.98  --bmc1_ucm_expand_neg_assumptions       false
% 35.44/4.98  --bmc1_ucm_layered_model                none
% 35.44/4.98  --bmc1_ucm_max_lemma_size               10
% 35.44/4.98  
% 35.44/4.98  ------ AIG Options
% 35.44/4.98  
% 35.44/4.98  --aig_mode                              false
% 35.44/4.98  
% 35.44/4.98  ------ Instantiation Options
% 35.44/4.98  
% 35.44/4.98  --instantiation_flag                    true
% 35.44/4.98  --inst_sos_flag                         true
% 35.44/4.98  --inst_sos_phase                        true
% 35.44/4.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 35.44/4.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 35.44/4.98  --inst_lit_sel_side                     num_symb
% 35.44/4.98  --inst_solver_per_active                1400
% 35.44/4.98  --inst_solver_calls_frac                1.
% 35.44/4.98  --inst_passive_queue_type               priority_queues
% 35.44/4.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 35.44/4.98  --inst_passive_queues_freq              [25;2]
% 35.44/4.98  --inst_dismatching                      true
% 35.44/4.98  --inst_eager_unprocessed_to_passive     true
% 35.44/4.98  --inst_prop_sim_given                   true
% 35.44/4.98  --inst_prop_sim_new                     false
% 35.44/4.98  --inst_subs_new                         false
% 35.44/4.98  --inst_eq_res_simp                      false
% 35.44/4.98  --inst_subs_given                       false
% 35.44/4.98  --inst_orphan_elimination               true
% 35.44/4.98  --inst_learning_loop_flag               true
% 35.44/4.98  --inst_learning_start                   3000
% 35.44/4.98  --inst_learning_factor                  2
% 35.44/4.98  --inst_start_prop_sim_after_learn       3
% 35.44/4.98  --inst_sel_renew                        solver
% 35.44/4.98  --inst_lit_activity_flag                true
% 35.44/4.98  --inst_restr_to_given                   false
% 35.44/4.98  --inst_activity_threshold               500
% 35.44/4.98  --inst_out_proof                        true
% 35.44/4.98  
% 35.44/4.98  ------ Resolution Options
% 35.44/4.98  
% 35.44/4.98  --resolution_flag                       true
% 35.44/4.98  --res_lit_sel                           adaptive
% 35.44/4.98  --res_lit_sel_side                      none
% 35.44/4.98  --res_ordering                          kbo
% 35.44/4.98  --res_to_prop_solver                    active
% 35.44/4.98  --res_prop_simpl_new                    false
% 35.44/4.98  --res_prop_simpl_given                  true
% 35.44/4.98  --res_passive_queue_type                priority_queues
% 35.44/4.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 35.44/4.98  --res_passive_queues_freq               [15;5]
% 35.44/4.98  --res_forward_subs                      full
% 35.44/4.98  --res_backward_subs                     full
% 35.44/4.98  --res_forward_subs_resolution           true
% 35.44/4.98  --res_backward_subs_resolution          true
% 35.44/4.98  --res_orphan_elimination                true
% 35.44/4.98  --res_time_limit                        2.
% 35.44/4.98  --res_out_proof                         true
% 35.44/4.98  
% 35.44/4.98  ------ Superposition Options
% 35.44/4.98  
% 35.44/4.98  --superposition_flag                    true
% 35.44/4.98  --sup_passive_queue_type                priority_queues
% 35.44/4.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 35.44/4.98  --sup_passive_queues_freq               [8;1;4]
% 35.44/4.98  --demod_completeness_check              fast
% 35.44/4.98  --demod_use_ground                      true
% 35.44/4.98  --sup_to_prop_solver                    passive
% 35.44/4.98  --sup_prop_simpl_new                    true
% 35.44/4.98  --sup_prop_simpl_given                  true
% 35.44/4.98  --sup_fun_splitting                     true
% 35.44/4.98  --sup_smt_interval                      50000
% 35.44/4.98  
% 35.44/4.98  ------ Superposition Simplification Setup
% 35.44/4.98  
% 35.44/4.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 35.44/4.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 35.44/4.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 35.44/4.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 35.44/4.98  --sup_full_triv                         [TrivRules;PropSubs]
% 35.44/4.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 35.44/4.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 35.44/4.98  --sup_immed_triv                        [TrivRules]
% 35.44/4.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 35.44/4.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.44/4.98  --sup_immed_bw_main                     []
% 35.44/4.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 35.44/4.98  --sup_input_triv                        [Unflattening;TrivRules]
% 35.44/4.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.44/4.98  --sup_input_bw                          []
% 35.44/4.98  
% 35.44/4.98  ------ Combination Options
% 35.44/4.98  
% 35.44/4.98  --comb_res_mult                         3
% 35.44/4.98  --comb_sup_mult                         2
% 35.44/4.98  --comb_inst_mult                        10
% 35.44/4.98  
% 35.44/4.98  ------ Debug Options
% 35.44/4.98  
% 35.44/4.98  --dbg_backtrace                         false
% 35.44/4.98  --dbg_dump_prop_clauses                 false
% 35.44/4.98  --dbg_dump_prop_clauses_file            -
% 35.44/4.98  --dbg_out_stat                          false
% 35.44/4.98  ------ Parsing...
% 35.44/4.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 35.44/4.98  
% 35.44/4.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 35.44/4.98  
% 35.44/4.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 35.44/4.98  
% 35.44/4.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.44/4.98  ------ Proving...
% 35.44/4.98  ------ Problem Properties 
% 35.44/4.98  
% 35.44/4.98  
% 35.44/4.98  clauses                                 13
% 35.44/4.98  conjectures                             3
% 35.44/4.98  EPR                                     2
% 35.44/4.98  Horn                                    13
% 35.44/4.98  unary                                   5
% 35.44/4.98  binary                                  4
% 35.44/4.98  lits                                    25
% 35.44/4.98  lits eq                                 4
% 35.44/4.98  fd_pure                                 0
% 35.44/4.98  fd_pseudo                               0
% 35.44/4.98  fd_cond                                 0
% 35.44/4.98  fd_pseudo_cond                          0
% 35.44/4.98  AC symbols                              0
% 35.44/4.98  
% 35.44/4.98  ------ Schedule dynamic 5 is on 
% 35.44/4.98  
% 35.44/4.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 35.44/4.98  
% 35.44/4.98  
% 35.44/4.98  ------ 
% 35.44/4.98  Current options:
% 35.44/4.98  ------ 
% 35.44/4.98  
% 35.44/4.98  ------ Input Options
% 35.44/4.98  
% 35.44/4.98  --out_options                           all
% 35.44/4.98  --tptp_safe_out                         true
% 35.44/4.98  --problem_path                          ""
% 35.44/4.98  --include_path                          ""
% 35.44/4.98  --clausifier                            res/vclausify_rel
% 35.44/4.98  --clausifier_options                    ""
% 35.44/4.98  --stdin                                 false
% 35.44/4.98  --stats_out                             all
% 35.44/4.98  
% 35.44/4.98  ------ General Options
% 35.44/4.98  
% 35.44/4.98  --fof                                   false
% 35.44/4.98  --time_out_real                         305.
% 35.44/4.98  --time_out_virtual                      -1.
% 35.44/4.98  --symbol_type_check                     false
% 35.44/4.98  --clausify_out                          false
% 35.44/4.98  --sig_cnt_out                           false
% 35.44/4.98  --trig_cnt_out                          false
% 35.44/4.98  --trig_cnt_out_tolerance                1.
% 35.44/4.98  --trig_cnt_out_sk_spl                   false
% 35.44/4.98  --abstr_cl_out                          false
% 35.44/4.98  
% 35.44/4.98  ------ Global Options
% 35.44/4.98  
% 35.44/4.98  --schedule                              default
% 35.44/4.98  --add_important_lit                     false
% 35.44/4.98  --prop_solver_per_cl                    1000
% 35.44/4.98  --min_unsat_core                        false
% 35.44/4.98  --soft_assumptions                      false
% 35.44/4.98  --soft_lemma_size                       3
% 35.44/4.98  --prop_impl_unit_size                   0
% 35.44/4.98  --prop_impl_unit                        []
% 35.44/4.98  --share_sel_clauses                     true
% 35.44/4.98  --reset_solvers                         false
% 35.44/4.98  --bc_imp_inh                            [conj_cone]
% 35.44/4.98  --conj_cone_tolerance                   3.
% 35.44/4.98  --extra_neg_conj                        none
% 35.44/4.98  --large_theory_mode                     true
% 35.44/4.98  --prolific_symb_bound                   200
% 35.44/4.98  --lt_threshold                          2000
% 35.44/4.98  --clause_weak_htbl                      true
% 35.44/4.98  --gc_record_bc_elim                     false
% 35.44/4.98  
% 35.44/4.98  ------ Preprocessing Options
% 35.44/4.98  
% 35.44/4.98  --preprocessing_flag                    true
% 35.44/4.98  --time_out_prep_mult                    0.1
% 35.44/4.98  --splitting_mode                        input
% 35.44/4.98  --splitting_grd                         true
% 35.44/4.98  --splitting_cvd                         false
% 35.44/4.98  --splitting_cvd_svl                     false
% 35.44/4.98  --splitting_nvd                         32
% 35.44/4.98  --sub_typing                            true
% 35.44/4.98  --prep_gs_sim                           true
% 35.44/4.98  --prep_unflatten                        true
% 35.44/4.98  --prep_res_sim                          true
% 35.44/4.98  --prep_upred                            true
% 35.44/4.98  --prep_sem_filter                       exhaustive
% 35.44/4.98  --prep_sem_filter_out                   false
% 35.44/4.98  --pred_elim                             true
% 35.44/4.98  --res_sim_input                         true
% 35.44/4.98  --eq_ax_congr_red                       true
% 35.44/4.98  --pure_diseq_elim                       true
% 35.44/4.98  --brand_transform                       false
% 35.44/4.98  --non_eq_to_eq                          false
% 35.44/4.98  --prep_def_merge                        true
% 35.44/4.98  --prep_def_merge_prop_impl              false
% 35.44/4.98  --prep_def_merge_mbd                    true
% 35.44/4.98  --prep_def_merge_tr_red                 false
% 35.44/4.98  --prep_def_merge_tr_cl                  false
% 35.44/4.98  --smt_preprocessing                     true
% 35.44/4.98  --smt_ac_axioms                         fast
% 35.44/4.98  --preprocessed_out                      false
% 35.44/4.98  --preprocessed_stats                    false
% 35.44/4.98  
% 35.44/4.98  ------ Abstraction refinement Options
% 35.44/4.98  
% 35.44/4.98  --abstr_ref                             []
% 35.44/4.98  --abstr_ref_prep                        false
% 35.44/4.98  --abstr_ref_until_sat                   false
% 35.44/4.98  --abstr_ref_sig_restrict                funpre
% 35.44/4.98  --abstr_ref_af_restrict_to_split_sk     false
% 35.44/4.98  --abstr_ref_under                       []
% 35.44/4.98  
% 35.44/4.98  ------ SAT Options
% 35.44/4.98  
% 35.44/4.98  --sat_mode                              false
% 35.44/4.98  --sat_fm_restart_options                ""
% 35.44/4.98  --sat_gr_def                            false
% 35.44/4.98  --sat_epr_types                         true
% 35.44/4.98  --sat_non_cyclic_types                  false
% 35.44/4.98  --sat_finite_models                     false
% 35.44/4.98  --sat_fm_lemmas                         false
% 35.44/4.98  --sat_fm_prep                           false
% 35.44/4.98  --sat_fm_uc_incr                        true
% 35.44/4.98  --sat_out_model                         small
% 35.44/4.98  --sat_out_clauses                       false
% 35.44/4.98  
% 35.44/4.98  ------ QBF Options
% 35.44/4.98  
% 35.44/4.98  --qbf_mode                              false
% 35.44/4.98  --qbf_elim_univ                         false
% 35.44/4.98  --qbf_dom_inst                          none
% 35.44/4.98  --qbf_dom_pre_inst                      false
% 35.44/4.98  --qbf_sk_in                             false
% 35.44/4.98  --qbf_pred_elim                         true
% 35.44/4.98  --qbf_split                             512
% 35.44/4.98  
% 35.44/4.98  ------ BMC1 Options
% 35.44/4.98  
% 35.44/4.98  --bmc1_incremental                      false
% 35.44/4.98  --bmc1_axioms                           reachable_all
% 35.44/4.98  --bmc1_min_bound                        0
% 35.44/4.98  --bmc1_max_bound                        -1
% 35.44/4.98  --bmc1_max_bound_default                -1
% 35.44/4.98  --bmc1_symbol_reachability              true
% 35.44/4.98  --bmc1_property_lemmas                  false
% 35.44/4.98  --bmc1_k_induction                      false
% 35.44/4.98  --bmc1_non_equiv_states                 false
% 35.44/4.98  --bmc1_deadlock                         false
% 35.44/4.98  --bmc1_ucm                              false
% 35.44/4.98  --bmc1_add_unsat_core                   none
% 35.44/4.98  --bmc1_unsat_core_children              false
% 35.44/4.98  --bmc1_unsat_core_extrapolate_axioms    false
% 35.44/4.98  --bmc1_out_stat                         full
% 35.44/4.98  --bmc1_ground_init                      false
% 35.44/4.98  --bmc1_pre_inst_next_state              false
% 35.44/4.98  --bmc1_pre_inst_state                   false
% 35.44/4.98  --bmc1_pre_inst_reach_state             false
% 35.44/4.98  --bmc1_out_unsat_core                   false
% 35.44/4.98  --bmc1_aig_witness_out                  false
% 35.44/4.98  --bmc1_verbose                          false
% 35.44/4.98  --bmc1_dump_clauses_tptp                false
% 35.44/4.98  --bmc1_dump_unsat_core_tptp             false
% 35.44/4.98  --bmc1_dump_file                        -
% 35.44/4.98  --bmc1_ucm_expand_uc_limit              128
% 35.44/4.98  --bmc1_ucm_n_expand_iterations          6
% 35.44/4.98  --bmc1_ucm_extend_mode                  1
% 35.44/4.98  --bmc1_ucm_init_mode                    2
% 35.44/4.98  --bmc1_ucm_cone_mode                    none
% 35.44/4.98  --bmc1_ucm_reduced_relation_type        0
% 35.44/4.98  --bmc1_ucm_relax_model                  4
% 35.44/4.98  --bmc1_ucm_full_tr_after_sat            true
% 35.44/4.98  --bmc1_ucm_expand_neg_assumptions       false
% 35.44/4.98  --bmc1_ucm_layered_model                none
% 35.44/4.98  --bmc1_ucm_max_lemma_size               10
% 35.44/4.98  
% 35.44/4.98  ------ AIG Options
% 35.44/4.98  
% 35.44/4.98  --aig_mode                              false
% 35.44/4.98  
% 35.44/4.98  ------ Instantiation Options
% 35.44/4.98  
% 35.44/4.98  --instantiation_flag                    true
% 35.44/4.98  --inst_sos_flag                         true
% 35.44/4.98  --inst_sos_phase                        true
% 35.44/4.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 35.44/4.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 35.44/4.98  --inst_lit_sel_side                     none
% 35.44/4.98  --inst_solver_per_active                1400
% 35.44/4.98  --inst_solver_calls_frac                1.
% 35.44/4.98  --inst_passive_queue_type               priority_queues
% 35.44/4.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 35.44/4.98  --inst_passive_queues_freq              [25;2]
% 35.44/4.98  --inst_dismatching                      true
% 35.44/4.98  --inst_eager_unprocessed_to_passive     true
% 35.44/4.98  --inst_prop_sim_given                   true
% 35.44/4.98  --inst_prop_sim_new                     false
% 35.44/4.98  --inst_subs_new                         false
% 35.44/4.98  --inst_eq_res_simp                      false
% 35.44/4.98  --inst_subs_given                       false
% 35.44/4.98  --inst_orphan_elimination               true
% 35.44/4.98  --inst_learning_loop_flag               true
% 35.44/4.98  --inst_learning_start                   3000
% 35.44/4.98  --inst_learning_factor                  2
% 35.44/4.98  --inst_start_prop_sim_after_learn       3
% 35.44/4.98  --inst_sel_renew                        solver
% 35.44/4.98  --inst_lit_activity_flag                true
% 35.44/4.98  --inst_restr_to_given                   false
% 35.44/4.98  --inst_activity_threshold               500
% 35.44/4.98  --inst_out_proof                        true
% 35.44/4.98  
% 35.44/4.98  ------ Resolution Options
% 35.44/4.98  
% 35.44/4.98  --resolution_flag                       false
% 35.44/4.98  --res_lit_sel                           adaptive
% 35.44/4.98  --res_lit_sel_side                      none
% 35.44/4.98  --res_ordering                          kbo
% 35.44/4.98  --res_to_prop_solver                    active
% 35.44/4.98  --res_prop_simpl_new                    false
% 35.44/4.98  --res_prop_simpl_given                  true
% 35.44/4.98  --res_passive_queue_type                priority_queues
% 35.44/4.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 35.44/4.98  --res_passive_queues_freq               [15;5]
% 35.44/4.98  --res_forward_subs                      full
% 35.44/4.98  --res_backward_subs                     full
% 35.44/4.98  --res_forward_subs_resolution           true
% 35.44/4.98  --res_backward_subs_resolution          true
% 35.44/4.98  --res_orphan_elimination                true
% 35.44/4.98  --res_time_limit                        2.
% 35.44/4.98  --res_out_proof                         true
% 35.44/4.98  
% 35.44/4.98  ------ Superposition Options
% 35.44/4.98  
% 35.44/4.98  --superposition_flag                    true
% 35.44/4.98  --sup_passive_queue_type                priority_queues
% 35.44/4.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 35.44/4.98  --sup_passive_queues_freq               [8;1;4]
% 35.44/4.98  --demod_completeness_check              fast
% 35.44/4.98  --demod_use_ground                      true
% 35.44/4.98  --sup_to_prop_solver                    passive
% 35.44/4.98  --sup_prop_simpl_new                    true
% 35.44/4.98  --sup_prop_simpl_given                  true
% 35.44/4.98  --sup_fun_splitting                     true
% 35.44/4.98  --sup_smt_interval                      50000
% 35.44/4.98  
% 35.44/4.98  ------ Superposition Simplification Setup
% 35.44/4.98  
% 35.44/4.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 35.44/4.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 35.44/4.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 35.44/4.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 35.44/4.98  --sup_full_triv                         [TrivRules;PropSubs]
% 35.44/4.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 35.44/4.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 35.44/4.98  --sup_immed_triv                        [TrivRules]
% 35.44/4.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 35.44/4.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.44/4.98  --sup_immed_bw_main                     []
% 35.44/4.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 35.44/4.98  --sup_input_triv                        [Unflattening;TrivRules]
% 35.44/4.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.44/4.98  --sup_input_bw                          []
% 35.44/4.98  
% 35.44/4.98  ------ Combination Options
% 35.44/4.98  
% 35.44/4.98  --comb_res_mult                         3
% 35.44/4.98  --comb_sup_mult                         2
% 35.44/4.98  --comb_inst_mult                        10
% 35.44/4.98  
% 35.44/4.98  ------ Debug Options
% 35.44/4.98  
% 35.44/4.98  --dbg_backtrace                         false
% 35.44/4.98  --dbg_dump_prop_clauses                 false
% 35.44/4.98  --dbg_dump_prop_clauses_file            -
% 35.44/4.98  --dbg_out_stat                          false
% 35.44/4.98  
% 35.44/4.98  
% 35.44/4.98  
% 35.44/4.98  
% 35.44/4.98  ------ Proving...
% 35.44/4.98  
% 35.44/4.98  
% 35.44/4.98  % SZS status Theorem for theBenchmark.p
% 35.44/4.98  
% 35.44/4.98  % SZS output start CNFRefutation for theBenchmark.p
% 35.44/4.98  
% 35.44/4.98  fof(f13,conjecture,(
% 35.44/4.98    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)))),
% 35.44/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.44/4.98  
% 35.44/4.98  fof(f14,negated_conjecture,(
% 35.44/4.98    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)))),
% 35.44/4.98    inference(negated_conjecture,[],[f13])).
% 35.44/4.98  
% 35.44/4.98  fof(f26,plain,(
% 35.44/4.98    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 35.44/4.98    inference(ennf_transformation,[],[f14])).
% 35.44/4.98  
% 35.44/4.98  fof(f27,plain,(
% 35.44/4.98    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 35.44/4.98    inference(flattening,[],[f26])).
% 35.44/4.98  
% 35.44/4.98  fof(f28,plain,(
% 35.44/4.98    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))),k3_xboole_0(k9_relat_1(X2,X0),X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 35.44/4.98    introduced(choice_axiom,[])).
% 35.44/4.98  
% 35.44/4.98  fof(f29,plain,(
% 35.44/4.98    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 35.44/4.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f28])).
% 35.44/4.98  
% 35.44/4.98  fof(f43,plain,(
% 35.44/4.98    v1_relat_1(sK2)),
% 35.44/4.98    inference(cnf_transformation,[],[f29])).
% 35.44/4.98  
% 35.44/4.98  fof(f11,axiom,(
% 35.44/4.98    ! [X0,X1,X2] : (v1_relat_1(X2) => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1))),
% 35.44/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.44/4.98  
% 35.44/4.98  fof(f23,plain,(
% 35.44/4.98    ! [X0,X1,X2] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 35.44/4.98    inference(ennf_transformation,[],[f11])).
% 35.44/4.98  
% 35.44/4.98  fof(f41,plain,(
% 35.44/4.98    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 35.44/4.98    inference(cnf_transformation,[],[f23])).
% 35.44/4.98  
% 35.44/4.98  fof(f5,axiom,(
% 35.44/4.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 35.44/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.44/4.98  
% 35.44/4.98  fof(f34,plain,(
% 35.44/4.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 35.44/4.98    inference(cnf_transformation,[],[f5])).
% 35.44/4.98  
% 35.44/4.98  fof(f4,axiom,(
% 35.44/4.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 35.44/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.44/4.98  
% 35.44/4.98  fof(f33,plain,(
% 35.44/4.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 35.44/4.98    inference(cnf_transformation,[],[f4])).
% 35.44/4.98  
% 35.44/4.98  fof(f46,plain,(
% 35.44/4.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 35.44/4.98    inference(definition_unfolding,[],[f34,f33])).
% 35.44/4.98  
% 35.44/4.98  fof(f50,plain,(
% 35.44/4.98    ( ! [X2,X0,X1] : (k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(X2,X1))) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 35.44/4.98    inference(definition_unfolding,[],[f41,f46])).
% 35.44/4.98  
% 35.44/4.98  fof(f1,axiom,(
% 35.44/4.98    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 35.44/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.44/4.98  
% 35.44/4.98  fof(f30,plain,(
% 35.44/4.98    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 35.44/4.98    inference(cnf_transformation,[],[f1])).
% 35.44/4.98  
% 35.44/4.98  fof(f47,plain,(
% 35.44/4.98    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0)) )),
% 35.44/4.98    inference(definition_unfolding,[],[f30,f46])).
% 35.44/4.98  
% 35.44/4.98  fof(f8,axiom,(
% 35.44/4.98    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)))),
% 35.44/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.44/4.98  
% 35.44/4.98  fof(f19,plain,(
% 35.44/4.98    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X0))),
% 35.44/4.98    inference(ennf_transformation,[],[f8])).
% 35.44/4.98  
% 35.44/4.98  fof(f37,plain,(
% 35.44/4.98    ( ! [X2,X0,X1] : (k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) | ~r1_tarski(X1,X2) | ~v1_relat_1(X0)) )),
% 35.44/4.98    inference(cnf_transformation,[],[f19])).
% 35.44/4.98  
% 35.44/4.98  fof(f6,axiom,(
% 35.44/4.98    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 35.44/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.44/4.98  
% 35.44/4.98  fof(f17,plain,(
% 35.44/4.98    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 35.44/4.98    inference(ennf_transformation,[],[f6])).
% 35.44/4.98  
% 35.44/4.98  fof(f35,plain,(
% 35.44/4.98    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 35.44/4.98    inference(cnf_transformation,[],[f17])).
% 35.44/4.98  
% 35.44/4.98  fof(f7,axiom,(
% 35.44/4.98    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 35.44/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.44/4.98  
% 35.44/4.98  fof(f18,plain,(
% 35.44/4.98    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 35.44/4.98    inference(ennf_transformation,[],[f7])).
% 35.44/4.98  
% 35.44/4.98  fof(f36,plain,(
% 35.44/4.98    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 35.44/4.98    inference(cnf_transformation,[],[f18])).
% 35.44/4.98  
% 35.44/4.98  fof(f9,axiom,(
% 35.44/4.98    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)))),
% 35.44/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.44/4.98  
% 35.44/4.98  fof(f20,plain,(
% 35.44/4.98    ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 35.44/4.98    inference(ennf_transformation,[],[f9])).
% 35.44/4.98  
% 35.44/4.98  fof(f38,plain,(
% 35.44/4.98    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 35.44/4.98    inference(cnf_transformation,[],[f20])).
% 35.44/4.98  
% 35.44/4.98  fof(f2,axiom,(
% 35.44/4.98    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 35.44/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.44/4.98  
% 35.44/4.98  fof(f15,plain,(
% 35.44/4.98    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 35.44/4.98    inference(ennf_transformation,[],[f2])).
% 35.44/4.98  
% 35.44/4.98  fof(f16,plain,(
% 35.44/4.98    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 35.44/4.98    inference(flattening,[],[f15])).
% 35.44/4.98  
% 35.44/4.98  fof(f31,plain,(
% 35.44/4.98    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 35.44/4.98    inference(cnf_transformation,[],[f16])).
% 35.44/4.98  
% 35.44/4.98  fof(f48,plain,(
% 35.44/4.98    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k1_enumset1(X1,X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 35.44/4.98    inference(definition_unfolding,[],[f31,f46])).
% 35.44/4.98  
% 35.44/4.98  fof(f3,axiom,(
% 35.44/4.98    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 35.44/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.44/4.98  
% 35.44/4.98  fof(f32,plain,(
% 35.44/4.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 35.44/4.98    inference(cnf_transformation,[],[f3])).
% 35.44/4.98  
% 35.44/4.98  fof(f49,plain,(
% 35.44/4.98    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 35.44/4.98    inference(definition_unfolding,[],[f32,f33,f33])).
% 35.44/4.98  
% 35.44/4.98  fof(f45,plain,(
% 35.44/4.98    ~r1_tarski(k9_relat_1(sK2,k3_xboole_0(sK0,k10_relat_1(sK2,sK1))),k3_xboole_0(k9_relat_1(sK2,sK0),sK1))),
% 35.44/4.98    inference(cnf_transformation,[],[f29])).
% 35.44/4.98  
% 35.44/4.98  fof(f51,plain,(
% 35.44/4.98    ~r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1)))),
% 35.44/4.98    inference(definition_unfolding,[],[f45,f46,f46])).
% 35.44/4.98  
% 35.44/4.98  fof(f12,axiom,(
% 35.44/4.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 35.44/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.44/4.98  
% 35.44/4.98  fof(f24,plain,(
% 35.44/4.98    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 35.44/4.98    inference(ennf_transformation,[],[f12])).
% 35.44/4.98  
% 35.44/4.98  fof(f25,plain,(
% 35.44/4.98    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 35.44/4.98    inference(flattening,[],[f24])).
% 35.44/4.98  
% 35.44/4.98  fof(f42,plain,(
% 35.44/4.98    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 35.44/4.98    inference(cnf_transformation,[],[f25])).
% 35.44/4.98  
% 35.44/4.98  fof(f10,axiom,(
% 35.44/4.98    ! [X0,X1] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))))),
% 35.44/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.44/4.98  
% 35.44/4.98  fof(f21,plain,(
% 35.44/4.98    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 35.44/4.98    inference(ennf_transformation,[],[f10])).
% 35.44/4.98  
% 35.44/4.98  fof(f22,plain,(
% 35.44/4.98    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 35.44/4.98    inference(flattening,[],[f21])).
% 35.44/4.98  
% 35.44/4.98  fof(f40,plain,(
% 35.44/4.98    ( ! [X0,X1] : (v1_funct_1(k7_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 35.44/4.98    inference(cnf_transformation,[],[f22])).
% 35.44/4.98  
% 35.44/4.98  fof(f44,plain,(
% 35.44/4.98    v1_funct_1(sK2)),
% 35.44/4.98    inference(cnf_transformation,[],[f29])).
% 35.44/4.98  
% 35.44/4.98  cnf(c_13,negated_conjecture,
% 35.44/4.98      ( v1_relat_1(sK2) ),
% 35.44/4.98      inference(cnf_transformation,[],[f43]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_241,negated_conjecture,
% 35.44/4.98      ( v1_relat_1(sK2) ),
% 35.44/4.98      inference(subtyping,[status(esa)],[c_13]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_513,plain,
% 35.44/4.98      ( v1_relat_1(sK2) = iProver_top ),
% 35.44/4.98      inference(predicate_to_equality,[status(thm)],[c_241]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_9,plain,
% 35.44/4.98      ( ~ v1_relat_1(X0)
% 35.44/4.98      | k1_setfam_1(k1_enumset1(X1,X1,k10_relat_1(X0,X2))) = k10_relat_1(k7_relat_1(X0,X1),X2) ),
% 35.44/4.98      inference(cnf_transformation,[],[f50]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_245,plain,
% 35.44/4.98      ( ~ v1_relat_1(X0_40)
% 35.44/4.98      | k1_setfam_1(k1_enumset1(X0_41,X0_41,k10_relat_1(X0_40,X1_41))) = k10_relat_1(k7_relat_1(X0_40,X0_41),X1_41) ),
% 35.44/4.98      inference(subtyping,[status(esa)],[c_9]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_509,plain,
% 35.44/4.98      ( k1_setfam_1(k1_enumset1(X0_41,X0_41,k10_relat_1(X0_40,X1_41))) = k10_relat_1(k7_relat_1(X0_40,X0_41),X1_41)
% 35.44/4.98      | v1_relat_1(X0_40) != iProver_top ),
% 35.44/4.98      inference(predicate_to_equality,[status(thm)],[c_245]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_960,plain,
% 35.44/4.98      ( k1_setfam_1(k1_enumset1(X0_41,X0_41,k10_relat_1(sK2,X1_41))) = k10_relat_1(k7_relat_1(sK2,X0_41),X1_41) ),
% 35.44/4.98      inference(superposition,[status(thm)],[c_513,c_509]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_0,plain,
% 35.44/4.98      ( r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) ),
% 35.44/4.98      inference(cnf_transformation,[],[f47]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_253,plain,
% 35.44/4.98      ( r1_tarski(k1_setfam_1(k1_enumset1(X0_41,X0_41,X1_41)),X0_41) ),
% 35.44/4.98      inference(subtyping,[status(esa)],[c_0]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_502,plain,
% 35.44/4.98      ( r1_tarski(k1_setfam_1(k1_enumset1(X0_41,X0_41,X1_41)),X0_41) = iProver_top ),
% 35.44/4.98      inference(predicate_to_equality,[status(thm)],[c_253]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_5,plain,
% 35.44/4.98      ( ~ r1_tarski(X0,X1)
% 35.44/4.98      | ~ v1_relat_1(X2)
% 35.44/4.98      | k9_relat_1(k7_relat_1(X2,X1),X0) = k9_relat_1(X2,X0) ),
% 35.44/4.98      inference(cnf_transformation,[],[f37]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_248,plain,
% 35.44/4.98      ( ~ r1_tarski(X0_41,X1_41)
% 35.44/4.98      | ~ v1_relat_1(X0_40)
% 35.44/4.98      | k9_relat_1(k7_relat_1(X0_40,X1_41),X0_41) = k9_relat_1(X0_40,X0_41) ),
% 35.44/4.98      inference(subtyping,[status(esa)],[c_5]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_506,plain,
% 35.44/4.98      ( k9_relat_1(k7_relat_1(X0_40,X0_41),X1_41) = k9_relat_1(X0_40,X1_41)
% 35.44/4.98      | r1_tarski(X1_41,X0_41) != iProver_top
% 35.44/4.98      | v1_relat_1(X0_40) != iProver_top ),
% 35.44/4.98      inference(predicate_to_equality,[status(thm)],[c_248]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_1239,plain,
% 35.44/4.98      ( k9_relat_1(k7_relat_1(X0_40,X0_41),k1_setfam_1(k1_enumset1(X0_41,X0_41,X1_41))) = k9_relat_1(X0_40,k1_setfam_1(k1_enumset1(X0_41,X0_41,X1_41)))
% 35.44/4.98      | v1_relat_1(X0_40) != iProver_top ),
% 35.44/4.98      inference(superposition,[status(thm)],[c_502,c_506]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_2955,plain,
% 35.44/4.98      ( k9_relat_1(k7_relat_1(sK2,X0_41),k1_setfam_1(k1_enumset1(X0_41,X0_41,X1_41))) = k9_relat_1(sK2,k1_setfam_1(k1_enumset1(X0_41,X0_41,X1_41))) ),
% 35.44/4.98      inference(superposition,[status(thm)],[c_513,c_1239]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_2961,plain,
% 35.44/4.98      ( k9_relat_1(sK2,k1_setfam_1(k1_enumset1(X0_41,X0_41,k10_relat_1(sK2,X1_41)))) = k9_relat_1(k7_relat_1(sK2,X0_41),k10_relat_1(k7_relat_1(sK2,X0_41),X1_41)) ),
% 35.44/4.98      inference(superposition,[status(thm)],[c_960,c_2955]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_2975,plain,
% 35.44/4.98      ( k9_relat_1(k7_relat_1(sK2,X0_41),k10_relat_1(k7_relat_1(sK2,X0_41),X1_41)) = k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X0_41),X1_41)) ),
% 35.44/4.98      inference(light_normalisation,[status(thm)],[c_2961,c_960]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_3,plain,
% 35.44/4.98      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 35.44/4.98      inference(cnf_transformation,[],[f35]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_250,plain,
% 35.44/4.98      ( ~ v1_relat_1(X0_40) | v1_relat_1(k7_relat_1(X0_40,X0_41)) ),
% 35.44/4.98      inference(subtyping,[status(esa)],[c_3]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_504,plain,
% 35.44/4.98      ( v1_relat_1(X0_40) != iProver_top
% 35.44/4.98      | v1_relat_1(k7_relat_1(X0_40,X0_41)) = iProver_top ),
% 35.44/4.98      inference(predicate_to_equality,[status(thm)],[c_250]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_4,plain,
% 35.44/4.98      ( ~ v1_relat_1(X0)
% 35.44/4.98      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 35.44/4.98      inference(cnf_transformation,[],[f36]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_249,plain,
% 35.44/4.98      ( ~ v1_relat_1(X0_40)
% 35.44/4.98      | k2_relat_1(k7_relat_1(X0_40,X0_41)) = k9_relat_1(X0_40,X0_41) ),
% 35.44/4.98      inference(subtyping,[status(esa)],[c_4]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_505,plain,
% 35.44/4.98      ( k2_relat_1(k7_relat_1(X0_40,X0_41)) = k9_relat_1(X0_40,X0_41)
% 35.44/4.98      | v1_relat_1(X0_40) != iProver_top ),
% 35.44/4.98      inference(predicate_to_equality,[status(thm)],[c_249]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_824,plain,
% 35.44/4.98      ( k2_relat_1(k7_relat_1(k7_relat_1(X0_40,X0_41),X1_41)) = k9_relat_1(k7_relat_1(X0_40,X0_41),X1_41)
% 35.44/4.98      | v1_relat_1(X0_40) != iProver_top ),
% 35.44/4.98      inference(superposition,[status(thm)],[c_504,c_505]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_1338,plain,
% 35.44/4.98      ( k2_relat_1(k7_relat_1(k7_relat_1(sK2,X0_41),X1_41)) = k9_relat_1(k7_relat_1(sK2,X0_41),X1_41) ),
% 35.44/4.98      inference(superposition,[status(thm)],[c_513,c_824]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_6,plain,
% 35.44/4.98      ( r1_tarski(k2_relat_1(k7_relat_1(X0,X1)),k2_relat_1(X0))
% 35.44/4.98      | ~ v1_relat_1(X0) ),
% 35.44/4.98      inference(cnf_transformation,[],[f38]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_247,plain,
% 35.44/4.98      ( r1_tarski(k2_relat_1(k7_relat_1(X0_40,X0_41)),k2_relat_1(X0_40))
% 35.44/4.98      | ~ v1_relat_1(X0_40) ),
% 35.44/4.98      inference(subtyping,[status(esa)],[c_6]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_507,plain,
% 35.44/4.98      ( r1_tarski(k2_relat_1(k7_relat_1(X0_40,X0_41)),k2_relat_1(X0_40)) = iProver_top
% 35.44/4.98      | v1_relat_1(X0_40) != iProver_top ),
% 35.44/4.98      inference(predicate_to_equality,[status(thm)],[c_247]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_1439,plain,
% 35.44/4.98      ( r1_tarski(k9_relat_1(k7_relat_1(sK2,X0_41),X1_41),k2_relat_1(k7_relat_1(sK2,X0_41))) = iProver_top
% 35.44/4.98      | v1_relat_1(k7_relat_1(sK2,X0_41)) != iProver_top ),
% 35.44/4.98      inference(superposition,[status(thm)],[c_1338,c_507]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_823,plain,
% 35.44/4.98      ( k2_relat_1(k7_relat_1(sK2,X0_41)) = k9_relat_1(sK2,X0_41) ),
% 35.44/4.98      inference(superposition,[status(thm)],[c_513,c_505]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_1440,plain,
% 35.44/4.98      ( r1_tarski(k9_relat_1(k7_relat_1(sK2,X0_41),X1_41),k9_relat_1(sK2,X0_41)) = iProver_top
% 35.44/4.98      | v1_relat_1(k7_relat_1(sK2,X0_41)) != iProver_top ),
% 35.44/4.98      inference(light_normalisation,[status(thm)],[c_1439,c_823]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_3100,plain,
% 35.44/4.98      ( r1_tarski(k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,X0_41),X1_41)),k9_relat_1(sK2,X0_41)) = iProver_top
% 35.44/4.98      | v1_relat_1(k7_relat_1(sK2,X0_41)) != iProver_top ),
% 35.44/4.98      inference(superposition,[status(thm)],[c_2975,c_1440]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_1,plain,
% 35.44/4.98      ( ~ r1_tarski(X0,X1)
% 35.44/4.98      | ~ r1_tarski(X0,X2)
% 35.44/4.98      | r1_tarski(X0,k1_setfam_1(k1_enumset1(X2,X2,X1))) ),
% 35.44/4.98      inference(cnf_transformation,[],[f48]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_252,plain,
% 35.44/4.98      ( ~ r1_tarski(X0_41,X1_41)
% 35.44/4.98      | ~ r1_tarski(X0_41,X2_41)
% 35.44/4.98      | r1_tarski(X0_41,k1_setfam_1(k1_enumset1(X2_41,X2_41,X1_41))) ),
% 35.44/4.98      inference(subtyping,[status(esa)],[c_1]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_503,plain,
% 35.44/4.98      ( r1_tarski(X0_41,X1_41) != iProver_top
% 35.44/4.98      | r1_tarski(X0_41,X2_41) != iProver_top
% 35.44/4.98      | r1_tarski(X0_41,k1_setfam_1(k1_enumset1(X2_41,X2_41,X1_41))) = iProver_top ),
% 35.44/4.98      inference(predicate_to_equality,[status(thm)],[c_252]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_2,plain,
% 35.44/4.98      ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
% 35.44/4.98      inference(cnf_transformation,[],[f49]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_251,plain,
% 35.44/4.98      ( k1_enumset1(X0_41,X0_41,X1_41) = k1_enumset1(X1_41,X1_41,X0_41) ),
% 35.44/4.98      inference(subtyping,[status(esa)],[c_2]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_11,negated_conjecture,
% 35.44/4.98      ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1))) ),
% 35.44/4.98      inference(cnf_transformation,[],[f51]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_243,negated_conjecture,
% 35.44/4.98      ( ~ r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1))) ),
% 35.44/4.98      inference(subtyping,[status(esa)],[c_11]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_511,plain,
% 35.44/4.98      ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k1_enumset1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK0),sK1))) != iProver_top ),
% 35.44/4.98      inference(predicate_to_equality,[status(thm)],[c_243]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_629,plain,
% 35.44/4.98      ( r1_tarski(k9_relat_1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))),k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0)))) != iProver_top ),
% 35.44/4.98      inference(demodulation,[status(thm)],[c_251,c_511]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_1023,plain,
% 35.44/4.98      ( r1_tarski(k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1)),k1_setfam_1(k1_enumset1(sK1,sK1,k9_relat_1(sK2,sK0)))) != iProver_top ),
% 35.44/4.98      inference(demodulation,[status(thm)],[c_960,c_629]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_1234,plain,
% 35.44/4.98      ( r1_tarski(k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1)),k9_relat_1(sK2,sK0)) != iProver_top
% 35.44/4.98      | r1_tarski(k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1)),sK1) != iProver_top ),
% 35.44/4.98      inference(superposition,[status(thm)],[c_503,c_1023]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_105271,plain,
% 35.44/4.98      ( r1_tarski(k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1)),sK1) != iProver_top
% 35.44/4.98      | v1_relat_1(k7_relat_1(sK2,sK0)) != iProver_top ),
% 35.44/4.98      inference(superposition,[status(thm)],[c_3100,c_1234]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_262,plain,
% 35.44/4.98      ( ~ r1_tarski(X0_41,X1_41)
% 35.44/4.98      | r1_tarski(X2_41,X3_41)
% 35.44/4.98      | X2_41 != X0_41
% 35.44/4.98      | X3_41 != X1_41 ),
% 35.44/4.98      theory(equality) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_2532,plain,
% 35.44/4.98      ( r1_tarski(X0_41,X1_41)
% 35.44/4.98      | ~ r1_tarski(k1_setfam_1(k1_enumset1(X2_41,X2_41,X3_41)),X2_41)
% 35.44/4.98      | X1_41 != X2_41
% 35.44/4.98      | X0_41 != k1_setfam_1(k1_enumset1(X2_41,X2_41,X3_41)) ),
% 35.44/4.98      inference(instantiation,[status(thm)],[c_262]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_27747,plain,
% 35.44/4.98      ( r1_tarski(k10_relat_1(k7_relat_1(sK2,sK0),sK1),X0_41)
% 35.44/4.98      | ~ r1_tarski(k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1))),sK0)
% 35.44/4.98      | X0_41 != sK0
% 35.44/4.98      | k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1))) ),
% 35.44/4.98      inference(instantiation,[status(thm)],[c_2532]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_27749,plain,
% 35.44/4.98      ( r1_tarski(k10_relat_1(k7_relat_1(sK2,sK0),sK1),sK0)
% 35.44/4.98      | ~ r1_tarski(k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1))),sK0)
% 35.44/4.98      | k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))
% 35.44/4.98      | sK0 != sK0 ),
% 35.44/4.98      inference(instantiation,[status(thm)],[c_27747]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_659,plain,
% 35.44/4.98      ( ~ r1_tarski(X0_41,X1_41)
% 35.44/4.98      | r1_tarski(X2_41,sK1)
% 35.44/4.98      | X2_41 != X0_41
% 35.44/4.98      | sK1 != X1_41 ),
% 35.44/4.98      inference(instantiation,[status(thm)],[c_262]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_790,plain,
% 35.44/4.98      ( ~ r1_tarski(X0_41,sK1)
% 35.44/4.98      | r1_tarski(X1_41,sK1)
% 35.44/4.98      | X1_41 != X0_41
% 35.44/4.98      | sK1 != sK1 ),
% 35.44/4.98      inference(instantiation,[status(thm)],[c_659]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_1044,plain,
% 35.44/4.98      ( r1_tarski(X0_41,sK1)
% 35.44/4.98      | ~ r1_tarski(k9_relat_1(X0_40,k10_relat_1(X0_40,sK1)),sK1)
% 35.44/4.98      | X0_41 != k9_relat_1(X0_40,k10_relat_1(X0_40,sK1))
% 35.44/4.98      | sK1 != sK1 ),
% 35.44/4.98      inference(instantiation,[status(thm)],[c_790]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_1964,plain,
% 35.44/4.98      ( r1_tarski(k9_relat_1(X0_40,X0_41),sK1)
% 35.44/4.98      | ~ r1_tarski(k9_relat_1(X1_40,k10_relat_1(X1_40,sK1)),sK1)
% 35.44/4.98      | k9_relat_1(X0_40,X0_41) != k9_relat_1(X1_40,k10_relat_1(X1_40,sK1))
% 35.44/4.98      | sK1 != sK1 ),
% 35.44/4.98      inference(instantiation,[status(thm)],[c_1044]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_10712,plain,
% 35.44/4.98      ( r1_tarski(k9_relat_1(X0_40,k10_relat_1(k7_relat_1(sK2,sK0),sK1)),sK1)
% 35.44/4.98      | ~ r1_tarski(k9_relat_1(k7_relat_1(sK2,sK0),k10_relat_1(k7_relat_1(sK2,sK0),sK1)),sK1)
% 35.44/4.98      | k9_relat_1(X0_40,k10_relat_1(k7_relat_1(sK2,sK0),sK1)) != k9_relat_1(k7_relat_1(sK2,sK0),k10_relat_1(k7_relat_1(sK2,sK0),sK1))
% 35.44/4.98      | sK1 != sK1 ),
% 35.44/4.98      inference(instantiation,[status(thm)],[c_1964]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_10714,plain,
% 35.44/4.98      ( k9_relat_1(X0_40,k10_relat_1(k7_relat_1(sK2,sK0),sK1)) != k9_relat_1(k7_relat_1(sK2,sK0),k10_relat_1(k7_relat_1(sK2,sK0),sK1))
% 35.44/4.98      | sK1 != sK1
% 35.44/4.98      | r1_tarski(k9_relat_1(X0_40,k10_relat_1(k7_relat_1(sK2,sK0),sK1)),sK1) = iProver_top
% 35.44/4.98      | r1_tarski(k9_relat_1(k7_relat_1(sK2,sK0),k10_relat_1(k7_relat_1(sK2,sK0),sK1)),sK1) != iProver_top ),
% 35.44/4.98      inference(predicate_to_equality,[status(thm)],[c_10712]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_10716,plain,
% 35.44/4.98      ( k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1)) != k9_relat_1(k7_relat_1(sK2,sK0),k10_relat_1(k7_relat_1(sK2,sK0),sK1))
% 35.44/4.98      | sK1 != sK1
% 35.44/4.98      | r1_tarski(k9_relat_1(k7_relat_1(sK2,sK0),k10_relat_1(k7_relat_1(sK2,sK0),sK1)),sK1) != iProver_top
% 35.44/4.98      | r1_tarski(k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1)),sK1) = iProver_top ),
% 35.44/4.98      inference(instantiation,[status(thm)],[c_10714]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_258,plain,
% 35.44/4.98      ( X0_41 != X1_41 | X2_41 != X1_41 | X2_41 = X0_41 ),
% 35.44/4.98      theory(equality) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_1008,plain,
% 35.44/4.98      ( X0_41 != X1_41
% 35.44/4.98      | X0_41 = k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))
% 35.44/4.98      | k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1))) != X1_41 ),
% 35.44/4.98      inference(instantiation,[status(thm)],[c_258]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_1860,plain,
% 35.44/4.98      ( X0_41 != k10_relat_1(k7_relat_1(sK2,sK0),sK1)
% 35.44/4.98      | X0_41 = k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))
% 35.44/4.98      | k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1))) != k10_relat_1(k7_relat_1(sK2,sK0),sK1) ),
% 35.44/4.98      inference(instantiation,[status(thm)],[c_1008]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_3854,plain,
% 35.44/4.98      ( k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k10_relat_1(k7_relat_1(sK2,sK0),sK1)
% 35.44/4.98      | k10_relat_1(k7_relat_1(sK2,sK0),sK1) = k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1)))
% 35.44/4.98      | k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1))) != k10_relat_1(k7_relat_1(sK2,sK0),sK1) ),
% 35.44/4.98      inference(instantiation,[status(thm)],[c_1860]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_1293,plain,
% 35.44/4.98      ( X0_41 != X1_41
% 35.44/4.98      | X0_41 = k9_relat_1(X0_40,k10_relat_1(k7_relat_1(sK2,sK0),sK1))
% 35.44/4.98      | k9_relat_1(X0_40,k10_relat_1(k7_relat_1(sK2,sK0),sK1)) != X1_41 ),
% 35.44/4.98      inference(instantiation,[status(thm)],[c_258]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_1622,plain,
% 35.44/4.98      ( X0_41 != k9_relat_1(X0_40,k10_relat_1(k7_relat_1(sK2,sK0),sK1))
% 35.44/4.98      | X0_41 = k9_relat_1(k7_relat_1(X0_40,X1_41),k10_relat_1(k7_relat_1(sK2,sK0),sK1))
% 35.44/4.98      | k9_relat_1(k7_relat_1(X0_40,X1_41),k10_relat_1(k7_relat_1(sK2,sK0),sK1)) != k9_relat_1(X0_40,k10_relat_1(k7_relat_1(sK2,sK0),sK1)) ),
% 35.44/4.98      inference(instantiation,[status(thm)],[c_1293]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_3589,plain,
% 35.44/4.98      ( k9_relat_1(X0_40,k10_relat_1(k7_relat_1(sK2,sK0),sK1)) != k9_relat_1(X0_40,k10_relat_1(k7_relat_1(sK2,sK0),sK1))
% 35.44/4.98      | k9_relat_1(X0_40,k10_relat_1(k7_relat_1(sK2,sK0),sK1)) = k9_relat_1(k7_relat_1(X0_40,X0_41),k10_relat_1(k7_relat_1(sK2,sK0),sK1))
% 35.44/4.98      | k9_relat_1(k7_relat_1(X0_40,X0_41),k10_relat_1(k7_relat_1(sK2,sK0),sK1)) != k9_relat_1(X0_40,k10_relat_1(k7_relat_1(sK2,sK0),sK1)) ),
% 35.44/4.98      inference(instantiation,[status(thm)],[c_1622]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_3590,plain,
% 35.44/4.98      ( k9_relat_1(k7_relat_1(sK2,sK0),k10_relat_1(k7_relat_1(sK2,sK0),sK1)) != k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1))
% 35.44/4.98      | k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1)) = k9_relat_1(k7_relat_1(sK2,sK0),k10_relat_1(k7_relat_1(sK2,sK0),sK1))
% 35.44/4.98      | k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1)) != k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1)) ),
% 35.44/4.98      inference(instantiation,[status(thm)],[c_3589]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_265,plain,
% 35.44/4.98      ( X0_41 != X1_41
% 35.44/4.98      | k9_relat_1(X0_40,X0_41) = k9_relat_1(X1_40,X1_41)
% 35.44/4.98      | X0_40 != X1_40 ),
% 35.44/4.98      theory(equality) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_1632,plain,
% 35.44/4.98      ( X0_41 != k10_relat_1(k7_relat_1(sK2,sK0),sK1)
% 35.44/4.98      | k9_relat_1(X0_40,X0_41) = k9_relat_1(X1_40,k10_relat_1(k7_relat_1(sK2,sK0),sK1))
% 35.44/4.98      | X0_40 != X1_40 ),
% 35.44/4.98      inference(instantiation,[status(thm)],[c_265]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_3485,plain,
% 35.44/4.98      ( k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k10_relat_1(k7_relat_1(sK2,sK0),sK1)
% 35.44/4.98      | k9_relat_1(X0_40,k10_relat_1(k7_relat_1(sK2,sK0),sK1)) = k9_relat_1(X1_40,k10_relat_1(k7_relat_1(sK2,sK0),sK1))
% 35.44/4.98      | X0_40 != X1_40 ),
% 35.44/4.98      inference(instantiation,[status(thm)],[c_1632]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_3486,plain,
% 35.44/4.98      ( k10_relat_1(k7_relat_1(sK2,sK0),sK1) != k10_relat_1(k7_relat_1(sK2,sK0),sK1)
% 35.44/4.98      | k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1)) = k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1))
% 35.44/4.98      | sK2 != sK2 ),
% 35.44/4.98      inference(instantiation,[status(thm)],[c_3485]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_256,plain,( X0_41 = X0_41 ),theory(equality) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_3473,plain,
% 35.44/4.98      ( k10_relat_1(k7_relat_1(sK2,sK0),sK1) = k10_relat_1(k7_relat_1(sK2,sK0),sK1) ),
% 35.44/4.98      inference(instantiation,[status(thm)],[c_256]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_1614,plain,
% 35.44/4.98      ( ~ r1_tarski(k10_relat_1(k7_relat_1(sK2,sK0),sK1),X0_41)
% 35.44/4.98      | ~ v1_relat_1(X0_40)
% 35.44/4.98      | k9_relat_1(k7_relat_1(X0_40,X0_41),k10_relat_1(k7_relat_1(sK2,sK0),sK1)) = k9_relat_1(X0_40,k10_relat_1(k7_relat_1(sK2,sK0),sK1)) ),
% 35.44/4.98      inference(instantiation,[status(thm)],[c_248]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_1616,plain,
% 35.44/4.98      ( ~ r1_tarski(k10_relat_1(k7_relat_1(sK2,sK0),sK1),sK0)
% 35.44/4.98      | ~ v1_relat_1(sK2)
% 35.44/4.98      | k9_relat_1(k7_relat_1(sK2,sK0),k10_relat_1(k7_relat_1(sK2,sK0),sK1)) = k9_relat_1(sK2,k10_relat_1(k7_relat_1(sK2,sK0),sK1)) ),
% 35.44/4.98      inference(instantiation,[status(thm)],[c_1614]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_10,plain,
% 35.44/4.98      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
% 35.44/4.98      | ~ v1_funct_1(X0)
% 35.44/4.98      | ~ v1_relat_1(X0) ),
% 35.44/4.98      inference(cnf_transformation,[],[f42]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_244,plain,
% 35.44/4.98      ( r1_tarski(k9_relat_1(X0_40,k10_relat_1(X0_40,X0_41)),X0_41)
% 35.44/4.98      | ~ v1_funct_1(X0_40)
% 35.44/4.98      | ~ v1_relat_1(X0_40) ),
% 35.44/4.98      inference(subtyping,[status(esa)],[c_10]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_770,plain,
% 35.44/4.98      ( r1_tarski(k9_relat_1(X0_40,k10_relat_1(X0_40,sK1)),sK1)
% 35.44/4.98      | ~ v1_funct_1(X0_40)
% 35.44/4.98      | ~ v1_relat_1(X0_40) ),
% 35.44/4.98      inference(instantiation,[status(thm)],[c_244]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_1313,plain,
% 35.44/4.98      ( r1_tarski(k9_relat_1(k7_relat_1(sK2,sK0),k10_relat_1(k7_relat_1(sK2,sK0),sK1)),sK1)
% 35.44/4.98      | ~ v1_funct_1(k7_relat_1(sK2,sK0))
% 35.44/4.98      | ~ v1_relat_1(k7_relat_1(sK2,sK0)) ),
% 35.44/4.98      inference(instantiation,[status(thm)],[c_770]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_1314,plain,
% 35.44/4.98      ( r1_tarski(k9_relat_1(k7_relat_1(sK2,sK0),k10_relat_1(k7_relat_1(sK2,sK0),sK1)),sK1) = iProver_top
% 35.44/4.98      | v1_funct_1(k7_relat_1(sK2,sK0)) != iProver_top
% 35.44/4.98      | v1_relat_1(k7_relat_1(sK2,sK0)) != iProver_top ),
% 35.44/4.98      inference(predicate_to_equality,[status(thm)],[c_1313]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_1141,plain,
% 35.44/4.98      ( r1_tarski(k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1))),sK0) ),
% 35.44/4.98      inference(instantiation,[status(thm)],[c_253]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_902,plain,
% 35.44/4.98      ( ~ v1_relat_1(sK2)
% 35.44/4.98      | k1_setfam_1(k1_enumset1(sK0,sK0,k10_relat_1(sK2,sK1))) = k10_relat_1(k7_relat_1(sK2,sK0),sK1) ),
% 35.44/4.98      inference(instantiation,[status(thm)],[c_245]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_595,plain,
% 35.44/4.98      ( sK1 = sK1 ),
% 35.44/4.98      inference(instantiation,[status(thm)],[c_256]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_7,plain,
% 35.44/4.98      ( ~ v1_funct_1(X0)
% 35.44/4.98      | v1_funct_1(k7_relat_1(X0,X1))
% 35.44/4.98      | ~ v1_relat_1(X0) ),
% 35.44/4.98      inference(cnf_transformation,[],[f40]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_246,plain,
% 35.44/4.98      ( ~ v1_funct_1(X0_40)
% 35.44/4.98      | v1_funct_1(k7_relat_1(X0_40,X0_41))
% 35.44/4.98      | ~ v1_relat_1(X0_40) ),
% 35.44/4.98      inference(subtyping,[status(esa)],[c_7]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_299,plain,
% 35.44/4.98      ( v1_funct_1(X0_40) != iProver_top
% 35.44/4.98      | v1_funct_1(k7_relat_1(X0_40,X0_41)) = iProver_top
% 35.44/4.98      | v1_relat_1(X0_40) != iProver_top ),
% 35.44/4.98      inference(predicate_to_equality,[status(thm)],[c_246]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_301,plain,
% 35.44/4.98      ( v1_funct_1(k7_relat_1(sK2,sK0)) = iProver_top
% 35.44/4.98      | v1_funct_1(sK2) != iProver_top
% 35.44/4.98      | v1_relat_1(sK2) != iProver_top ),
% 35.44/4.98      inference(instantiation,[status(thm)],[c_299]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_287,plain,
% 35.44/4.98      ( v1_relat_1(X0_40) != iProver_top
% 35.44/4.98      | v1_relat_1(k7_relat_1(X0_40,X0_41)) = iProver_top ),
% 35.44/4.98      inference(predicate_to_equality,[status(thm)],[c_250]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_289,plain,
% 35.44/4.98      ( v1_relat_1(k7_relat_1(sK2,sK0)) = iProver_top
% 35.44/4.98      | v1_relat_1(sK2) != iProver_top ),
% 35.44/4.98      inference(instantiation,[status(thm)],[c_287]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_278,plain,
% 35.44/4.98      ( sK0 = sK0 ),
% 35.44/4.98      inference(instantiation,[status(thm)],[c_256]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_255,plain,( X0_40 = X0_40 ),theory(equality) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_277,plain,
% 35.44/4.98      ( sK2 = sK2 ),
% 35.44/4.98      inference(instantiation,[status(thm)],[c_255]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_12,negated_conjecture,
% 35.44/4.98      ( v1_funct_1(sK2) ),
% 35.44/4.98      inference(cnf_transformation,[],[f44]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_15,plain,
% 35.44/4.98      ( v1_funct_1(sK2) = iProver_top ),
% 35.44/4.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(c_14,plain,
% 35.44/4.98      ( v1_relat_1(sK2) = iProver_top ),
% 35.44/4.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 35.44/4.98  
% 35.44/4.98  cnf(contradiction,plain,
% 35.44/4.98      ( $false ),
% 35.44/4.98      inference(minisat,
% 35.44/4.98                [status(thm)],
% 35.44/4.98                [c_105271,c_27749,c_10716,c_3854,c_3590,c_3486,c_3473,
% 35.44/4.98                 c_1616,c_1314,c_1141,c_902,c_595,c_301,c_289,c_278,
% 35.44/4.98                 c_277,c_15,c_14,c_13]) ).
% 35.44/4.98  
% 35.44/4.98  
% 35.44/4.98  % SZS output end CNFRefutation for theBenchmark.p
% 35.44/4.98  
% 35.44/4.98  ------                               Statistics
% 35.44/4.98  
% 35.44/4.98  ------ General
% 35.44/4.98  
% 35.44/4.98  abstr_ref_over_cycles:                  0
% 35.44/4.98  abstr_ref_under_cycles:                 0
% 35.44/4.98  gc_basic_clause_elim:                   0
% 35.44/4.98  forced_gc_time:                         0
% 35.44/4.98  parsing_time:                           0.008
% 35.44/4.98  unif_index_cands_time:                  0.
% 35.44/4.98  unif_index_add_time:                    0.
% 35.44/4.98  orderings_time:                         0.
% 35.44/4.98  out_proof_time:                         0.011
% 35.44/4.98  total_time:                             4.465
% 35.44/4.98  num_of_symbols:                         43
% 35.44/4.98  num_of_terms:                           151130
% 35.44/4.98  
% 35.44/4.98  ------ Preprocessing
% 35.44/4.98  
% 35.44/4.98  num_of_splits:                          0
% 35.44/4.98  num_of_split_atoms:                     0
% 35.44/4.98  num_of_reused_defs:                     0
% 35.44/4.98  num_eq_ax_congr_red:                    6
% 35.44/4.98  num_of_sem_filtered_clauses:            1
% 35.44/4.98  num_of_subtypes:                        3
% 35.44/4.98  monotx_restored_types:                  0
% 35.44/4.98  sat_num_of_epr_types:                   0
% 35.44/4.98  sat_num_of_non_cyclic_types:            0
% 35.44/4.98  sat_guarded_non_collapsed_types:        0
% 35.44/4.98  num_pure_diseq_elim:                    0
% 35.44/4.98  simp_replaced_by:                       0
% 35.44/4.98  res_preprocessed:                       79
% 35.44/4.98  prep_upred:                             0
% 35.44/4.98  prep_unflattend:                        0
% 35.44/4.98  smt_new_axioms:                         0
% 35.44/4.98  pred_elim_cands:                        3
% 35.44/4.98  pred_elim:                              0
% 35.44/4.98  pred_elim_cl:                           0
% 35.44/4.98  pred_elim_cycles:                       2
% 35.44/4.98  merged_defs:                            0
% 35.44/4.98  merged_defs_ncl:                        0
% 35.44/4.98  bin_hyper_res:                          0
% 35.44/4.98  prep_cycles:                            4
% 35.44/4.98  pred_elim_time:                         0.
% 35.44/4.98  splitting_time:                         0.
% 35.44/4.98  sem_filter_time:                        0.
% 35.44/4.98  monotx_time:                            0.
% 35.44/4.98  subtype_inf_time:                       0.
% 35.44/4.98  
% 35.44/4.98  ------ Problem properties
% 35.44/4.98  
% 35.44/4.98  clauses:                                13
% 35.44/4.98  conjectures:                            3
% 35.44/4.98  epr:                                    2
% 35.44/4.98  horn:                                   13
% 35.44/4.98  ground:                                 3
% 35.44/4.98  unary:                                  5
% 35.44/4.98  binary:                                 4
% 35.44/4.98  lits:                                   25
% 35.44/4.98  lits_eq:                                4
% 35.44/4.98  fd_pure:                                0
% 35.44/4.98  fd_pseudo:                              0
% 35.44/4.98  fd_cond:                                0
% 35.44/4.98  fd_pseudo_cond:                         0
% 35.44/4.98  ac_symbols:                             0
% 35.44/4.98  
% 35.44/4.98  ------ Propositional Solver
% 35.44/4.98  
% 35.44/4.98  prop_solver_calls:                      38
% 35.44/4.98  prop_fast_solver_calls:                 1019
% 35.44/4.98  smt_solver_calls:                       0
% 35.44/4.98  smt_fast_solver_calls:                  0
% 35.44/4.98  prop_num_of_clauses:                    30757
% 35.44/4.98  prop_preprocess_simplified:             35936
% 35.44/4.98  prop_fo_subsumed:                       5
% 35.44/4.98  prop_solver_time:                       0.
% 35.44/4.98  smt_solver_time:                        0.
% 35.44/4.98  smt_fast_solver_time:                   0.
% 35.44/4.98  prop_fast_solver_time:                  0.
% 35.44/4.98  prop_unsat_core_time:                   0.002
% 35.44/4.98  
% 35.44/4.98  ------ QBF
% 35.44/4.98  
% 35.44/4.98  qbf_q_res:                              0
% 35.44/4.98  qbf_num_tautologies:                    0
% 35.44/4.98  qbf_prep_cycles:                        0
% 35.44/4.98  
% 35.44/4.98  ------ BMC1
% 35.44/4.98  
% 35.44/4.98  bmc1_current_bound:                     -1
% 35.44/4.98  bmc1_last_solved_bound:                 -1
% 35.44/4.98  bmc1_unsat_core_size:                   -1
% 35.44/4.99  bmc1_unsat_core_parents_size:           -1
% 35.44/4.99  bmc1_merge_next_fun:                    0
% 35.44/4.99  bmc1_unsat_core_clauses_time:           0.
% 35.44/4.99  
% 35.44/4.99  ------ Instantiation
% 35.44/4.99  
% 35.44/4.99  inst_num_of_clauses:                    5614
% 35.44/4.99  inst_num_in_passive:                    823
% 35.44/4.99  inst_num_in_active:                     2168
% 35.44/4.99  inst_num_in_unprocessed:                2630
% 35.44/4.99  inst_num_of_loops:                      2350
% 35.44/4.99  inst_num_of_learning_restarts:          0
% 35.44/4.99  inst_num_moves_active_passive:          176
% 35.44/4.99  inst_lit_activity:                      0
% 35.44/4.99  inst_lit_activity_moves:                1
% 35.44/4.99  inst_num_tautologies:                   0
% 35.44/4.99  inst_num_prop_implied:                  0
% 35.44/4.99  inst_num_existing_simplified:           0
% 35.44/4.99  inst_num_eq_res_simplified:             0
% 35.44/4.99  inst_num_child_elim:                    0
% 35.44/4.99  inst_num_of_dismatching_blockings:      7752
% 35.44/4.99  inst_num_of_non_proper_insts:           10839
% 35.44/4.99  inst_num_of_duplicates:                 0
% 35.44/4.99  inst_inst_num_from_inst_to_res:         0
% 35.44/4.99  inst_dismatching_checking_time:         0.
% 35.44/4.99  
% 35.44/4.99  ------ Resolution
% 35.44/4.99  
% 35.44/4.99  res_num_of_clauses:                     0
% 35.44/4.99  res_num_in_passive:                     0
% 35.44/4.99  res_num_in_active:                      0
% 35.44/4.99  res_num_of_loops:                       83
% 35.44/4.99  res_forward_subset_subsumed:            682
% 35.44/4.99  res_backward_subset_subsumed:           16
% 35.44/4.99  res_forward_subsumed:                   0
% 35.44/4.99  res_backward_subsumed:                  0
% 35.44/4.99  res_forward_subsumption_resolution:     0
% 35.44/4.99  res_backward_subsumption_resolution:    0
% 35.44/4.99  res_clause_to_clause_subsumption:       25874
% 35.44/4.99  res_orphan_elimination:                 0
% 35.44/4.99  res_tautology_del:                      976
% 35.44/4.99  res_num_eq_res_simplified:              0
% 35.44/4.99  res_num_sel_changes:                    0
% 35.44/4.99  res_moves_from_active_to_pass:          0
% 35.44/4.99  
% 35.44/4.99  ------ Superposition
% 35.44/4.99  
% 35.44/4.99  sup_time_total:                         0.
% 35.44/4.99  sup_time_generating:                    0.
% 35.44/4.99  sup_time_sim_full:                      0.
% 35.44/4.99  sup_time_sim_immed:                     0.
% 35.44/4.99  
% 35.44/4.99  sup_num_of_clauses:                     6757
% 35.44/4.99  sup_num_in_active:                      462
% 35.44/4.99  sup_num_in_passive:                     6295
% 35.44/4.99  sup_num_of_loops:                       469
% 35.44/4.99  sup_fw_superposition:                   17199
% 35.44/4.99  sup_bw_superposition:                   10903
% 35.44/4.99  sup_immediate_simplified:               10494
% 35.44/4.99  sup_given_eliminated:                   0
% 35.44/4.99  comparisons_done:                       0
% 35.44/4.99  comparisons_avoided:                    0
% 35.44/4.99  
% 35.44/4.99  ------ Simplifications
% 35.44/4.99  
% 35.44/4.99  
% 35.44/4.99  sim_fw_subset_subsumed:                 0
% 35.44/4.99  sim_bw_subset_subsumed:                 2
% 35.44/4.99  sim_fw_subsumed:                        1513
% 35.44/4.99  sim_bw_subsumed:                        261
% 35.44/4.99  sim_fw_subsumption_res:                 0
% 35.44/4.99  sim_bw_subsumption_res:                 0
% 35.44/4.99  sim_tautology_del:                      0
% 35.44/4.99  sim_eq_tautology_del:                   4016
% 35.44/4.99  sim_eq_res_simp:                        0
% 35.44/4.99  sim_fw_demodulated:                     6808
% 35.44/4.99  sim_bw_demodulated:                     23
% 35.44/4.99  sim_light_normalised:                   2973
% 35.44/4.99  sim_joinable_taut:                      0
% 35.44/4.99  sim_joinable_simp:                      0
% 35.44/4.99  sim_ac_normalised:                      0
% 35.44/4.99  sim_smt_subsumption:                    0
% 35.44/4.99  
%------------------------------------------------------------------------------
