%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:09:19 EST 2020

% Result     : Theorem 39.65s
% Output     : CNFRefutation 39.65s
% Verified   : 
% Statistics : Number of formulae       :  174 (7742 expanded)
%              Number of clauses        :  114 (2814 expanded)
%              Number of leaves         :   17 (1886 expanded)
%              Depth                    :   33
%              Number of atoms          :  339 (11460 expanded)
%              Number of equality atoms :  191 (7142 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(k10_relat_1(X0,X2),X1)
         => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_tarski(k10_relat_1(X0,X2),X1)
           => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
     => ( k10_relat_1(X0,sK2) != k10_relat_1(k7_relat_1(X0,sK1),sK2)
        & r1_tarski(k10_relat_1(X0,sK2),sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
            & r1_tarski(k10_relat_1(X0,X2),X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X2,X1] :
          ( k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2)
          & r1_tarski(k10_relat_1(sK0,X2),X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    & r1_tarski(k10_relat_1(sK0,sK2),sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f34,f38,f37])).

fof(f62,plain,(
    r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f70,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f41])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f64,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f46,f45])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(X2,X1))) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f55,f64])).

fof(f60,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f16,axiom,(
    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f68,plain,(
    ! [X0,X1] : k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(definition_unfolding,[],[f59,f64])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f9,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f54,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f50,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f40,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f65,plain,(
    ! [X0] : k1_setfam_1(k1_enumset1(X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f40,f64])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(X1,k1_relat_1(X1)))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f57,f64])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f49,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f43,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f61,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f63,plain,(
    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_19,negated_conjecture,
    ( r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_563,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_565,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k1_enumset1(X1,X1,k10_relat_1(X0,X2))) = k10_relat_1(k7_relat_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_21,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_342,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(X1,X2))) = k10_relat_1(k7_relat_1(X1,X0),X2)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_21])).

cnf(c_343,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(sK0,X1))) = k10_relat_1(k7_relat_1(sK0,X0),X1) ),
    inference(unflattening,[status(thm)],[c_342])).

cnf(c_17,plain,
    ( k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_12,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_315,plain,
    ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
    | k6_relat_1(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_12])).

cnf(c_316,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(unflattening,[status(thm)],[c_315])).

cnf(c_569,plain,
    ( k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(demodulation,[status(thm)],[c_17,c_316])).

cnf(c_2077,plain,
    ( k6_relat_1(k10_relat_1(k7_relat_1(sK0,X0),X1)) = k7_relat_1(k6_relat_1(X0),k10_relat_1(sK0,X1)) ),
    inference(superposition,[status(thm)],[c_343,c_569])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_336,plain,
    ( k6_relat_1(X0) != X1
    | k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2) ),
    inference(resolution_lifted,[status(thm)],[c_5,c_12])).

cnf(c_337,plain,
    ( k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1) ),
    inference(unflattening,[status(thm)],[c_336])).

cnf(c_2696,plain,
    ( k2_relat_1(k6_relat_1(k10_relat_1(k7_relat_1(sK0,X0),X1))) = k9_relat_1(k6_relat_1(X0),k10_relat_1(sK0,X1)) ),
    inference(superposition,[status(thm)],[c_2077,c_337])).

cnf(c_8,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2697,plain,
    ( k9_relat_1(k6_relat_1(X0),k10_relat_1(sK0,X1)) = k10_relat_1(k7_relat_1(sK0,X0),X1) ),
    inference(demodulation,[status(thm)],[c_2696,c_8])).

cnf(c_11,plain,
    ( v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_16,plain,
    ( r1_tarski(X0,k10_relat_1(X1,X2))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ r1_tarski(k9_relat_1(X1,X0),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_202,plain,
    ( r1_tarski(X0,k10_relat_1(X1,X2))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ r1_tarski(k9_relat_1(X1,X0),X2)
    | ~ v1_relat_1(X1)
    | k6_relat_1(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_16])).

cnf(c_203,plain,
    ( r1_tarski(X0,k10_relat_1(k6_relat_1(X1),X2))
    | ~ r1_tarski(X0,k1_relat_1(k6_relat_1(X1)))
    | ~ r1_tarski(k9_relat_1(k6_relat_1(X1),X0),X2)
    | ~ v1_relat_1(k6_relat_1(X1)) ),
    inference(unflattening,[status(thm)],[c_202])).

cnf(c_215,plain,
    ( r1_tarski(X0,k10_relat_1(k6_relat_1(X1),X2))
    | ~ r1_tarski(X0,k1_relat_1(k6_relat_1(X1)))
    | ~ r1_tarski(k9_relat_1(k6_relat_1(X1),X0),X2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_203,c_12])).

cnf(c_562,plain,
    ( r1_tarski(X0,k10_relat_1(k6_relat_1(X1),X2)) = iProver_top
    | r1_tarski(X0,k1_relat_1(k6_relat_1(X1))) != iProver_top
    | r1_tarski(k9_relat_1(k6_relat_1(X1),X0),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_215])).

cnf(c_9,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_571,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k10_relat_1(k6_relat_1(X1),X2)) = iProver_top
    | r1_tarski(k9_relat_1(k6_relat_1(X1),X0),X2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_562,c_9])).

cnf(c_3580,plain,
    ( r1_tarski(k10_relat_1(k7_relat_1(sK0,X0),X1),X2) != iProver_top
    | r1_tarski(k10_relat_1(sK0,X1),X0) != iProver_top
    | r1_tarski(k10_relat_1(sK0,X1),k10_relat_1(k6_relat_1(X0),X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2697,c_571])).

cnf(c_0,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2074,plain,
    ( k7_relat_1(k6_relat_1(X0),X0) = k6_relat_1(X0) ),
    inference(superposition,[status(thm)],[c_0,c_569])).

cnf(c_309,plain,
    ( k6_relat_1(X0) != X1
    | k1_setfam_1(k1_enumset1(X2,X2,k10_relat_1(X1,X3))) = k10_relat_1(k7_relat_1(X1,X2),X3) ),
    inference(resolution_lifted,[status(thm)],[c_13,c_12])).

cnf(c_310,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(k6_relat_1(X1),X2))) = k10_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2) ),
    inference(unflattening,[status(thm)],[c_309])).

cnf(c_2086,plain,
    ( k10_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))),X2),X3) = k1_setfam_1(k1_enumset1(X2,X2,k10_relat_1(k7_relat_1(k6_relat_1(X0),X1),X3))) ),
    inference(superposition,[status(thm)],[c_569,c_310])).

cnf(c_2083,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(superposition,[status(thm)],[c_569,c_8])).

cnf(c_2089,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k9_relat_1(k6_relat_1(X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_2083,c_337])).

cnf(c_2091,plain,
    ( k6_relat_1(k9_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(demodulation,[status(thm)],[c_2089,c_569])).

cnf(c_2255,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3))) = k10_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0),X3) ),
    inference(light_normalisation,[status(thm)],[c_2086,c_2089,c_2091])).

cnf(c_6957,plain,
    ( k10_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k10_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)),X2) = k10_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) ),
    inference(superposition,[status(thm)],[c_2255,c_0])).

cnf(c_7164,plain,
    ( k10_relat_1(k7_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)),X1) = k10_relat_1(k7_relat_1(k6_relat_1(X0),X0),X1) ),
    inference(superposition,[status(thm)],[c_2074,c_6957])).

cnf(c_15,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_setfam_1(k1_enumset1(X1,X1,k9_relat_1(X0,k1_relat_1(X0)))) = k9_relat_1(X0,k10_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_222,plain,
    ( ~ v1_relat_1(X0)
    | k6_relat_1(X1) != X0
    | k1_setfam_1(k1_enumset1(X2,X2,k9_relat_1(X0,k1_relat_1(X0)))) = k9_relat_1(X0,k10_relat_1(X0,X2)) ),
    inference(resolution_lifted,[status(thm)],[c_11,c_15])).

cnf(c_223,plain,
    ( ~ v1_relat_1(k6_relat_1(X0))
    | k1_setfam_1(k1_enumset1(X1,X1,k9_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0))))) = k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) ),
    inference(unflattening,[status(thm)],[c_222])).

cnf(c_227,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,k9_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0))))) = k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_223,c_12])).

cnf(c_228,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(k6_relat_1(X1),k1_relat_1(k6_relat_1(X1))))) = k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X0)) ),
    inference(renaming,[status(thm)],[c_227])).

cnf(c_570,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(k6_relat_1(X1),X1))) = k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X0)) ),
    inference(demodulation,[status(thm)],[c_228,c_9])).

cnf(c_2966,plain,
    ( k9_relat_1(k6_relat_1(X0),X0) = k2_relat_1(k6_relat_1(X0)) ),
    inference(superposition,[status(thm)],[c_2074,c_337])).

cnf(c_2973,plain,
    ( k9_relat_1(k6_relat_1(X0),X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2966,c_8])).

cnf(c_3434,plain,
    ( k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X1),X0) ),
    inference(demodulation,[status(thm)],[c_570,c_2089,c_2973])).

cnf(c_4610,plain,
    ( k7_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = k6_relat_1(k9_relat_1(k6_relat_1(X1),X0)) ),
    inference(superposition,[status(thm)],[c_3434,c_2091])).

cnf(c_4644,plain,
    ( k7_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(demodulation,[status(thm)],[c_4610,c_2091])).

cnf(c_7176,plain,
    ( k10_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) = k10_relat_1(k6_relat_1(X1),X0) ),
    inference(light_normalisation,[status(thm)],[c_7164,c_2074,c_4644])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_321,plain,
    ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
    | k6_relat_1(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_12])).

cnf(c_322,plain,
    ( k10_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X0))) = k1_relat_1(k6_relat_1(X0)) ),
    inference(unflattening,[status(thm)],[c_321])).

cnf(c_568,plain,
    ( k10_relat_1(k6_relat_1(X0),X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_322,c_8,c_9])).

cnf(c_1918,plain,
    ( k10_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) = k1_setfam_1(k1_enumset1(X1,X1,X0)) ),
    inference(superposition,[status(thm)],[c_568,c_310])).

cnf(c_4374,plain,
    ( k10_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) = k9_relat_1(k6_relat_1(X1),X0) ),
    inference(demodulation,[status(thm)],[c_1918,c_2089])).

cnf(c_7177,plain,
    ( k10_relat_1(k6_relat_1(X0),X1) = k9_relat_1(k6_relat_1(X0),X1) ),
    inference(demodulation,[status(thm)],[c_7176,c_4374])).

cnf(c_67638,plain,
    ( r1_tarski(k10_relat_1(k7_relat_1(sK0,X0),X1),X2) != iProver_top
    | r1_tarski(k10_relat_1(sK0,X1),X0) != iProver_top
    | r1_tarski(k10_relat_1(sK0,X1),k9_relat_1(k6_relat_1(X0),X2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3580,c_7177])).

cnf(c_6,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_327,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0))
    | k6_relat_1(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_12])).

cnf(c_328,plain,
    ( r1_tarski(k10_relat_1(k6_relat_1(X0),X1),k1_relat_1(k6_relat_1(X0))) ),
    inference(unflattening,[status(thm)],[c_327])).

cnf(c_558,plain,
    ( r1_tarski(k10_relat_1(k6_relat_1(X0),X1),k1_relat_1(k6_relat_1(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_328])).

cnf(c_567,plain,
    ( r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_558,c_9])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_566,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3445,plain,
    ( k10_relat_1(k6_relat_1(X0),X1) = X0
    | r1_tarski(X0,k10_relat_1(k6_relat_1(X0),X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_567,c_566])).

cnf(c_8884,plain,
    ( k10_relat_1(k6_relat_1(X0),X1) = X0
    | r1_tarski(X0,k9_relat_1(k6_relat_1(X0),X1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3445,c_7177])).

cnf(c_8885,plain,
    ( k9_relat_1(k6_relat_1(X0),X1) = X0
    | r1_tarski(X0,k9_relat_1(k6_relat_1(X0),X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8884,c_7177])).

cnf(c_67671,plain,
    ( k9_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),X1) = k10_relat_1(sK0,X0)
    | r1_tarski(k10_relat_1(k7_relat_1(sK0,k10_relat_1(sK0,X0)),X0),X1) != iProver_top
    | r1_tarski(k10_relat_1(sK0,X0),k10_relat_1(sK0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_67638,c_8885])).

cnf(c_1194,plain,
    ( k10_relat_1(k7_relat_1(sK0,k10_relat_1(sK0,X0)),X0) = k10_relat_1(sK0,X0) ),
    inference(superposition,[status(thm)],[c_0,c_343])).

cnf(c_67674,plain,
    ( k9_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),X1) = k10_relat_1(sK0,X0)
    | r1_tarski(k10_relat_1(sK0,X0),X1) != iProver_top
    | r1_tarski(k10_relat_1(sK0,X0),k10_relat_1(sK0,X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_67671,c_1194])).

cnf(c_71442,plain,
    ( k9_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),X1) = k10_relat_1(sK0,X0)
    | r1_tarski(k10_relat_1(sK0,X0),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_565,c_67674])).

cnf(c_72464,plain,
    ( k9_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1) = k10_relat_1(sK0,sK2) ),
    inference(superposition,[status(thm)],[c_563,c_71442])).

cnf(c_4378,plain,
    ( k10_relat_1(k6_relat_1(k10_relat_1(k7_relat_1(sK0,X0),X1)),X0) = k9_relat_1(k6_relat_1(k10_relat_1(sK0,X1)),X0) ),
    inference(superposition,[status(thm)],[c_2077,c_4374])).

cnf(c_4814,plain,
    ( r1_tarski(k9_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),X1),k10_relat_1(k7_relat_1(sK0,X1),X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4378,c_567])).

cnf(c_73730,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k7_relat_1(sK0,sK1),sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_72464,c_4814])).

cnf(c_359,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_21])).

cnf(c_360,plain,
    ( r1_tarski(k10_relat_1(sK0,X0),k1_relat_1(sK0)) ),
    inference(unflattening,[status(thm)],[c_359])).

cnf(c_557,plain,
    ( r1_tarski(k10_relat_1(sK0,X0),k1_relat_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_360])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_248,plain,
    ( r1_tarski(X0,k10_relat_1(X1,X2))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ r1_tarski(k9_relat_1(X1,X0),X2)
    | ~ v1_relat_1(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_20])).

cnf(c_249,plain,
    ( r1_tarski(X0,k10_relat_1(sK0,X1))
    | ~ r1_tarski(X0,k1_relat_1(sK0))
    | ~ r1_tarski(k9_relat_1(sK0,X0),X1)
    | ~ v1_relat_1(sK0) ),
    inference(unflattening,[status(thm)],[c_248])).

cnf(c_253,plain,
    ( ~ r1_tarski(k9_relat_1(sK0,X0),X1)
    | ~ r1_tarski(X0,k1_relat_1(sK0))
    | r1_tarski(X0,k10_relat_1(sK0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_249,c_21])).

cnf(c_254,plain,
    ( r1_tarski(X0,k10_relat_1(sK0,X1))
    | ~ r1_tarski(X0,k1_relat_1(sK0))
    | ~ r1_tarski(k9_relat_1(sK0,X0),X1) ),
    inference(renaming,[status(thm)],[c_253])).

cnf(c_560,plain,
    ( r1_tarski(X0,k10_relat_1(sK0,X1)) = iProver_top
    | r1_tarski(X0,k1_relat_1(sK0)) != iProver_top
    | r1_tarski(k9_relat_1(sK0,X0),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_254])).

cnf(c_1790,plain,
    ( r1_tarski(X0,k10_relat_1(sK0,k9_relat_1(sK0,X0))) = iProver_top
    | r1_tarski(X0,k1_relat_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_565,c_560])).

cnf(c_3576,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k10_relat_1(k6_relat_1(X1),k10_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(k6_relat_1(X1),X0))))) = iProver_top
    | r1_tarski(k9_relat_1(k6_relat_1(X1),X0),k1_relat_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1790,c_571])).

cnf(c_55584,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k9_relat_1(k6_relat_1(X1),k10_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(k6_relat_1(X1),X0))))) = iProver_top
    | r1_tarski(k9_relat_1(k6_relat_1(X1),X0),k1_relat_1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3576,c_7177])).

cnf(c_55585,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k10_relat_1(k7_relat_1(sK0,X1),k9_relat_1(sK0,k9_relat_1(k6_relat_1(X1),X0)))) = iProver_top
    | r1_tarski(k9_relat_1(k6_relat_1(X1),X0),k1_relat_1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_55584,c_2697])).

cnf(c_8895,plain,
    ( k9_relat_1(k6_relat_1(X0),k10_relat_1(sK0,X1)) = X0
    | r1_tarski(X0,k10_relat_1(k7_relat_1(sK0,X0),X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2697,c_8885])).

cnf(c_8900,plain,
    ( k10_relat_1(k7_relat_1(sK0,X0),X1) = X0
    | r1_tarski(X0,k10_relat_1(k7_relat_1(sK0,X0),X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8895,c_2697])).

cnf(c_55624,plain,
    ( k10_relat_1(k7_relat_1(sK0,X0),k9_relat_1(sK0,k9_relat_1(k6_relat_1(X0),X0))) = X0
    | r1_tarski(X0,X0) != iProver_top
    | r1_tarski(k9_relat_1(k6_relat_1(X0),X0),k1_relat_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_55585,c_8900])).

cnf(c_55628,plain,
    ( k10_relat_1(k7_relat_1(sK0,X0),k9_relat_1(sK0,X0)) = X0
    | r1_tarski(X0,X0) != iProver_top
    | r1_tarski(X0,k1_relat_1(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_55624,c_2973])).

cnf(c_59,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_60011,plain,
    ( k10_relat_1(k7_relat_1(sK0,X0),k9_relat_1(sK0,X0)) = X0
    | r1_tarski(X0,k1_relat_1(sK0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_55628,c_59])).

cnf(c_60019,plain,
    ( k10_relat_1(k7_relat_1(sK0,k10_relat_1(sK0,X0)),k9_relat_1(sK0,k10_relat_1(sK0,X0))) = k10_relat_1(sK0,X0) ),
    inference(superposition,[status(thm)],[c_557,c_60011])).

cnf(c_62307,plain,
    ( k9_relat_1(k6_relat_1(k10_relat_1(sK0,k9_relat_1(sK0,k10_relat_1(sK0,X0)))),k10_relat_1(sK0,X0)) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),k10_relat_1(sK0,X0)) ),
    inference(superposition,[status(thm)],[c_60019,c_4378])).

cnf(c_62327,plain,
    ( k9_relat_1(k6_relat_1(k10_relat_1(sK0,k9_relat_1(sK0,k10_relat_1(sK0,X0)))),k10_relat_1(sK0,X0)) = k10_relat_1(sK0,X0) ),
    inference(demodulation,[status(thm)],[c_62307,c_568,c_2697])).

cnf(c_64606,plain,
    ( k10_relat_1(k7_relat_1(sK0,k10_relat_1(sK0,k9_relat_1(sK0,k10_relat_1(sK0,X0)))),X0) = k10_relat_1(sK0,X0) ),
    inference(superposition,[status(thm)],[c_62327,c_2697])).

cnf(c_64796,plain,
    ( k10_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),k10_relat_1(sK0,k9_relat_1(sK0,k10_relat_1(sK0,X0)))) = k9_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),k10_relat_1(sK0,k9_relat_1(sK0,k10_relat_1(sK0,X0)))) ),
    inference(superposition,[status(thm)],[c_64606,c_4378])).

cnf(c_64822,plain,
    ( k10_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),k10_relat_1(sK0,k9_relat_1(sK0,k10_relat_1(sK0,X0)))) = k10_relat_1(sK0,X0) ),
    inference(demodulation,[status(thm)],[c_64796,c_2697,c_7177,c_60019])).

cnf(c_64829,plain,
    ( k10_relat_1(k7_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),X1),k10_relat_1(sK0,k9_relat_1(sK0,k10_relat_1(sK0,X0)))) = k1_setfam_1(k1_enumset1(X1,X1,k10_relat_1(sK0,X0))) ),
    inference(superposition,[status(thm)],[c_64822,c_310])).

cnf(c_64835,plain,
    ( k10_relat_1(k7_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),X1),k10_relat_1(sK0,k9_relat_1(sK0,k10_relat_1(sK0,X0)))) = k10_relat_1(k7_relat_1(sK0,X1),X0) ),
    inference(demodulation,[status(thm)],[c_64829,c_343])).

cnf(c_2079,plain,
    ( r1_tarski(k10_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),k1_setfam_1(k1_enumset1(X0,X0,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_569,c_567])).

cnf(c_2262,plain,
    ( r1_tarski(k10_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),k9_relat_1(k6_relat_1(X0),X1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2079,c_2089])).

cnf(c_65147,plain,
    ( r1_tarski(k10_relat_1(k7_relat_1(sK0,X0),X1),k9_relat_1(k6_relat_1(k10_relat_1(sK0,X1)),X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_64835,c_2262])).

cnf(c_73725,plain,
    ( r1_tarski(k10_relat_1(k7_relat_1(sK0,sK1),sK2),k10_relat_1(sK0,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_72464,c_65147])).

cnf(c_593,plain,
    ( ~ r1_tarski(k10_relat_1(k7_relat_1(sK0,sK1),sK2),k10_relat_1(sK0,sK2))
    | ~ r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k7_relat_1(sK0,sK1),sK2))
    | k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_594,plain,
    ( k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    | r1_tarski(k10_relat_1(k7_relat_1(sK0,sK1),sK2),k10_relat_1(sK0,sK2)) != iProver_top
    | r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k7_relat_1(sK0,sK1),sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_593])).

cnf(c_18,negated_conjecture,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f63])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_73730,c_73725,c_594,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:28:01 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 39.65/5.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 39.65/5.50  
% 39.65/5.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 39.65/5.50  
% 39.65/5.50  ------  iProver source info
% 39.65/5.50  
% 39.65/5.50  git: date: 2020-06-30 10:37:57 +0100
% 39.65/5.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 39.65/5.50  git: non_committed_changes: false
% 39.65/5.50  git: last_make_outside_of_git: false
% 39.65/5.50  
% 39.65/5.50  ------ 
% 39.65/5.50  
% 39.65/5.50  ------ Input Options
% 39.65/5.50  
% 39.65/5.50  --out_options                           all
% 39.65/5.50  --tptp_safe_out                         true
% 39.65/5.50  --problem_path                          ""
% 39.65/5.50  --include_path                          ""
% 39.65/5.50  --clausifier                            res/vclausify_rel
% 39.65/5.50  --clausifier_options                    ""
% 39.65/5.50  --stdin                                 false
% 39.65/5.50  --stats_out                             all
% 39.65/5.50  
% 39.65/5.50  ------ General Options
% 39.65/5.50  
% 39.65/5.50  --fof                                   false
% 39.65/5.50  --time_out_real                         305.
% 39.65/5.50  --time_out_virtual                      -1.
% 39.65/5.50  --symbol_type_check                     false
% 39.65/5.50  --clausify_out                          false
% 39.65/5.50  --sig_cnt_out                           false
% 39.65/5.50  --trig_cnt_out                          false
% 39.65/5.50  --trig_cnt_out_tolerance                1.
% 39.65/5.50  --trig_cnt_out_sk_spl                   false
% 39.65/5.50  --abstr_cl_out                          false
% 39.65/5.50  
% 39.65/5.50  ------ Global Options
% 39.65/5.50  
% 39.65/5.50  --schedule                              default
% 39.65/5.50  --add_important_lit                     false
% 39.65/5.50  --prop_solver_per_cl                    1000
% 39.65/5.50  --min_unsat_core                        false
% 39.65/5.50  --soft_assumptions                      false
% 39.65/5.50  --soft_lemma_size                       3
% 39.65/5.50  --prop_impl_unit_size                   0
% 39.65/5.50  --prop_impl_unit                        []
% 39.65/5.50  --share_sel_clauses                     true
% 39.65/5.50  --reset_solvers                         false
% 39.65/5.50  --bc_imp_inh                            [conj_cone]
% 39.65/5.50  --conj_cone_tolerance                   3.
% 39.65/5.50  --extra_neg_conj                        none
% 39.65/5.50  --large_theory_mode                     true
% 39.65/5.50  --prolific_symb_bound                   200
% 39.65/5.50  --lt_threshold                          2000
% 39.65/5.50  --clause_weak_htbl                      true
% 39.65/5.50  --gc_record_bc_elim                     false
% 39.65/5.50  
% 39.65/5.50  ------ Preprocessing Options
% 39.65/5.50  
% 39.65/5.50  --preprocessing_flag                    true
% 39.65/5.50  --time_out_prep_mult                    0.1
% 39.65/5.50  --splitting_mode                        input
% 39.65/5.50  --splitting_grd                         true
% 39.65/5.50  --splitting_cvd                         false
% 39.65/5.50  --splitting_cvd_svl                     false
% 39.65/5.50  --splitting_nvd                         32
% 39.65/5.50  --sub_typing                            true
% 39.65/5.50  --prep_gs_sim                           true
% 39.65/5.50  --prep_unflatten                        true
% 39.65/5.50  --prep_res_sim                          true
% 39.65/5.50  --prep_upred                            true
% 39.65/5.50  --prep_sem_filter                       exhaustive
% 39.65/5.50  --prep_sem_filter_out                   false
% 39.65/5.50  --pred_elim                             true
% 39.65/5.50  --res_sim_input                         true
% 39.65/5.50  --eq_ax_congr_red                       true
% 39.65/5.50  --pure_diseq_elim                       true
% 39.65/5.50  --brand_transform                       false
% 39.65/5.50  --non_eq_to_eq                          false
% 39.65/5.50  --prep_def_merge                        true
% 39.65/5.50  --prep_def_merge_prop_impl              false
% 39.65/5.50  --prep_def_merge_mbd                    true
% 39.65/5.50  --prep_def_merge_tr_red                 false
% 39.65/5.50  --prep_def_merge_tr_cl                  false
% 39.65/5.50  --smt_preprocessing                     true
% 39.65/5.50  --smt_ac_axioms                         fast
% 39.65/5.50  --preprocessed_out                      false
% 39.65/5.50  --preprocessed_stats                    false
% 39.65/5.50  
% 39.65/5.50  ------ Abstraction refinement Options
% 39.65/5.50  
% 39.65/5.50  --abstr_ref                             []
% 39.65/5.50  --abstr_ref_prep                        false
% 39.65/5.50  --abstr_ref_until_sat                   false
% 39.65/5.50  --abstr_ref_sig_restrict                funpre
% 39.65/5.50  --abstr_ref_af_restrict_to_split_sk     false
% 39.65/5.50  --abstr_ref_under                       []
% 39.65/5.50  
% 39.65/5.50  ------ SAT Options
% 39.65/5.50  
% 39.65/5.50  --sat_mode                              false
% 39.65/5.50  --sat_fm_restart_options                ""
% 39.65/5.50  --sat_gr_def                            false
% 39.65/5.50  --sat_epr_types                         true
% 39.65/5.50  --sat_non_cyclic_types                  false
% 39.65/5.50  --sat_finite_models                     false
% 39.65/5.50  --sat_fm_lemmas                         false
% 39.65/5.50  --sat_fm_prep                           false
% 39.65/5.50  --sat_fm_uc_incr                        true
% 39.65/5.50  --sat_out_model                         small
% 39.65/5.50  --sat_out_clauses                       false
% 39.65/5.50  
% 39.65/5.50  ------ QBF Options
% 39.65/5.50  
% 39.65/5.50  --qbf_mode                              false
% 39.65/5.50  --qbf_elim_univ                         false
% 39.65/5.50  --qbf_dom_inst                          none
% 39.65/5.50  --qbf_dom_pre_inst                      false
% 39.65/5.50  --qbf_sk_in                             false
% 39.65/5.50  --qbf_pred_elim                         true
% 39.65/5.50  --qbf_split                             512
% 39.65/5.50  
% 39.65/5.50  ------ BMC1 Options
% 39.65/5.50  
% 39.65/5.50  --bmc1_incremental                      false
% 39.65/5.50  --bmc1_axioms                           reachable_all
% 39.65/5.50  --bmc1_min_bound                        0
% 39.65/5.50  --bmc1_max_bound                        -1
% 39.65/5.50  --bmc1_max_bound_default                -1
% 39.65/5.50  --bmc1_symbol_reachability              true
% 39.65/5.50  --bmc1_property_lemmas                  false
% 39.65/5.50  --bmc1_k_induction                      false
% 39.65/5.50  --bmc1_non_equiv_states                 false
% 39.65/5.50  --bmc1_deadlock                         false
% 39.65/5.50  --bmc1_ucm                              false
% 39.65/5.50  --bmc1_add_unsat_core                   none
% 39.65/5.50  --bmc1_unsat_core_children              false
% 39.65/5.50  --bmc1_unsat_core_extrapolate_axioms    false
% 39.65/5.50  --bmc1_out_stat                         full
% 39.65/5.50  --bmc1_ground_init                      false
% 39.65/5.50  --bmc1_pre_inst_next_state              false
% 39.65/5.50  --bmc1_pre_inst_state                   false
% 39.65/5.50  --bmc1_pre_inst_reach_state             false
% 39.65/5.50  --bmc1_out_unsat_core                   false
% 39.65/5.50  --bmc1_aig_witness_out                  false
% 39.65/5.50  --bmc1_verbose                          false
% 39.65/5.50  --bmc1_dump_clauses_tptp                false
% 39.65/5.50  --bmc1_dump_unsat_core_tptp             false
% 39.65/5.50  --bmc1_dump_file                        -
% 39.65/5.50  --bmc1_ucm_expand_uc_limit              128
% 39.65/5.50  --bmc1_ucm_n_expand_iterations          6
% 39.65/5.50  --bmc1_ucm_extend_mode                  1
% 39.65/5.50  --bmc1_ucm_init_mode                    2
% 39.65/5.50  --bmc1_ucm_cone_mode                    none
% 39.65/5.50  --bmc1_ucm_reduced_relation_type        0
% 39.65/5.50  --bmc1_ucm_relax_model                  4
% 39.65/5.50  --bmc1_ucm_full_tr_after_sat            true
% 39.65/5.50  --bmc1_ucm_expand_neg_assumptions       false
% 39.65/5.50  --bmc1_ucm_layered_model                none
% 39.65/5.50  --bmc1_ucm_max_lemma_size               10
% 39.65/5.50  
% 39.65/5.50  ------ AIG Options
% 39.65/5.50  
% 39.65/5.50  --aig_mode                              false
% 39.65/5.50  
% 39.65/5.50  ------ Instantiation Options
% 39.65/5.50  
% 39.65/5.50  --instantiation_flag                    true
% 39.65/5.50  --inst_sos_flag                         true
% 39.65/5.50  --inst_sos_phase                        true
% 39.65/5.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 39.65/5.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 39.65/5.50  --inst_lit_sel_side                     num_symb
% 39.65/5.50  --inst_solver_per_active                1400
% 39.65/5.50  --inst_solver_calls_frac                1.
% 39.65/5.50  --inst_passive_queue_type               priority_queues
% 39.65/5.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 39.65/5.50  --inst_passive_queues_freq              [25;2]
% 39.65/5.50  --inst_dismatching                      true
% 39.65/5.50  --inst_eager_unprocessed_to_passive     true
% 39.65/5.50  --inst_prop_sim_given                   true
% 39.65/5.50  --inst_prop_sim_new                     false
% 39.65/5.50  --inst_subs_new                         false
% 39.65/5.50  --inst_eq_res_simp                      false
% 39.65/5.50  --inst_subs_given                       false
% 39.65/5.50  --inst_orphan_elimination               true
% 39.65/5.50  --inst_learning_loop_flag               true
% 39.65/5.50  --inst_learning_start                   3000
% 39.65/5.50  --inst_learning_factor                  2
% 39.65/5.50  --inst_start_prop_sim_after_learn       3
% 39.65/5.50  --inst_sel_renew                        solver
% 39.65/5.50  --inst_lit_activity_flag                true
% 39.65/5.50  --inst_restr_to_given                   false
% 39.65/5.50  --inst_activity_threshold               500
% 39.65/5.50  --inst_out_proof                        true
% 39.65/5.50  
% 39.65/5.50  ------ Resolution Options
% 39.65/5.50  
% 39.65/5.50  --resolution_flag                       true
% 39.65/5.50  --res_lit_sel                           adaptive
% 39.65/5.50  --res_lit_sel_side                      none
% 39.65/5.50  --res_ordering                          kbo
% 39.65/5.50  --res_to_prop_solver                    active
% 39.65/5.50  --res_prop_simpl_new                    false
% 39.65/5.50  --res_prop_simpl_given                  true
% 39.65/5.50  --res_passive_queue_type                priority_queues
% 39.65/5.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 39.65/5.50  --res_passive_queues_freq               [15;5]
% 39.65/5.50  --res_forward_subs                      full
% 39.65/5.50  --res_backward_subs                     full
% 39.65/5.50  --res_forward_subs_resolution           true
% 39.65/5.50  --res_backward_subs_resolution          true
% 39.65/5.50  --res_orphan_elimination                true
% 39.65/5.50  --res_time_limit                        2.
% 39.65/5.50  --res_out_proof                         true
% 39.65/5.50  
% 39.65/5.50  ------ Superposition Options
% 39.65/5.50  
% 39.65/5.50  --superposition_flag                    true
% 39.65/5.50  --sup_passive_queue_type                priority_queues
% 39.65/5.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 39.65/5.50  --sup_passive_queues_freq               [8;1;4]
% 39.65/5.50  --demod_completeness_check              fast
% 39.65/5.50  --demod_use_ground                      true
% 39.65/5.50  --sup_to_prop_solver                    passive
% 39.65/5.50  --sup_prop_simpl_new                    true
% 39.65/5.50  --sup_prop_simpl_given                  true
% 39.65/5.50  --sup_fun_splitting                     true
% 39.65/5.50  --sup_smt_interval                      50000
% 39.65/5.50  
% 39.65/5.50  ------ Superposition Simplification Setup
% 39.65/5.50  
% 39.65/5.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 39.65/5.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 39.65/5.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 39.65/5.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 39.65/5.50  --sup_full_triv                         [TrivRules;PropSubs]
% 39.65/5.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 39.65/5.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 39.65/5.50  --sup_immed_triv                        [TrivRules]
% 39.65/5.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 39.65/5.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 39.65/5.50  --sup_immed_bw_main                     []
% 39.65/5.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 39.65/5.50  --sup_input_triv                        [Unflattening;TrivRules]
% 39.65/5.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 39.65/5.50  --sup_input_bw                          []
% 39.65/5.50  
% 39.65/5.50  ------ Combination Options
% 39.65/5.50  
% 39.65/5.50  --comb_res_mult                         3
% 39.65/5.50  --comb_sup_mult                         2
% 39.65/5.50  --comb_inst_mult                        10
% 39.65/5.50  
% 39.65/5.50  ------ Debug Options
% 39.65/5.50  
% 39.65/5.50  --dbg_backtrace                         false
% 39.65/5.50  --dbg_dump_prop_clauses                 false
% 39.65/5.50  --dbg_dump_prop_clauses_file            -
% 39.65/5.50  --dbg_out_stat                          false
% 39.65/5.50  ------ Parsing...
% 39.65/5.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 39.65/5.50  
% 39.65/5.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 39.65/5.50  
% 39.65/5.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 39.65/5.50  
% 39.65/5.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.65/5.50  ------ Proving...
% 39.65/5.50  ------ Problem Properties 
% 39.65/5.50  
% 39.65/5.50  
% 39.65/5.50  clauses                                 25
% 39.65/5.50  conjectures                             2
% 39.65/5.50  EPR                                     3
% 39.65/5.50  Horn                                    25
% 39.65/5.50  unary                                   21
% 39.65/5.50  binary                                  0
% 39.65/5.50  lits                                    33
% 39.65/5.50  lits eq                                 16
% 39.65/5.50  fd_pure                                 0
% 39.65/5.50  fd_pseudo                               0
% 39.65/5.50  fd_cond                                 0
% 39.65/5.50  fd_pseudo_cond                          1
% 39.65/5.50  AC symbols                              0
% 39.65/5.50  
% 39.65/5.50  ------ Schedule dynamic 5 is on 
% 39.65/5.50  
% 39.65/5.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 39.65/5.50  
% 39.65/5.50  
% 39.65/5.50  ------ 
% 39.65/5.50  Current options:
% 39.65/5.50  ------ 
% 39.65/5.50  
% 39.65/5.50  ------ Input Options
% 39.65/5.50  
% 39.65/5.50  --out_options                           all
% 39.65/5.50  --tptp_safe_out                         true
% 39.65/5.50  --problem_path                          ""
% 39.65/5.50  --include_path                          ""
% 39.65/5.50  --clausifier                            res/vclausify_rel
% 39.65/5.50  --clausifier_options                    ""
% 39.65/5.50  --stdin                                 false
% 39.65/5.50  --stats_out                             all
% 39.65/5.50  
% 39.65/5.50  ------ General Options
% 39.65/5.50  
% 39.65/5.50  --fof                                   false
% 39.65/5.50  --time_out_real                         305.
% 39.65/5.50  --time_out_virtual                      -1.
% 39.65/5.50  --symbol_type_check                     false
% 39.65/5.50  --clausify_out                          false
% 39.65/5.50  --sig_cnt_out                           false
% 39.65/5.50  --trig_cnt_out                          false
% 39.65/5.50  --trig_cnt_out_tolerance                1.
% 39.65/5.50  --trig_cnt_out_sk_spl                   false
% 39.65/5.50  --abstr_cl_out                          false
% 39.65/5.50  
% 39.65/5.50  ------ Global Options
% 39.65/5.50  
% 39.65/5.50  --schedule                              default
% 39.65/5.50  --add_important_lit                     false
% 39.65/5.50  --prop_solver_per_cl                    1000
% 39.65/5.50  --min_unsat_core                        false
% 39.65/5.50  --soft_assumptions                      false
% 39.65/5.50  --soft_lemma_size                       3
% 39.65/5.50  --prop_impl_unit_size                   0
% 39.65/5.50  --prop_impl_unit                        []
% 39.65/5.50  --share_sel_clauses                     true
% 39.65/5.50  --reset_solvers                         false
% 39.65/5.50  --bc_imp_inh                            [conj_cone]
% 39.65/5.50  --conj_cone_tolerance                   3.
% 39.65/5.50  --extra_neg_conj                        none
% 39.65/5.50  --large_theory_mode                     true
% 39.65/5.50  --prolific_symb_bound                   200
% 39.65/5.50  --lt_threshold                          2000
% 39.65/5.50  --clause_weak_htbl                      true
% 39.65/5.50  --gc_record_bc_elim                     false
% 39.65/5.50  
% 39.65/5.50  ------ Preprocessing Options
% 39.65/5.50  
% 39.65/5.50  --preprocessing_flag                    true
% 39.65/5.50  --time_out_prep_mult                    0.1
% 39.65/5.50  --splitting_mode                        input
% 39.65/5.50  --splitting_grd                         true
% 39.65/5.50  --splitting_cvd                         false
% 39.65/5.50  --splitting_cvd_svl                     false
% 39.65/5.50  --splitting_nvd                         32
% 39.65/5.50  --sub_typing                            true
% 39.65/5.50  --prep_gs_sim                           true
% 39.65/5.50  --prep_unflatten                        true
% 39.65/5.50  --prep_res_sim                          true
% 39.65/5.50  --prep_upred                            true
% 39.65/5.50  --prep_sem_filter                       exhaustive
% 39.65/5.50  --prep_sem_filter_out                   false
% 39.65/5.50  --pred_elim                             true
% 39.65/5.50  --res_sim_input                         true
% 39.65/5.50  --eq_ax_congr_red                       true
% 39.65/5.50  --pure_diseq_elim                       true
% 39.65/5.50  --brand_transform                       false
% 39.65/5.50  --non_eq_to_eq                          false
% 39.65/5.50  --prep_def_merge                        true
% 39.65/5.50  --prep_def_merge_prop_impl              false
% 39.65/5.50  --prep_def_merge_mbd                    true
% 39.65/5.50  --prep_def_merge_tr_red                 false
% 39.65/5.50  --prep_def_merge_tr_cl                  false
% 39.65/5.50  --smt_preprocessing                     true
% 39.65/5.50  --smt_ac_axioms                         fast
% 39.65/5.50  --preprocessed_out                      false
% 39.65/5.50  --preprocessed_stats                    false
% 39.65/5.50  
% 39.65/5.50  ------ Abstraction refinement Options
% 39.65/5.50  
% 39.65/5.50  --abstr_ref                             []
% 39.65/5.50  --abstr_ref_prep                        false
% 39.65/5.50  --abstr_ref_until_sat                   false
% 39.65/5.50  --abstr_ref_sig_restrict                funpre
% 39.65/5.50  --abstr_ref_af_restrict_to_split_sk     false
% 39.65/5.50  --abstr_ref_under                       []
% 39.65/5.50  
% 39.65/5.50  ------ SAT Options
% 39.65/5.50  
% 39.65/5.50  --sat_mode                              false
% 39.65/5.50  --sat_fm_restart_options                ""
% 39.65/5.50  --sat_gr_def                            false
% 39.65/5.50  --sat_epr_types                         true
% 39.65/5.50  --sat_non_cyclic_types                  false
% 39.65/5.50  --sat_finite_models                     false
% 39.65/5.50  --sat_fm_lemmas                         false
% 39.65/5.50  --sat_fm_prep                           false
% 39.65/5.50  --sat_fm_uc_incr                        true
% 39.65/5.50  --sat_out_model                         small
% 39.65/5.50  --sat_out_clauses                       false
% 39.65/5.50  
% 39.65/5.50  ------ QBF Options
% 39.65/5.50  
% 39.65/5.50  --qbf_mode                              false
% 39.65/5.50  --qbf_elim_univ                         false
% 39.65/5.50  --qbf_dom_inst                          none
% 39.65/5.50  --qbf_dom_pre_inst                      false
% 39.65/5.50  --qbf_sk_in                             false
% 39.65/5.50  --qbf_pred_elim                         true
% 39.65/5.50  --qbf_split                             512
% 39.65/5.50  
% 39.65/5.50  ------ BMC1 Options
% 39.65/5.50  
% 39.65/5.50  --bmc1_incremental                      false
% 39.65/5.50  --bmc1_axioms                           reachable_all
% 39.65/5.50  --bmc1_min_bound                        0
% 39.65/5.50  --bmc1_max_bound                        -1
% 39.65/5.50  --bmc1_max_bound_default                -1
% 39.65/5.50  --bmc1_symbol_reachability              true
% 39.65/5.50  --bmc1_property_lemmas                  false
% 39.65/5.50  --bmc1_k_induction                      false
% 39.65/5.50  --bmc1_non_equiv_states                 false
% 39.65/5.50  --bmc1_deadlock                         false
% 39.65/5.50  --bmc1_ucm                              false
% 39.65/5.50  --bmc1_add_unsat_core                   none
% 39.65/5.50  --bmc1_unsat_core_children              false
% 39.65/5.50  --bmc1_unsat_core_extrapolate_axioms    false
% 39.65/5.50  --bmc1_out_stat                         full
% 39.65/5.50  --bmc1_ground_init                      false
% 39.65/5.50  --bmc1_pre_inst_next_state              false
% 39.65/5.50  --bmc1_pre_inst_state                   false
% 39.65/5.50  --bmc1_pre_inst_reach_state             false
% 39.65/5.50  --bmc1_out_unsat_core                   false
% 39.65/5.50  --bmc1_aig_witness_out                  false
% 39.65/5.50  --bmc1_verbose                          false
% 39.65/5.50  --bmc1_dump_clauses_tptp                false
% 39.65/5.50  --bmc1_dump_unsat_core_tptp             false
% 39.65/5.50  --bmc1_dump_file                        -
% 39.65/5.50  --bmc1_ucm_expand_uc_limit              128
% 39.65/5.50  --bmc1_ucm_n_expand_iterations          6
% 39.65/5.50  --bmc1_ucm_extend_mode                  1
% 39.65/5.50  --bmc1_ucm_init_mode                    2
% 39.65/5.50  --bmc1_ucm_cone_mode                    none
% 39.65/5.50  --bmc1_ucm_reduced_relation_type        0
% 39.65/5.50  --bmc1_ucm_relax_model                  4
% 39.65/5.50  --bmc1_ucm_full_tr_after_sat            true
% 39.65/5.50  --bmc1_ucm_expand_neg_assumptions       false
% 39.65/5.50  --bmc1_ucm_layered_model                none
% 39.65/5.50  --bmc1_ucm_max_lemma_size               10
% 39.65/5.50  
% 39.65/5.50  ------ AIG Options
% 39.65/5.50  
% 39.65/5.50  --aig_mode                              false
% 39.65/5.50  
% 39.65/5.50  ------ Instantiation Options
% 39.65/5.50  
% 39.65/5.50  --instantiation_flag                    true
% 39.65/5.50  --inst_sos_flag                         true
% 39.65/5.50  --inst_sos_phase                        true
% 39.65/5.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 39.65/5.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 39.65/5.50  --inst_lit_sel_side                     none
% 39.65/5.50  --inst_solver_per_active                1400
% 39.65/5.50  --inst_solver_calls_frac                1.
% 39.65/5.50  --inst_passive_queue_type               priority_queues
% 39.65/5.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 39.65/5.50  --inst_passive_queues_freq              [25;2]
% 39.65/5.50  --inst_dismatching                      true
% 39.65/5.50  --inst_eager_unprocessed_to_passive     true
% 39.65/5.51  --inst_prop_sim_given                   true
% 39.65/5.51  --inst_prop_sim_new                     false
% 39.65/5.51  --inst_subs_new                         false
% 39.65/5.51  --inst_eq_res_simp                      false
% 39.65/5.51  --inst_subs_given                       false
% 39.65/5.51  --inst_orphan_elimination               true
% 39.65/5.51  --inst_learning_loop_flag               true
% 39.65/5.51  --inst_learning_start                   3000
% 39.65/5.51  --inst_learning_factor                  2
% 39.65/5.51  --inst_start_prop_sim_after_learn       3
% 39.65/5.51  --inst_sel_renew                        solver
% 39.65/5.51  --inst_lit_activity_flag                true
% 39.65/5.51  --inst_restr_to_given                   false
% 39.65/5.51  --inst_activity_threshold               500
% 39.65/5.51  --inst_out_proof                        true
% 39.65/5.51  
% 39.65/5.51  ------ Resolution Options
% 39.65/5.51  
% 39.65/5.51  --resolution_flag                       false
% 39.65/5.51  --res_lit_sel                           adaptive
% 39.65/5.51  --res_lit_sel_side                      none
% 39.65/5.51  --res_ordering                          kbo
% 39.65/5.51  --res_to_prop_solver                    active
% 39.65/5.51  --res_prop_simpl_new                    false
% 39.65/5.51  --res_prop_simpl_given                  true
% 39.65/5.51  --res_passive_queue_type                priority_queues
% 39.65/5.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 39.65/5.51  --res_passive_queues_freq               [15;5]
% 39.65/5.51  --res_forward_subs                      full
% 39.65/5.51  --res_backward_subs                     full
% 39.65/5.51  --res_forward_subs_resolution           true
% 39.65/5.51  --res_backward_subs_resolution          true
% 39.65/5.51  --res_orphan_elimination                true
% 39.65/5.51  --res_time_limit                        2.
% 39.65/5.51  --res_out_proof                         true
% 39.65/5.51  
% 39.65/5.51  ------ Superposition Options
% 39.65/5.51  
% 39.65/5.51  --superposition_flag                    true
% 39.65/5.51  --sup_passive_queue_type                priority_queues
% 39.65/5.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 39.65/5.51  --sup_passive_queues_freq               [8;1;4]
% 39.65/5.51  --demod_completeness_check              fast
% 39.65/5.51  --demod_use_ground                      true
% 39.65/5.51  --sup_to_prop_solver                    passive
% 39.65/5.51  --sup_prop_simpl_new                    true
% 39.65/5.51  --sup_prop_simpl_given                  true
% 39.65/5.51  --sup_fun_splitting                     true
% 39.65/5.51  --sup_smt_interval                      50000
% 39.65/5.51  
% 39.65/5.51  ------ Superposition Simplification Setup
% 39.65/5.51  
% 39.65/5.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 39.65/5.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 39.65/5.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 39.65/5.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 39.65/5.51  --sup_full_triv                         [TrivRules;PropSubs]
% 39.65/5.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 39.65/5.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 39.65/5.51  --sup_immed_triv                        [TrivRules]
% 39.65/5.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 39.65/5.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 39.65/5.51  --sup_immed_bw_main                     []
% 39.65/5.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 39.65/5.51  --sup_input_triv                        [Unflattening;TrivRules]
% 39.65/5.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 39.65/5.51  --sup_input_bw                          []
% 39.65/5.51  
% 39.65/5.51  ------ Combination Options
% 39.65/5.51  
% 39.65/5.51  --comb_res_mult                         3
% 39.65/5.51  --comb_sup_mult                         2
% 39.65/5.51  --comb_inst_mult                        10
% 39.65/5.51  
% 39.65/5.51  ------ Debug Options
% 39.65/5.51  
% 39.65/5.51  --dbg_backtrace                         false
% 39.65/5.51  --dbg_dump_prop_clauses                 false
% 39.65/5.51  --dbg_dump_prop_clauses_file            -
% 39.65/5.51  --dbg_out_stat                          false
% 39.65/5.51  
% 39.65/5.51  
% 39.65/5.51  
% 39.65/5.51  
% 39.65/5.51  ------ Proving...
% 39.65/5.51  
% 39.65/5.51  
% 39.65/5.51  % SZS status Theorem for theBenchmark.p
% 39.65/5.51  
% 39.65/5.51  % SZS output start CNFRefutation for theBenchmark.p
% 39.65/5.51  
% 39.65/5.51  fof(f17,conjecture,(
% 39.65/5.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 39.65/5.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.65/5.51  
% 39.65/5.51  fof(f18,negated_conjecture,(
% 39.65/5.51    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 39.65/5.51    inference(negated_conjecture,[],[f17])).
% 39.65/5.51  
% 39.65/5.51  fof(f33,plain,(
% 39.65/5.51    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 39.65/5.51    inference(ennf_transformation,[],[f18])).
% 39.65/5.51  
% 39.65/5.51  fof(f34,plain,(
% 39.65/5.51    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 39.65/5.51    inference(flattening,[],[f33])).
% 39.65/5.51  
% 39.65/5.51  fof(f38,plain,(
% 39.65/5.51    ( ! [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) => (k10_relat_1(X0,sK2) != k10_relat_1(k7_relat_1(X0,sK1),sK2) & r1_tarski(k10_relat_1(X0,sK2),sK1))) )),
% 39.65/5.51    introduced(choice_axiom,[])).
% 39.65/5.51  
% 39.65/5.51  fof(f37,plain,(
% 39.65/5.51    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X2,X1] : (k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(k10_relat_1(sK0,X2),X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 39.65/5.51    introduced(choice_axiom,[])).
% 39.65/5.51  
% 39.65/5.51  fof(f39,plain,(
% 39.65/5.51    (k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(k10_relat_1(sK0,sK2),sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 39.65/5.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f34,f38,f37])).
% 39.65/5.51  
% 39.65/5.51  fof(f62,plain,(
% 39.65/5.51    r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 39.65/5.51    inference(cnf_transformation,[],[f39])).
% 39.65/5.51  
% 39.65/5.51  fof(f2,axiom,(
% 39.65/5.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 39.65/5.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.65/5.51  
% 39.65/5.51  fof(f35,plain,(
% 39.65/5.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 39.65/5.51    inference(nnf_transformation,[],[f2])).
% 39.65/5.51  
% 39.65/5.51  fof(f36,plain,(
% 39.65/5.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 39.65/5.51    inference(flattening,[],[f35])).
% 39.65/5.51  
% 39.65/5.51  fof(f41,plain,(
% 39.65/5.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 39.65/5.51    inference(cnf_transformation,[],[f36])).
% 39.65/5.51  
% 39.65/5.51  fof(f70,plain,(
% 39.65/5.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 39.65/5.51    inference(equality_resolution,[],[f41])).
% 39.65/5.51  
% 39.65/5.51  fof(f12,axiom,(
% 39.65/5.51    ! [X0,X1,X2] : (v1_relat_1(X2) => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1))),
% 39.65/5.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.65/5.51  
% 39.65/5.51  fof(f26,plain,(
% 39.65/5.51    ! [X0,X1,X2] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 39.65/5.51    inference(ennf_transformation,[],[f12])).
% 39.65/5.51  
% 39.65/5.51  fof(f55,plain,(
% 39.65/5.51    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 39.65/5.51    inference(cnf_transformation,[],[f26])).
% 39.65/5.51  
% 39.65/5.51  fof(f5,axiom,(
% 39.65/5.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 39.65/5.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.65/5.51  
% 39.65/5.51  fof(f46,plain,(
% 39.65/5.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 39.65/5.51    inference(cnf_transformation,[],[f5])).
% 39.65/5.51  
% 39.65/5.51  fof(f4,axiom,(
% 39.65/5.51    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 39.65/5.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.65/5.51  
% 39.65/5.51  fof(f45,plain,(
% 39.65/5.51    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 39.65/5.51    inference(cnf_transformation,[],[f4])).
% 39.65/5.51  
% 39.65/5.51  fof(f64,plain,(
% 39.65/5.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 39.65/5.51    inference(definition_unfolding,[],[f46,f45])).
% 39.65/5.51  
% 39.65/5.51  fof(f66,plain,(
% 39.65/5.51    ( ! [X2,X0,X1] : (k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(X2,X1))) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 39.65/5.51    inference(definition_unfolding,[],[f55,f64])).
% 39.65/5.51  
% 39.65/5.51  fof(f60,plain,(
% 39.65/5.51    v1_relat_1(sK0)),
% 39.65/5.51    inference(cnf_transformation,[],[f39])).
% 39.65/5.51  
% 39.65/5.51  fof(f16,axiom,(
% 39.65/5.51    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))),
% 39.65/5.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.65/5.51  
% 39.65/5.51  fof(f59,plain,(
% 39.65/5.51    ( ! [X0,X1] : (k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) )),
% 39.65/5.51    inference(cnf_transformation,[],[f16])).
% 39.65/5.51  
% 39.65/5.51  fof(f68,plain,(
% 39.65/5.51    ( ! [X0,X1] : (k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) )),
% 39.65/5.51    inference(definition_unfolding,[],[f59,f64])).
% 39.65/5.51  
% 39.65/5.51  fof(f10,axiom,(
% 39.65/5.51    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 39.65/5.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.65/5.51  
% 39.65/5.51  fof(f25,plain,(
% 39.65/5.51    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 39.65/5.51    inference(ennf_transformation,[],[f10])).
% 39.65/5.51  
% 39.65/5.51  fof(f52,plain,(
% 39.65/5.51    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 39.65/5.51    inference(cnf_transformation,[],[f25])).
% 39.65/5.51  
% 39.65/5.51  fof(f11,axiom,(
% 39.65/5.51    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 39.65/5.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.65/5.51  
% 39.65/5.51  fof(f53,plain,(
% 39.65/5.51    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 39.65/5.51    inference(cnf_transformation,[],[f11])).
% 39.65/5.51  
% 39.65/5.51  fof(f6,axiom,(
% 39.65/5.51    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 39.65/5.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.65/5.51  
% 39.65/5.51  fof(f22,plain,(
% 39.65/5.51    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 39.65/5.51    inference(ennf_transformation,[],[f6])).
% 39.65/5.51  
% 39.65/5.51  fof(f47,plain,(
% 39.65/5.51    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 39.65/5.51    inference(cnf_transformation,[],[f22])).
% 39.65/5.51  
% 39.65/5.51  fof(f9,axiom,(
% 39.65/5.51    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 39.65/5.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.65/5.51  
% 39.65/5.51  fof(f51,plain,(
% 39.65/5.51    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 39.65/5.51    inference(cnf_transformation,[],[f9])).
% 39.65/5.51  
% 39.65/5.51  fof(f54,plain,(
% 39.65/5.51    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 39.65/5.51    inference(cnf_transformation,[],[f11])).
% 39.65/5.51  
% 39.65/5.51  fof(f15,axiom,(
% 39.65/5.51    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 39.65/5.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.65/5.51  
% 39.65/5.51  fof(f31,plain,(
% 39.65/5.51    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 39.65/5.51    inference(ennf_transformation,[],[f15])).
% 39.65/5.51  
% 39.65/5.51  fof(f32,plain,(
% 39.65/5.51    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 39.65/5.51    inference(flattening,[],[f31])).
% 39.65/5.51  
% 39.65/5.51  fof(f58,plain,(
% 39.65/5.51    ( ! [X2,X0,X1] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 39.65/5.51    inference(cnf_transformation,[],[f32])).
% 39.65/5.51  
% 39.65/5.51  fof(f50,plain,(
% 39.65/5.51    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 39.65/5.51    inference(cnf_transformation,[],[f9])).
% 39.65/5.51  
% 39.65/5.51  fof(f1,axiom,(
% 39.65/5.51    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 39.65/5.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.65/5.51  
% 39.65/5.51  fof(f19,plain,(
% 39.65/5.51    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 39.65/5.51    inference(rectify,[],[f1])).
% 39.65/5.51  
% 39.65/5.51  fof(f40,plain,(
% 39.65/5.51    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 39.65/5.51    inference(cnf_transformation,[],[f19])).
% 39.65/5.51  
% 39.65/5.51  fof(f65,plain,(
% 39.65/5.51    ( ! [X0] : (k1_setfam_1(k1_enumset1(X0,X0,X0)) = X0) )),
% 39.65/5.51    inference(definition_unfolding,[],[f40,f64])).
% 39.65/5.51  
% 39.65/5.51  fof(f14,axiom,(
% 39.65/5.51    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)))),
% 39.65/5.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.65/5.51  
% 39.65/5.51  fof(f29,plain,(
% 39.65/5.51    ! [X0,X1] : (k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 39.65/5.51    inference(ennf_transformation,[],[f14])).
% 39.65/5.51  
% 39.65/5.51  fof(f30,plain,(
% 39.65/5.51    ! [X0,X1] : (k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 39.65/5.51    inference(flattening,[],[f29])).
% 39.65/5.51  
% 39.65/5.51  fof(f57,plain,(
% 39.65/5.51    ( ! [X0,X1] : (k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 39.65/5.51    inference(cnf_transformation,[],[f30])).
% 39.65/5.51  
% 39.65/5.51  fof(f67,plain,(
% 39.65/5.51    ( ! [X0,X1] : (k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(X1,k1_relat_1(X1)))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 39.65/5.51    inference(definition_unfolding,[],[f57,f64])).
% 39.65/5.51  
% 39.65/5.51  fof(f8,axiom,(
% 39.65/5.51    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 39.65/5.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.65/5.51  
% 39.65/5.51  fof(f24,plain,(
% 39.65/5.51    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 39.65/5.51    inference(ennf_transformation,[],[f8])).
% 39.65/5.51  
% 39.65/5.51  fof(f49,plain,(
% 39.65/5.51    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 39.65/5.51    inference(cnf_transformation,[],[f24])).
% 39.65/5.51  
% 39.65/5.51  fof(f7,axiom,(
% 39.65/5.51    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 39.65/5.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.65/5.51  
% 39.65/5.51  fof(f23,plain,(
% 39.65/5.51    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 39.65/5.51    inference(ennf_transformation,[],[f7])).
% 39.65/5.51  
% 39.65/5.51  fof(f48,plain,(
% 39.65/5.51    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 39.65/5.51    inference(cnf_transformation,[],[f23])).
% 39.65/5.51  
% 39.65/5.51  fof(f43,plain,(
% 39.65/5.51    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 39.65/5.51    inference(cnf_transformation,[],[f36])).
% 39.65/5.51  
% 39.65/5.51  fof(f61,plain,(
% 39.65/5.51    v1_funct_1(sK0)),
% 39.65/5.51    inference(cnf_transformation,[],[f39])).
% 39.65/5.51  
% 39.65/5.51  fof(f63,plain,(
% 39.65/5.51    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 39.65/5.51    inference(cnf_transformation,[],[f39])).
% 39.65/5.51  
% 39.65/5.51  cnf(c_19,negated_conjecture,
% 39.65/5.51      ( r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
% 39.65/5.51      inference(cnf_transformation,[],[f62]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_563,plain,
% 39.65/5.51      ( r1_tarski(k10_relat_1(sK0,sK2),sK1) = iProver_top ),
% 39.65/5.51      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_3,plain,
% 39.65/5.51      ( r1_tarski(X0,X0) ),
% 39.65/5.51      inference(cnf_transformation,[],[f70]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_565,plain,
% 39.65/5.51      ( r1_tarski(X0,X0) = iProver_top ),
% 39.65/5.51      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_13,plain,
% 39.65/5.51      ( ~ v1_relat_1(X0)
% 39.65/5.51      | k1_setfam_1(k1_enumset1(X1,X1,k10_relat_1(X0,X2))) = k10_relat_1(k7_relat_1(X0,X1),X2) ),
% 39.65/5.51      inference(cnf_transformation,[],[f66]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_21,negated_conjecture,
% 39.65/5.51      ( v1_relat_1(sK0) ),
% 39.65/5.51      inference(cnf_transformation,[],[f60]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_342,plain,
% 39.65/5.51      ( k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(X1,X2))) = k10_relat_1(k7_relat_1(X1,X0),X2)
% 39.65/5.51      | sK0 != X1 ),
% 39.65/5.51      inference(resolution_lifted,[status(thm)],[c_13,c_21]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_343,plain,
% 39.65/5.51      ( k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(sK0,X1))) = k10_relat_1(k7_relat_1(sK0,X0),X1) ),
% 39.65/5.51      inference(unflattening,[status(thm)],[c_342]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_17,plain,
% 39.65/5.51      ( k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
% 39.65/5.51      inference(cnf_transformation,[],[f68]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_10,plain,
% 39.65/5.51      ( ~ v1_relat_1(X0)
% 39.65/5.51      | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
% 39.65/5.51      inference(cnf_transformation,[],[f52]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_12,plain,
% 39.65/5.51      ( v1_relat_1(k6_relat_1(X0)) ),
% 39.65/5.51      inference(cnf_transformation,[],[f53]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_315,plain,
% 39.65/5.51      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
% 39.65/5.51      | k6_relat_1(X2) != X1 ),
% 39.65/5.51      inference(resolution_lifted,[status(thm)],[c_10,c_12]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_316,plain,
% 39.65/5.51      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
% 39.65/5.51      inference(unflattening,[status(thm)],[c_315]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_569,plain,
% 39.65/5.51      ( k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
% 39.65/5.51      inference(demodulation,[status(thm)],[c_17,c_316]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_2077,plain,
% 39.65/5.51      ( k6_relat_1(k10_relat_1(k7_relat_1(sK0,X0),X1)) = k7_relat_1(k6_relat_1(X0),k10_relat_1(sK0,X1)) ),
% 39.65/5.51      inference(superposition,[status(thm)],[c_343,c_569]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_5,plain,
% 39.65/5.51      ( ~ v1_relat_1(X0)
% 39.65/5.51      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 39.65/5.51      inference(cnf_transformation,[],[f47]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_336,plain,
% 39.65/5.51      ( k6_relat_1(X0) != X1
% 39.65/5.51      | k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2) ),
% 39.65/5.51      inference(resolution_lifted,[status(thm)],[c_5,c_12]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_337,plain,
% 39.65/5.51      ( k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1) ),
% 39.65/5.51      inference(unflattening,[status(thm)],[c_336]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_2696,plain,
% 39.65/5.51      ( k2_relat_1(k6_relat_1(k10_relat_1(k7_relat_1(sK0,X0),X1))) = k9_relat_1(k6_relat_1(X0),k10_relat_1(sK0,X1)) ),
% 39.65/5.51      inference(superposition,[status(thm)],[c_2077,c_337]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_8,plain,
% 39.65/5.51      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 39.65/5.51      inference(cnf_transformation,[],[f51]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_2697,plain,
% 39.65/5.51      ( k9_relat_1(k6_relat_1(X0),k10_relat_1(sK0,X1)) = k10_relat_1(k7_relat_1(sK0,X0),X1) ),
% 39.65/5.51      inference(demodulation,[status(thm)],[c_2696,c_8]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_11,plain,
% 39.65/5.51      ( v1_funct_1(k6_relat_1(X0)) ),
% 39.65/5.51      inference(cnf_transformation,[],[f54]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_16,plain,
% 39.65/5.51      ( r1_tarski(X0,k10_relat_1(X1,X2))
% 39.65/5.51      | ~ r1_tarski(X0,k1_relat_1(X1))
% 39.65/5.51      | ~ r1_tarski(k9_relat_1(X1,X0),X2)
% 39.65/5.51      | ~ v1_funct_1(X1)
% 39.65/5.51      | ~ v1_relat_1(X1) ),
% 39.65/5.51      inference(cnf_transformation,[],[f58]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_202,plain,
% 39.65/5.51      ( r1_tarski(X0,k10_relat_1(X1,X2))
% 39.65/5.51      | ~ r1_tarski(X0,k1_relat_1(X1))
% 39.65/5.51      | ~ r1_tarski(k9_relat_1(X1,X0),X2)
% 39.65/5.51      | ~ v1_relat_1(X1)
% 39.65/5.51      | k6_relat_1(X3) != X1 ),
% 39.65/5.51      inference(resolution_lifted,[status(thm)],[c_11,c_16]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_203,plain,
% 39.65/5.51      ( r1_tarski(X0,k10_relat_1(k6_relat_1(X1),X2))
% 39.65/5.51      | ~ r1_tarski(X0,k1_relat_1(k6_relat_1(X1)))
% 39.65/5.51      | ~ r1_tarski(k9_relat_1(k6_relat_1(X1),X0),X2)
% 39.65/5.51      | ~ v1_relat_1(k6_relat_1(X1)) ),
% 39.65/5.51      inference(unflattening,[status(thm)],[c_202]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_215,plain,
% 39.65/5.51      ( r1_tarski(X0,k10_relat_1(k6_relat_1(X1),X2))
% 39.65/5.51      | ~ r1_tarski(X0,k1_relat_1(k6_relat_1(X1)))
% 39.65/5.51      | ~ r1_tarski(k9_relat_1(k6_relat_1(X1),X0),X2) ),
% 39.65/5.51      inference(forward_subsumption_resolution,
% 39.65/5.51                [status(thm)],
% 39.65/5.51                [c_203,c_12]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_562,plain,
% 39.65/5.51      ( r1_tarski(X0,k10_relat_1(k6_relat_1(X1),X2)) = iProver_top
% 39.65/5.51      | r1_tarski(X0,k1_relat_1(k6_relat_1(X1))) != iProver_top
% 39.65/5.51      | r1_tarski(k9_relat_1(k6_relat_1(X1),X0),X2) != iProver_top ),
% 39.65/5.51      inference(predicate_to_equality,[status(thm)],[c_215]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_9,plain,
% 39.65/5.51      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 39.65/5.51      inference(cnf_transformation,[],[f50]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_571,plain,
% 39.65/5.51      ( r1_tarski(X0,X1) != iProver_top
% 39.65/5.51      | r1_tarski(X0,k10_relat_1(k6_relat_1(X1),X2)) = iProver_top
% 39.65/5.51      | r1_tarski(k9_relat_1(k6_relat_1(X1),X0),X2) != iProver_top ),
% 39.65/5.51      inference(demodulation,[status(thm)],[c_562,c_9]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_3580,plain,
% 39.65/5.51      ( r1_tarski(k10_relat_1(k7_relat_1(sK0,X0),X1),X2) != iProver_top
% 39.65/5.51      | r1_tarski(k10_relat_1(sK0,X1),X0) != iProver_top
% 39.65/5.51      | r1_tarski(k10_relat_1(sK0,X1),k10_relat_1(k6_relat_1(X0),X2)) = iProver_top ),
% 39.65/5.51      inference(superposition,[status(thm)],[c_2697,c_571]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_0,plain,
% 39.65/5.51      ( k1_setfam_1(k1_enumset1(X0,X0,X0)) = X0 ),
% 39.65/5.51      inference(cnf_transformation,[],[f65]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_2074,plain,
% 39.65/5.51      ( k7_relat_1(k6_relat_1(X0),X0) = k6_relat_1(X0) ),
% 39.65/5.51      inference(superposition,[status(thm)],[c_0,c_569]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_309,plain,
% 39.65/5.51      ( k6_relat_1(X0) != X1
% 39.65/5.51      | k1_setfam_1(k1_enumset1(X2,X2,k10_relat_1(X1,X3))) = k10_relat_1(k7_relat_1(X1,X2),X3) ),
% 39.65/5.51      inference(resolution_lifted,[status(thm)],[c_13,c_12]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_310,plain,
% 39.65/5.51      ( k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(k6_relat_1(X1),X2))) = k10_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2) ),
% 39.65/5.51      inference(unflattening,[status(thm)],[c_309]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_2086,plain,
% 39.65/5.51      ( k10_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))),X2),X3) = k1_setfam_1(k1_enumset1(X2,X2,k10_relat_1(k7_relat_1(k6_relat_1(X0),X1),X3))) ),
% 39.65/5.51      inference(superposition,[status(thm)],[c_569,c_310]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_2083,plain,
% 39.65/5.51      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
% 39.65/5.51      inference(superposition,[status(thm)],[c_569,c_8]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_2089,plain,
% 39.65/5.51      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k9_relat_1(k6_relat_1(X0),X1) ),
% 39.65/5.51      inference(light_normalisation,[status(thm)],[c_2083,c_337]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_2091,plain,
% 39.65/5.51      ( k6_relat_1(k9_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
% 39.65/5.51      inference(demodulation,[status(thm)],[c_2089,c_569]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_2255,plain,
% 39.65/5.51      ( k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3))) = k10_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0),X3) ),
% 39.65/5.51      inference(light_normalisation,[status(thm)],[c_2086,c_2089,c_2091]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_6957,plain,
% 39.65/5.51      ( k10_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k10_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)),X2) = k10_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) ),
% 39.65/5.51      inference(superposition,[status(thm)],[c_2255,c_0]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_7164,plain,
% 39.65/5.51      ( k10_relat_1(k7_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)),X1) = k10_relat_1(k7_relat_1(k6_relat_1(X0),X0),X1) ),
% 39.65/5.51      inference(superposition,[status(thm)],[c_2074,c_6957]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_15,plain,
% 39.65/5.51      ( ~ v1_funct_1(X0)
% 39.65/5.51      | ~ v1_relat_1(X0)
% 39.65/5.51      | k1_setfam_1(k1_enumset1(X1,X1,k9_relat_1(X0,k1_relat_1(X0)))) = k9_relat_1(X0,k10_relat_1(X0,X1)) ),
% 39.65/5.51      inference(cnf_transformation,[],[f67]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_222,plain,
% 39.65/5.51      ( ~ v1_relat_1(X0)
% 39.65/5.51      | k6_relat_1(X1) != X0
% 39.65/5.51      | k1_setfam_1(k1_enumset1(X2,X2,k9_relat_1(X0,k1_relat_1(X0)))) = k9_relat_1(X0,k10_relat_1(X0,X2)) ),
% 39.65/5.51      inference(resolution_lifted,[status(thm)],[c_11,c_15]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_223,plain,
% 39.65/5.51      ( ~ v1_relat_1(k6_relat_1(X0))
% 39.65/5.51      | k1_setfam_1(k1_enumset1(X1,X1,k9_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0))))) = k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) ),
% 39.65/5.51      inference(unflattening,[status(thm)],[c_222]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_227,plain,
% 39.65/5.51      ( k1_setfam_1(k1_enumset1(X1,X1,k9_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0))))) = k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) ),
% 39.65/5.51      inference(global_propositional_subsumption,
% 39.65/5.51                [status(thm)],
% 39.65/5.51                [c_223,c_12]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_228,plain,
% 39.65/5.51      ( k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(k6_relat_1(X1),k1_relat_1(k6_relat_1(X1))))) = k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X0)) ),
% 39.65/5.51      inference(renaming,[status(thm)],[c_227]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_570,plain,
% 39.65/5.51      ( k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(k6_relat_1(X1),X1))) = k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X0)) ),
% 39.65/5.51      inference(demodulation,[status(thm)],[c_228,c_9]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_2966,plain,
% 39.65/5.51      ( k9_relat_1(k6_relat_1(X0),X0) = k2_relat_1(k6_relat_1(X0)) ),
% 39.65/5.51      inference(superposition,[status(thm)],[c_2074,c_337]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_2973,plain,
% 39.65/5.51      ( k9_relat_1(k6_relat_1(X0),X0) = X0 ),
% 39.65/5.51      inference(light_normalisation,[status(thm)],[c_2966,c_8]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_3434,plain,
% 39.65/5.51      ( k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X1),X0) ),
% 39.65/5.51      inference(demodulation,[status(thm)],[c_570,c_2089,c_2973]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_4610,plain,
% 39.65/5.51      ( k7_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = k6_relat_1(k9_relat_1(k6_relat_1(X1),X0)) ),
% 39.65/5.51      inference(superposition,[status(thm)],[c_3434,c_2091]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_4644,plain,
% 39.65/5.51      ( k7_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
% 39.65/5.51      inference(demodulation,[status(thm)],[c_4610,c_2091]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_7176,plain,
% 39.65/5.51      ( k10_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) = k10_relat_1(k6_relat_1(X1),X0) ),
% 39.65/5.51      inference(light_normalisation,[status(thm)],[c_7164,c_2074,c_4644]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_7,plain,
% 39.65/5.51      ( ~ v1_relat_1(X0)
% 39.65/5.51      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 39.65/5.51      inference(cnf_transformation,[],[f49]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_321,plain,
% 39.65/5.51      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
% 39.65/5.51      | k6_relat_1(X1) != X0 ),
% 39.65/5.51      inference(resolution_lifted,[status(thm)],[c_7,c_12]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_322,plain,
% 39.65/5.51      ( k10_relat_1(k6_relat_1(X0),k2_relat_1(k6_relat_1(X0))) = k1_relat_1(k6_relat_1(X0)) ),
% 39.65/5.51      inference(unflattening,[status(thm)],[c_321]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_568,plain,
% 39.65/5.51      ( k10_relat_1(k6_relat_1(X0),X0) = X0 ),
% 39.65/5.51      inference(light_normalisation,[status(thm)],[c_322,c_8,c_9]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_1918,plain,
% 39.65/5.51      ( k10_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) = k1_setfam_1(k1_enumset1(X1,X1,X0)) ),
% 39.65/5.51      inference(superposition,[status(thm)],[c_568,c_310]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_4374,plain,
% 39.65/5.51      ( k10_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) = k9_relat_1(k6_relat_1(X1),X0) ),
% 39.65/5.51      inference(demodulation,[status(thm)],[c_1918,c_2089]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_7177,plain,
% 39.65/5.51      ( k10_relat_1(k6_relat_1(X0),X1) = k9_relat_1(k6_relat_1(X0),X1) ),
% 39.65/5.51      inference(demodulation,[status(thm)],[c_7176,c_4374]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_67638,plain,
% 39.65/5.51      ( r1_tarski(k10_relat_1(k7_relat_1(sK0,X0),X1),X2) != iProver_top
% 39.65/5.51      | r1_tarski(k10_relat_1(sK0,X1),X0) != iProver_top
% 39.65/5.51      | r1_tarski(k10_relat_1(sK0,X1),k9_relat_1(k6_relat_1(X0),X2)) = iProver_top ),
% 39.65/5.51      inference(demodulation,[status(thm)],[c_3580,c_7177]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_6,plain,
% 39.65/5.51      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 39.65/5.51      inference(cnf_transformation,[],[f48]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_327,plain,
% 39.65/5.51      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0))
% 39.65/5.51      | k6_relat_1(X2) != X0 ),
% 39.65/5.51      inference(resolution_lifted,[status(thm)],[c_6,c_12]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_328,plain,
% 39.65/5.51      ( r1_tarski(k10_relat_1(k6_relat_1(X0),X1),k1_relat_1(k6_relat_1(X0))) ),
% 39.65/5.51      inference(unflattening,[status(thm)],[c_327]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_558,plain,
% 39.65/5.51      ( r1_tarski(k10_relat_1(k6_relat_1(X0),X1),k1_relat_1(k6_relat_1(X0))) = iProver_top ),
% 39.65/5.51      inference(predicate_to_equality,[status(thm)],[c_328]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_567,plain,
% 39.65/5.51      ( r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) = iProver_top ),
% 39.65/5.51      inference(light_normalisation,[status(thm)],[c_558,c_9]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_1,plain,
% 39.65/5.51      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 39.65/5.51      inference(cnf_transformation,[],[f43]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_566,plain,
% 39.65/5.51      ( X0 = X1
% 39.65/5.51      | r1_tarski(X0,X1) != iProver_top
% 39.65/5.51      | r1_tarski(X1,X0) != iProver_top ),
% 39.65/5.51      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_3445,plain,
% 39.65/5.51      ( k10_relat_1(k6_relat_1(X0),X1) = X0
% 39.65/5.51      | r1_tarski(X0,k10_relat_1(k6_relat_1(X0),X1)) != iProver_top ),
% 39.65/5.51      inference(superposition,[status(thm)],[c_567,c_566]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_8884,plain,
% 39.65/5.51      ( k10_relat_1(k6_relat_1(X0),X1) = X0
% 39.65/5.51      | r1_tarski(X0,k9_relat_1(k6_relat_1(X0),X1)) != iProver_top ),
% 39.65/5.51      inference(light_normalisation,[status(thm)],[c_3445,c_7177]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_8885,plain,
% 39.65/5.51      ( k9_relat_1(k6_relat_1(X0),X1) = X0
% 39.65/5.51      | r1_tarski(X0,k9_relat_1(k6_relat_1(X0),X1)) != iProver_top ),
% 39.65/5.51      inference(demodulation,[status(thm)],[c_8884,c_7177]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_67671,plain,
% 39.65/5.51      ( k9_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),X1) = k10_relat_1(sK0,X0)
% 39.65/5.51      | r1_tarski(k10_relat_1(k7_relat_1(sK0,k10_relat_1(sK0,X0)),X0),X1) != iProver_top
% 39.65/5.51      | r1_tarski(k10_relat_1(sK0,X0),k10_relat_1(sK0,X0)) != iProver_top ),
% 39.65/5.51      inference(superposition,[status(thm)],[c_67638,c_8885]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_1194,plain,
% 39.65/5.51      ( k10_relat_1(k7_relat_1(sK0,k10_relat_1(sK0,X0)),X0) = k10_relat_1(sK0,X0) ),
% 39.65/5.51      inference(superposition,[status(thm)],[c_0,c_343]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_67674,plain,
% 39.65/5.51      ( k9_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),X1) = k10_relat_1(sK0,X0)
% 39.65/5.51      | r1_tarski(k10_relat_1(sK0,X0),X1) != iProver_top
% 39.65/5.51      | r1_tarski(k10_relat_1(sK0,X0),k10_relat_1(sK0,X0)) != iProver_top ),
% 39.65/5.51      inference(light_normalisation,[status(thm)],[c_67671,c_1194]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_71442,plain,
% 39.65/5.51      ( k9_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),X1) = k10_relat_1(sK0,X0)
% 39.65/5.51      | r1_tarski(k10_relat_1(sK0,X0),X1) != iProver_top ),
% 39.65/5.51      inference(superposition,[status(thm)],[c_565,c_67674]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_72464,plain,
% 39.65/5.51      ( k9_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1) = k10_relat_1(sK0,sK2) ),
% 39.65/5.51      inference(superposition,[status(thm)],[c_563,c_71442]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_4378,plain,
% 39.65/5.51      ( k10_relat_1(k6_relat_1(k10_relat_1(k7_relat_1(sK0,X0),X1)),X0) = k9_relat_1(k6_relat_1(k10_relat_1(sK0,X1)),X0) ),
% 39.65/5.51      inference(superposition,[status(thm)],[c_2077,c_4374]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_4814,plain,
% 39.65/5.51      ( r1_tarski(k9_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),X1),k10_relat_1(k7_relat_1(sK0,X1),X0)) = iProver_top ),
% 39.65/5.51      inference(superposition,[status(thm)],[c_4378,c_567]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_73730,plain,
% 39.65/5.51      ( r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k7_relat_1(sK0,sK1),sK2)) = iProver_top ),
% 39.65/5.51      inference(superposition,[status(thm)],[c_72464,c_4814]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_359,plain,
% 39.65/5.51      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) | sK0 != X0 ),
% 39.65/5.51      inference(resolution_lifted,[status(thm)],[c_6,c_21]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_360,plain,
% 39.65/5.51      ( r1_tarski(k10_relat_1(sK0,X0),k1_relat_1(sK0)) ),
% 39.65/5.51      inference(unflattening,[status(thm)],[c_359]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_557,plain,
% 39.65/5.51      ( r1_tarski(k10_relat_1(sK0,X0),k1_relat_1(sK0)) = iProver_top ),
% 39.65/5.51      inference(predicate_to_equality,[status(thm)],[c_360]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_20,negated_conjecture,
% 39.65/5.51      ( v1_funct_1(sK0) ),
% 39.65/5.51      inference(cnf_transformation,[],[f61]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_248,plain,
% 39.65/5.51      ( r1_tarski(X0,k10_relat_1(X1,X2))
% 39.65/5.51      | ~ r1_tarski(X0,k1_relat_1(X1))
% 39.65/5.51      | ~ r1_tarski(k9_relat_1(X1,X0),X2)
% 39.65/5.51      | ~ v1_relat_1(X1)
% 39.65/5.51      | sK0 != X1 ),
% 39.65/5.51      inference(resolution_lifted,[status(thm)],[c_16,c_20]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_249,plain,
% 39.65/5.51      ( r1_tarski(X0,k10_relat_1(sK0,X1))
% 39.65/5.51      | ~ r1_tarski(X0,k1_relat_1(sK0))
% 39.65/5.51      | ~ r1_tarski(k9_relat_1(sK0,X0),X1)
% 39.65/5.51      | ~ v1_relat_1(sK0) ),
% 39.65/5.51      inference(unflattening,[status(thm)],[c_248]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_253,plain,
% 39.65/5.51      ( ~ r1_tarski(k9_relat_1(sK0,X0),X1)
% 39.65/5.51      | ~ r1_tarski(X0,k1_relat_1(sK0))
% 39.65/5.51      | r1_tarski(X0,k10_relat_1(sK0,X1)) ),
% 39.65/5.51      inference(global_propositional_subsumption,
% 39.65/5.51                [status(thm)],
% 39.65/5.51                [c_249,c_21]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_254,plain,
% 39.65/5.51      ( r1_tarski(X0,k10_relat_1(sK0,X1))
% 39.65/5.51      | ~ r1_tarski(X0,k1_relat_1(sK0))
% 39.65/5.51      | ~ r1_tarski(k9_relat_1(sK0,X0),X1) ),
% 39.65/5.51      inference(renaming,[status(thm)],[c_253]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_560,plain,
% 39.65/5.51      ( r1_tarski(X0,k10_relat_1(sK0,X1)) = iProver_top
% 39.65/5.51      | r1_tarski(X0,k1_relat_1(sK0)) != iProver_top
% 39.65/5.51      | r1_tarski(k9_relat_1(sK0,X0),X1) != iProver_top ),
% 39.65/5.51      inference(predicate_to_equality,[status(thm)],[c_254]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_1790,plain,
% 39.65/5.51      ( r1_tarski(X0,k10_relat_1(sK0,k9_relat_1(sK0,X0))) = iProver_top
% 39.65/5.51      | r1_tarski(X0,k1_relat_1(sK0)) != iProver_top ),
% 39.65/5.51      inference(superposition,[status(thm)],[c_565,c_560]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_3576,plain,
% 39.65/5.51      ( r1_tarski(X0,X1) != iProver_top
% 39.65/5.51      | r1_tarski(X0,k10_relat_1(k6_relat_1(X1),k10_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(k6_relat_1(X1),X0))))) = iProver_top
% 39.65/5.51      | r1_tarski(k9_relat_1(k6_relat_1(X1),X0),k1_relat_1(sK0)) != iProver_top ),
% 39.65/5.51      inference(superposition,[status(thm)],[c_1790,c_571]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_55584,plain,
% 39.65/5.51      ( r1_tarski(X0,X1) != iProver_top
% 39.65/5.51      | r1_tarski(X0,k9_relat_1(k6_relat_1(X1),k10_relat_1(sK0,k9_relat_1(sK0,k9_relat_1(k6_relat_1(X1),X0))))) = iProver_top
% 39.65/5.51      | r1_tarski(k9_relat_1(k6_relat_1(X1),X0),k1_relat_1(sK0)) != iProver_top ),
% 39.65/5.51      inference(demodulation,[status(thm)],[c_3576,c_7177]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_55585,plain,
% 39.65/5.51      ( r1_tarski(X0,X1) != iProver_top
% 39.65/5.51      | r1_tarski(X0,k10_relat_1(k7_relat_1(sK0,X1),k9_relat_1(sK0,k9_relat_1(k6_relat_1(X1),X0)))) = iProver_top
% 39.65/5.51      | r1_tarski(k9_relat_1(k6_relat_1(X1),X0),k1_relat_1(sK0)) != iProver_top ),
% 39.65/5.51      inference(demodulation,[status(thm)],[c_55584,c_2697]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_8895,plain,
% 39.65/5.51      ( k9_relat_1(k6_relat_1(X0),k10_relat_1(sK0,X1)) = X0
% 39.65/5.51      | r1_tarski(X0,k10_relat_1(k7_relat_1(sK0,X0),X1)) != iProver_top ),
% 39.65/5.51      inference(superposition,[status(thm)],[c_2697,c_8885]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_8900,plain,
% 39.65/5.51      ( k10_relat_1(k7_relat_1(sK0,X0),X1) = X0
% 39.65/5.51      | r1_tarski(X0,k10_relat_1(k7_relat_1(sK0,X0),X1)) != iProver_top ),
% 39.65/5.51      inference(demodulation,[status(thm)],[c_8895,c_2697]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_55624,plain,
% 39.65/5.51      ( k10_relat_1(k7_relat_1(sK0,X0),k9_relat_1(sK0,k9_relat_1(k6_relat_1(X0),X0))) = X0
% 39.65/5.51      | r1_tarski(X0,X0) != iProver_top
% 39.65/5.51      | r1_tarski(k9_relat_1(k6_relat_1(X0),X0),k1_relat_1(sK0)) != iProver_top ),
% 39.65/5.51      inference(superposition,[status(thm)],[c_55585,c_8900]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_55628,plain,
% 39.65/5.51      ( k10_relat_1(k7_relat_1(sK0,X0),k9_relat_1(sK0,X0)) = X0
% 39.65/5.51      | r1_tarski(X0,X0) != iProver_top
% 39.65/5.51      | r1_tarski(X0,k1_relat_1(sK0)) != iProver_top ),
% 39.65/5.51      inference(light_normalisation,[status(thm)],[c_55624,c_2973]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_59,plain,
% 39.65/5.51      ( r1_tarski(X0,X0) = iProver_top ),
% 39.65/5.51      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_60011,plain,
% 39.65/5.51      ( k10_relat_1(k7_relat_1(sK0,X0),k9_relat_1(sK0,X0)) = X0
% 39.65/5.51      | r1_tarski(X0,k1_relat_1(sK0)) != iProver_top ),
% 39.65/5.51      inference(global_propositional_subsumption,
% 39.65/5.51                [status(thm)],
% 39.65/5.51                [c_55628,c_59]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_60019,plain,
% 39.65/5.51      ( k10_relat_1(k7_relat_1(sK0,k10_relat_1(sK0,X0)),k9_relat_1(sK0,k10_relat_1(sK0,X0))) = k10_relat_1(sK0,X0) ),
% 39.65/5.51      inference(superposition,[status(thm)],[c_557,c_60011]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_62307,plain,
% 39.65/5.51      ( k9_relat_1(k6_relat_1(k10_relat_1(sK0,k9_relat_1(sK0,k10_relat_1(sK0,X0)))),k10_relat_1(sK0,X0)) = k10_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),k10_relat_1(sK0,X0)) ),
% 39.65/5.51      inference(superposition,[status(thm)],[c_60019,c_4378]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_62327,plain,
% 39.65/5.51      ( k9_relat_1(k6_relat_1(k10_relat_1(sK0,k9_relat_1(sK0,k10_relat_1(sK0,X0)))),k10_relat_1(sK0,X0)) = k10_relat_1(sK0,X0) ),
% 39.65/5.51      inference(demodulation,[status(thm)],[c_62307,c_568,c_2697]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_64606,plain,
% 39.65/5.51      ( k10_relat_1(k7_relat_1(sK0,k10_relat_1(sK0,k9_relat_1(sK0,k10_relat_1(sK0,X0)))),X0) = k10_relat_1(sK0,X0) ),
% 39.65/5.51      inference(superposition,[status(thm)],[c_62327,c_2697]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_64796,plain,
% 39.65/5.51      ( k10_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),k10_relat_1(sK0,k9_relat_1(sK0,k10_relat_1(sK0,X0)))) = k9_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),k10_relat_1(sK0,k9_relat_1(sK0,k10_relat_1(sK0,X0)))) ),
% 39.65/5.51      inference(superposition,[status(thm)],[c_64606,c_4378]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_64822,plain,
% 39.65/5.51      ( k10_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),k10_relat_1(sK0,k9_relat_1(sK0,k10_relat_1(sK0,X0)))) = k10_relat_1(sK0,X0) ),
% 39.65/5.51      inference(demodulation,
% 39.65/5.51                [status(thm)],
% 39.65/5.51                [c_64796,c_2697,c_7177,c_60019]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_64829,plain,
% 39.65/5.51      ( k10_relat_1(k7_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),X1),k10_relat_1(sK0,k9_relat_1(sK0,k10_relat_1(sK0,X0)))) = k1_setfam_1(k1_enumset1(X1,X1,k10_relat_1(sK0,X0))) ),
% 39.65/5.51      inference(superposition,[status(thm)],[c_64822,c_310]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_64835,plain,
% 39.65/5.51      ( k10_relat_1(k7_relat_1(k6_relat_1(k10_relat_1(sK0,X0)),X1),k10_relat_1(sK0,k9_relat_1(sK0,k10_relat_1(sK0,X0)))) = k10_relat_1(k7_relat_1(sK0,X1),X0) ),
% 39.65/5.51      inference(demodulation,[status(thm)],[c_64829,c_343]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_2079,plain,
% 39.65/5.51      ( r1_tarski(k10_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),k1_setfam_1(k1_enumset1(X0,X0,X1))) = iProver_top ),
% 39.65/5.51      inference(superposition,[status(thm)],[c_569,c_567]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_2262,plain,
% 39.65/5.51      ( r1_tarski(k10_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),k9_relat_1(k6_relat_1(X0),X1)) = iProver_top ),
% 39.65/5.51      inference(light_normalisation,[status(thm)],[c_2079,c_2089]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_65147,plain,
% 39.65/5.51      ( r1_tarski(k10_relat_1(k7_relat_1(sK0,X0),X1),k9_relat_1(k6_relat_1(k10_relat_1(sK0,X1)),X0)) = iProver_top ),
% 39.65/5.51      inference(superposition,[status(thm)],[c_64835,c_2262]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_73725,plain,
% 39.65/5.51      ( r1_tarski(k10_relat_1(k7_relat_1(sK0,sK1),sK2),k10_relat_1(sK0,sK2)) = iProver_top ),
% 39.65/5.51      inference(superposition,[status(thm)],[c_72464,c_65147]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_593,plain,
% 39.65/5.51      ( ~ r1_tarski(k10_relat_1(k7_relat_1(sK0,sK1),sK2),k10_relat_1(sK0,sK2))
% 39.65/5.51      | ~ r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k7_relat_1(sK0,sK1),sK2))
% 39.65/5.51      | k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
% 39.65/5.51      inference(instantiation,[status(thm)],[c_1]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_594,plain,
% 39.65/5.51      ( k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2)
% 39.65/5.51      | r1_tarski(k10_relat_1(k7_relat_1(sK0,sK1),sK2),k10_relat_1(sK0,sK2)) != iProver_top
% 39.65/5.51      | r1_tarski(k10_relat_1(sK0,sK2),k10_relat_1(k7_relat_1(sK0,sK1),sK2)) != iProver_top ),
% 39.65/5.51      inference(predicate_to_equality,[status(thm)],[c_593]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(c_18,negated_conjecture,
% 39.65/5.51      ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
% 39.65/5.51      inference(cnf_transformation,[],[f63]) ).
% 39.65/5.51  
% 39.65/5.51  cnf(contradiction,plain,
% 39.65/5.51      ( $false ),
% 39.65/5.51      inference(minisat,[status(thm)],[c_73730,c_73725,c_594,c_18]) ).
% 39.65/5.51  
% 39.65/5.51  
% 39.65/5.51  % SZS output end CNFRefutation for theBenchmark.p
% 39.65/5.51  
% 39.65/5.51  ------                               Statistics
% 39.65/5.51  
% 39.65/5.51  ------ General
% 39.65/5.51  
% 39.65/5.51  abstr_ref_over_cycles:                  0
% 39.65/5.51  abstr_ref_under_cycles:                 0
% 39.65/5.51  gc_basic_clause_elim:                   0
% 39.65/5.51  forced_gc_time:                         0
% 39.65/5.51  parsing_time:                           0.015
% 39.65/5.51  unif_index_cands_time:                  0.
% 39.65/5.51  unif_index_add_time:                    0.
% 39.65/5.51  orderings_time:                         0.
% 39.65/5.51  out_proof_time:                         0.028
% 39.65/5.51  total_time:                             4.753
% 39.65/5.51  num_of_symbols:                         46
% 39.65/5.51  num_of_terms:                           90638
% 39.65/5.51  
% 39.65/5.51  ------ Preprocessing
% 39.65/5.51  
% 39.65/5.51  num_of_splits:                          0
% 39.65/5.51  num_of_split_atoms:                     0
% 39.65/5.51  num_of_reused_defs:                     0
% 39.65/5.51  num_eq_ax_congr_red:                    5
% 39.65/5.51  num_of_sem_filtered_clauses:            1
% 39.65/5.51  num_of_subtypes:                        0
% 39.65/5.51  monotx_restored_types:                  0
% 39.65/5.51  sat_num_of_epr_types:                   0
% 39.65/5.51  sat_num_of_non_cyclic_types:            0
% 39.65/5.51  sat_guarded_non_collapsed_types:        0
% 39.65/5.51  num_pure_diseq_elim:                    0
% 39.65/5.51  simp_replaced_by:                       0
% 39.65/5.51  res_preprocessed:                       96
% 39.65/5.51  prep_upred:                             0
% 39.65/5.51  prep_unflattend:                        16
% 39.65/5.51  smt_new_axioms:                         0
% 39.65/5.51  pred_elim_cands:                        3
% 39.65/5.51  pred_elim:                              2
% 39.65/5.51  pred_elim_cl:                           -4
% 39.65/5.51  pred_elim_cycles:                       3
% 39.65/5.51  merged_defs:                            0
% 39.65/5.51  merged_defs_ncl:                        0
% 39.65/5.51  bin_hyper_res:                          0
% 39.65/5.51  prep_cycles:                            3
% 39.65/5.51  pred_elim_time:                         0.003
% 39.65/5.51  splitting_time:                         0.
% 39.65/5.51  sem_filter_time:                        0.
% 39.65/5.51  monotx_time:                            0.
% 39.65/5.51  subtype_inf_time:                       0.
% 39.65/5.51  
% 39.65/5.51  ------ Problem properties
% 39.65/5.51  
% 39.65/5.51  clauses:                                25
% 39.65/5.51  conjectures:                            2
% 39.65/5.51  epr:                                    3
% 39.65/5.51  horn:                                   25
% 39.65/5.51  ground:                                 3
% 39.65/5.51  unary:                                  21
% 39.65/5.51  binary:                                 0
% 39.65/5.51  lits:                                   33
% 39.65/5.51  lits_eq:                                16
% 39.65/5.51  fd_pure:                                0
% 39.65/5.51  fd_pseudo:                              0
% 39.65/5.51  fd_cond:                                0
% 39.65/5.51  fd_pseudo_cond:                         1
% 39.65/5.51  ac_symbols:                             0
% 39.65/5.51  
% 39.65/5.51  ------ Propositional Solver
% 39.65/5.51  
% 39.65/5.51  prop_solver_calls:                      38
% 39.65/5.51  prop_fast_solver_calls:                 1719
% 39.65/5.51  smt_solver_calls:                       0
% 39.65/5.51  smt_fast_solver_calls:                  0
% 39.65/5.51  prop_num_of_clauses:                    37506
% 39.65/5.51  prop_preprocess_simplified:             39953
% 39.65/5.51  prop_fo_subsumed:                       50
% 39.65/5.51  prop_solver_time:                       0.
% 39.65/5.51  smt_solver_time:                        0.
% 39.65/5.51  smt_fast_solver_time:                   0.
% 39.65/5.51  prop_fast_solver_time:                  0.
% 39.65/5.51  prop_unsat_core_time:                   0.007
% 39.65/5.51  
% 39.65/5.51  ------ QBF
% 39.65/5.51  
% 39.65/5.51  qbf_q_res:                              0
% 39.65/5.51  qbf_num_tautologies:                    0
% 39.65/5.51  qbf_prep_cycles:                        0
% 39.65/5.51  
% 39.65/5.51  ------ BMC1
% 39.65/5.51  
% 39.65/5.51  bmc1_current_bound:                     -1
% 39.65/5.51  bmc1_last_solved_bound:                 -1
% 39.65/5.51  bmc1_unsat_core_size:                   -1
% 39.65/5.51  bmc1_unsat_core_parents_size:           -1
% 39.65/5.51  bmc1_merge_next_fun:                    0
% 39.65/5.51  bmc1_unsat_core_clauses_time:           0.
% 39.65/5.51  
% 39.65/5.51  ------ Instantiation
% 39.65/5.51  
% 39.65/5.51  inst_num_of_clauses:                    6313
% 39.65/5.51  inst_num_in_passive:                    1485
% 39.65/5.51  inst_num_in_active:                     1843
% 39.65/5.51  inst_num_in_unprocessed:                2985
% 39.65/5.51  inst_num_of_loops:                      1980
% 39.65/5.51  inst_num_of_learning_restarts:          0
% 39.65/5.51  inst_num_moves_active_passive:          135
% 39.65/5.51  inst_lit_activity:                      0
% 39.65/5.51  inst_lit_activity_moves:                1
% 39.65/5.51  inst_num_tautologies:                   0
% 39.65/5.51  inst_num_prop_implied:                  0
% 39.65/5.51  inst_num_existing_simplified:           0
% 39.65/5.51  inst_num_eq_res_simplified:             0
% 39.65/5.51  inst_num_child_elim:                    0
% 39.65/5.51  inst_num_of_dismatching_blockings:      4430
% 39.65/5.51  inst_num_of_non_proper_insts:           7380
% 39.65/5.51  inst_num_of_duplicates:                 0
% 39.65/5.51  inst_inst_num_from_inst_to_res:         0
% 39.65/5.51  inst_dismatching_checking_time:         0.
% 39.65/5.51  
% 39.65/5.51  ------ Resolution
% 39.65/5.51  
% 39.65/5.51  res_num_of_clauses:                     0
% 39.65/5.51  res_num_in_passive:                     0
% 39.65/5.51  res_num_in_active:                      0
% 39.65/5.51  res_num_of_loops:                       99
% 39.65/5.51  res_forward_subset_subsumed:            906
% 39.65/5.51  res_backward_subset_subsumed:           2
% 39.65/5.51  res_forward_subsumed:                   0
% 39.65/5.51  res_backward_subsumed:                  0
% 39.65/5.51  res_forward_subsumption_resolution:     1
% 39.65/5.51  res_backward_subsumption_resolution:    0
% 39.65/5.51  res_clause_to_clause_subsumption:       49330
% 39.65/5.51  res_orphan_elimination:                 0
% 39.65/5.51  res_tautology_del:                      788
% 39.65/5.51  res_num_eq_res_simplified:              0
% 39.65/5.51  res_num_sel_changes:                    0
% 39.65/5.51  res_moves_from_active_to_pass:          0
% 39.65/5.51  
% 39.65/5.51  ------ Superposition
% 39.65/5.51  
% 39.65/5.51  sup_time_total:                         0.
% 39.65/5.51  sup_time_generating:                    0.
% 39.65/5.51  sup_time_sim_full:                      0.
% 39.65/5.51  sup_time_sim_immed:                     0.
% 39.65/5.51  
% 39.65/5.51  sup_num_of_clauses:                     4871
% 39.65/5.51  sup_num_in_active:                      366
% 39.65/5.51  sup_num_in_passive:                     4505
% 39.65/5.51  sup_num_of_loops:                       394
% 39.65/5.51  sup_fw_superposition:                   4281
% 39.65/5.51  sup_bw_superposition:                   3029
% 39.65/5.51  sup_immediate_simplified:               2424
% 39.65/5.51  sup_given_eliminated:                   5
% 39.65/5.51  comparisons_done:                       0
% 39.65/5.51  comparisons_avoided:                    0
% 39.65/5.51  
% 39.65/5.51  ------ Simplifications
% 39.65/5.51  
% 39.65/5.51  
% 39.65/5.51  sim_fw_subset_subsumed:                 286
% 39.65/5.51  sim_bw_subset_subsumed:                 71
% 39.65/5.51  sim_fw_subsumed:                        761
% 39.65/5.51  sim_bw_subsumed:                        113
% 39.65/5.51  sim_fw_subsumption_res:                 0
% 39.65/5.51  sim_bw_subsumption_res:                 0
% 39.65/5.51  sim_tautology_del:                      159
% 39.65/5.51  sim_eq_tautology_del:                   125
% 39.65/5.51  sim_eq_res_simp:                        0
% 39.65/5.51  sim_fw_demodulated:                     988
% 39.65/5.51  sim_bw_demodulated:                     36
% 39.65/5.51  sim_light_normalised:                   720
% 39.65/5.51  sim_joinable_taut:                      0
% 39.65/5.51  sim_joinable_simp:                      0
% 39.65/5.51  sim_ac_normalised:                      0
% 39.65/5.51  sim_smt_subsumption:                    0
% 39.65/5.51  
%------------------------------------------------------------------------------
