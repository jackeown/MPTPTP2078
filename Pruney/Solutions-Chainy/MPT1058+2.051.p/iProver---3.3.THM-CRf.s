%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:09:20 EST 2020

% Result     : Theorem 28.02s
% Output     : CNFRefutation 28.02s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 496 expanded)
%              Number of clauses        :   68 ( 184 expanded)
%              Number of leaves         :   18 ( 120 expanded)
%              Depth                    :   20
%              Number of atoms          :  249 ( 811 expanded)
%              Number of equality atoms :  131 ( 468 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(k10_relat_1(X0,X2),X1)
         => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_tarski(k10_relat_1(X0,X2),X1)
           => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
     => ( k10_relat_1(X0,sK2) != k10_relat_1(k7_relat_1(X0,sK1),sK2)
        & r1_tarski(k10_relat_1(X0,sK2),sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
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

fof(f35,plain,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    & r1_tarski(k10_relat_1(sK0,sK2),sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f34,f33])).

fof(f57,plain,(
    r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f36,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f59,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f43,f42])).

fof(f60,plain,(
    ! [X0] : k1_setfam_1(k1_enumset1(X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f36,f59])).

fof(f15,axiom,(
    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f64,plain,(
    ! [X0,X1] : k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(definition_unfolding,[],[f54,f59])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f9,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f50,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f46,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f31])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f66,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f37])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(X2,X1))) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f51,f59])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(X1,k1_relat_1(X1)))) = k9_relat_1(X1,k10_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f52,f59])).

fof(f39,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f61,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f40,f59])).

fof(f55,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f58,plain,(
    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_18,negated_conjecture,
    ( r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_495,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_0,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_16,plain,
    ( k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_12,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_269,plain,
    ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
    | k6_relat_1(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_12])).

cnf(c_270,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(unflattening,[status(thm)],[c_269])).

cnf(c_527,plain,
    ( k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(demodulation,[status(thm)],[c_16,c_270])).

cnf(c_1897,plain,
    ( k7_relat_1(k6_relat_1(X0),X0) = k6_relat_1(X0) ),
    inference(superposition,[status(thm)],[c_0,c_527])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_284,plain,
    ( k6_relat_1(X0) != X1
    | k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2) ),
    inference(resolution_lifted,[status(thm)],[c_6,c_12])).

cnf(c_285,plain,
    ( k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1) ),
    inference(unflattening,[status(thm)],[c_284])).

cnf(c_2853,plain,
    ( k9_relat_1(k6_relat_1(X0),X0) = k2_relat_1(k6_relat_1(X0)) ),
    inference(superposition,[status(thm)],[c_1897,c_285])).

cnf(c_8,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2867,plain,
    ( k9_relat_1(k6_relat_1(X0),X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2853,c_8])).

cnf(c_11,plain,
    ( v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_15,plain,
    ( r1_tarski(X0,k10_relat_1(X1,X2))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ r1_tarski(k9_relat_1(X1,X0),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_190,plain,
    ( r1_tarski(X0,k10_relat_1(X1,X2))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ r1_tarski(k9_relat_1(X1,X0),X2)
    | ~ v1_relat_1(X1)
    | k6_relat_1(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_15])).

cnf(c_191,plain,
    ( r1_tarski(X0,k10_relat_1(k6_relat_1(X1),X2))
    | ~ r1_tarski(X0,k1_relat_1(k6_relat_1(X1)))
    | ~ r1_tarski(k9_relat_1(k6_relat_1(X1),X0),X2)
    | ~ v1_relat_1(k6_relat_1(X1)) ),
    inference(unflattening,[status(thm)],[c_190])).

cnf(c_203,plain,
    ( r1_tarski(X0,k10_relat_1(k6_relat_1(X1),X2))
    | ~ r1_tarski(X0,k1_relat_1(k6_relat_1(X1)))
    | ~ r1_tarski(k9_relat_1(k6_relat_1(X1),X0),X2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_191,c_12])).

cnf(c_494,plain,
    ( r1_tarski(X0,k10_relat_1(k6_relat_1(X1),X2)) = iProver_top
    | r1_tarski(X0,k1_relat_1(k6_relat_1(X1))) != iProver_top
    | r1_tarski(k9_relat_1(k6_relat_1(X1),X0),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_203])).

cnf(c_9,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_557,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k10_relat_1(k6_relat_1(X1),X2)) = iProver_top
    | r1_tarski(k9_relat_1(k6_relat_1(X1),X0),X2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_494,c_9])).

cnf(c_6043,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X0) != iProver_top
    | r1_tarski(X0,k10_relat_1(k6_relat_1(X0),X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2867,c_557])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_55,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_48742,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k10_relat_1(k6_relat_1(X0),X1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6043,c_55])).

cnf(c_1904,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(superposition,[status(thm)],[c_527,c_8])).

cnf(c_3012,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k9_relat_1(k6_relat_1(X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_1904,c_285])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k1_enumset1(X1,X1,k10_relat_1(X0,X2))) = k10_relat_1(k7_relat_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_263,plain,
    ( k6_relat_1(X0) != X1
    | k1_setfam_1(k1_enumset1(X2,X2,k10_relat_1(X1,X3))) = k10_relat_1(k7_relat_1(X1,X2),X3) ),
    inference(resolution_lifted,[status(thm)],[c_13,c_12])).

cnf(c_264,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(k6_relat_1(X1),X2))) = k10_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2) ),
    inference(unflattening,[status(thm)],[c_263])).

cnf(c_3045,plain,
    ( k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X1),X2)) = k10_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2) ),
    inference(superposition,[status(thm)],[c_3012,c_264])).

cnf(c_14,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_setfam_1(k1_enumset1(X1,X1,k9_relat_1(X0,k1_relat_1(X0)))) = k9_relat_1(X0,k10_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_210,plain,
    ( ~ v1_relat_1(X0)
    | k6_relat_1(X1) != X0
    | k1_setfam_1(k1_enumset1(X2,X2,k9_relat_1(X0,k1_relat_1(X0)))) = k9_relat_1(X0,k10_relat_1(X0,X2)) ),
    inference(resolution_lifted,[status(thm)],[c_11,c_14])).

cnf(c_211,plain,
    ( ~ v1_relat_1(k6_relat_1(X0))
    | k1_setfam_1(k1_enumset1(X1,X1,k9_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0))))) = k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) ),
    inference(unflattening,[status(thm)],[c_210])).

cnf(c_215,plain,
    ( k1_setfam_1(k1_enumset1(X1,X1,k9_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0))))) = k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_211,c_12])).

cnf(c_216,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(k6_relat_1(X1),k1_relat_1(k6_relat_1(X1))))) = k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X0)) ),
    inference(renaming,[status(thm)],[c_215])).

cnf(c_542,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(k6_relat_1(X1),X1))) = k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X0)) ),
    inference(demodulation,[status(thm)],[c_216,c_9])).

cnf(c_4624,plain,
    ( k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X1),X0) ),
    inference(demodulation,[status(thm)],[c_542,c_2867,c_3012])).

cnf(c_31320,plain,
    ( k10_relat_1(k7_relat_1(k6_relat_1(X0),X0),X1) = k9_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[status(thm)],[c_3045,c_4624])).

cnf(c_31360,plain,
    ( k10_relat_1(k6_relat_1(X0),X1) = k9_relat_1(k6_relat_1(X1),X0) ),
    inference(light_normalisation,[status(thm)],[c_31320,c_1897])).

cnf(c_48746,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k9_relat_1(k6_relat_1(X1),X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_48742,c_31360])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_499,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_48757,plain,
    ( k9_relat_1(k6_relat_1(X0),X1) = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(k9_relat_1(k6_relat_1(X0),X1),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_48746,c_499])).

cnf(c_4,plain,
    ( r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_497,plain,
    ( r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3020,plain,
    ( r1_tarski(k9_relat_1(k6_relat_1(X0),X1),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3012,c_497])).

cnf(c_6316,plain,
    ( r1_tarski(k9_relat_1(k6_relat_1(X0),X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_4624,c_3020])).

cnf(c_106305,plain,
    ( r1_tarski(X1,X0) != iProver_top
    | k9_relat_1(k6_relat_1(X0),X1) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_48757,c_6316])).

cnf(c_106306,plain,
    ( k9_relat_1(k6_relat_1(X0),X1) = X1
    | r1_tarski(X1,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_106305])).

cnf(c_106312,plain,
    ( k9_relat_1(k6_relat_1(sK1),k10_relat_1(sK0,sK2)) = k10_relat_1(sK0,sK2) ),
    inference(superposition,[status(thm)],[c_495,c_106306])).

cnf(c_20,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_290,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(X1,X2))) = k10_relat_1(k7_relat_1(X1,X0),X2)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_20])).

cnf(c_291,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(sK0,X1))) = k10_relat_1(k7_relat_1(sK0,X0),X1) ),
    inference(unflattening,[status(thm)],[c_290])).

cnf(c_1900,plain,
    ( k6_relat_1(k10_relat_1(k7_relat_1(sK0,X0),X1)) = k7_relat_1(k6_relat_1(X0),k10_relat_1(sK0,X1)) ),
    inference(superposition,[status(thm)],[c_291,c_527])).

cnf(c_2855,plain,
    ( k2_relat_1(k6_relat_1(k10_relat_1(k7_relat_1(sK0,X0),X1))) = k9_relat_1(k6_relat_1(X0),k10_relat_1(sK0,X1)) ),
    inference(superposition,[status(thm)],[c_1900,c_285])).

cnf(c_2861,plain,
    ( k9_relat_1(k6_relat_1(X0),k10_relat_1(sK0,X1)) = k10_relat_1(k7_relat_1(sK0,X0),X1) ),
    inference(demodulation,[status(thm)],[c_2855,c_8])).

cnf(c_107328,plain,
    ( k10_relat_1(k7_relat_1(sK0,sK1),sK2) = k10_relat_1(sK0,sK2) ),
    inference(superposition,[status(thm)],[c_106312,c_2861])).

cnf(c_328,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_687,plain,
    ( k10_relat_1(sK0,sK2) = k10_relat_1(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_328])).

cnf(c_329,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_623,plain,
    ( k10_relat_1(k7_relat_1(sK0,sK1),sK2) != X0
    | k10_relat_1(sK0,sK2) != X0
    | k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(instantiation,[status(thm)],[c_329])).

cnf(c_686,plain,
    ( k10_relat_1(k7_relat_1(sK0,sK1),sK2) != k10_relat_1(sK0,sK2)
    | k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    | k10_relat_1(sK0,sK2) != k10_relat_1(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_623])).

cnf(c_17,negated_conjecture,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_107328,c_687,c_686,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:41:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 28.02/4.03  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 28.02/4.03  
% 28.02/4.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 28.02/4.03  
% 28.02/4.03  ------  iProver source info
% 28.02/4.03  
% 28.02/4.03  git: date: 2020-06-30 10:37:57 +0100
% 28.02/4.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 28.02/4.03  git: non_committed_changes: false
% 28.02/4.03  git: last_make_outside_of_git: false
% 28.02/4.03  
% 28.02/4.03  ------ 
% 28.02/4.03  
% 28.02/4.03  ------ Input Options
% 28.02/4.03  
% 28.02/4.03  --out_options                           all
% 28.02/4.03  --tptp_safe_out                         true
% 28.02/4.03  --problem_path                          ""
% 28.02/4.03  --include_path                          ""
% 28.02/4.03  --clausifier                            res/vclausify_rel
% 28.02/4.03  --clausifier_options                    --mode clausify
% 28.02/4.03  --stdin                                 false
% 28.02/4.03  --stats_out                             all
% 28.02/4.03  
% 28.02/4.03  ------ General Options
% 28.02/4.03  
% 28.02/4.03  --fof                                   false
% 28.02/4.03  --time_out_real                         305.
% 28.02/4.03  --time_out_virtual                      -1.
% 28.02/4.03  --symbol_type_check                     false
% 28.02/4.03  --clausify_out                          false
% 28.02/4.03  --sig_cnt_out                           false
% 28.02/4.03  --trig_cnt_out                          false
% 28.02/4.03  --trig_cnt_out_tolerance                1.
% 28.02/4.03  --trig_cnt_out_sk_spl                   false
% 28.02/4.03  --abstr_cl_out                          false
% 28.02/4.03  
% 28.02/4.03  ------ Global Options
% 28.02/4.03  
% 28.02/4.03  --schedule                              default
% 28.02/4.03  --add_important_lit                     false
% 28.02/4.03  --prop_solver_per_cl                    1000
% 28.02/4.03  --min_unsat_core                        false
% 28.02/4.03  --soft_assumptions                      false
% 28.02/4.03  --soft_lemma_size                       3
% 28.02/4.03  --prop_impl_unit_size                   0
% 28.02/4.03  --prop_impl_unit                        []
% 28.02/4.03  --share_sel_clauses                     true
% 28.02/4.03  --reset_solvers                         false
% 28.02/4.03  --bc_imp_inh                            [conj_cone]
% 28.02/4.03  --conj_cone_tolerance                   3.
% 28.02/4.03  --extra_neg_conj                        none
% 28.02/4.03  --large_theory_mode                     true
% 28.02/4.03  --prolific_symb_bound                   200
% 28.02/4.03  --lt_threshold                          2000
% 28.02/4.03  --clause_weak_htbl                      true
% 28.02/4.03  --gc_record_bc_elim                     false
% 28.02/4.03  
% 28.02/4.03  ------ Preprocessing Options
% 28.02/4.03  
% 28.02/4.03  --preprocessing_flag                    true
% 28.02/4.03  --time_out_prep_mult                    0.1
% 28.02/4.03  --splitting_mode                        input
% 28.02/4.03  --splitting_grd                         true
% 28.02/4.03  --splitting_cvd                         false
% 28.02/4.03  --splitting_cvd_svl                     false
% 28.02/4.03  --splitting_nvd                         32
% 28.02/4.03  --sub_typing                            true
% 28.02/4.03  --prep_gs_sim                           true
% 28.02/4.03  --prep_unflatten                        true
% 28.02/4.03  --prep_res_sim                          true
% 28.02/4.03  --prep_upred                            true
% 28.02/4.03  --prep_sem_filter                       exhaustive
% 28.02/4.03  --prep_sem_filter_out                   false
% 28.02/4.03  --pred_elim                             true
% 28.02/4.03  --res_sim_input                         true
% 28.02/4.03  --eq_ax_congr_red                       true
% 28.02/4.03  --pure_diseq_elim                       true
% 28.02/4.03  --brand_transform                       false
% 28.02/4.03  --non_eq_to_eq                          false
% 28.02/4.03  --prep_def_merge                        true
% 28.02/4.03  --prep_def_merge_prop_impl              false
% 28.02/4.03  --prep_def_merge_mbd                    true
% 28.02/4.03  --prep_def_merge_tr_red                 false
% 28.02/4.03  --prep_def_merge_tr_cl                  false
% 28.02/4.03  --smt_preprocessing                     true
% 28.02/4.03  --smt_ac_axioms                         fast
% 28.02/4.03  --preprocessed_out                      false
% 28.02/4.03  --preprocessed_stats                    false
% 28.02/4.03  
% 28.02/4.03  ------ Abstraction refinement Options
% 28.02/4.03  
% 28.02/4.03  --abstr_ref                             []
% 28.02/4.03  --abstr_ref_prep                        false
% 28.02/4.03  --abstr_ref_until_sat                   false
% 28.02/4.03  --abstr_ref_sig_restrict                funpre
% 28.02/4.03  --abstr_ref_af_restrict_to_split_sk     false
% 28.02/4.03  --abstr_ref_under                       []
% 28.02/4.03  
% 28.02/4.03  ------ SAT Options
% 28.02/4.03  
% 28.02/4.03  --sat_mode                              false
% 28.02/4.03  --sat_fm_restart_options                ""
% 28.02/4.03  --sat_gr_def                            false
% 28.02/4.03  --sat_epr_types                         true
% 28.02/4.03  --sat_non_cyclic_types                  false
% 28.02/4.03  --sat_finite_models                     false
% 28.02/4.03  --sat_fm_lemmas                         false
% 28.02/4.03  --sat_fm_prep                           false
% 28.02/4.03  --sat_fm_uc_incr                        true
% 28.02/4.03  --sat_out_model                         small
% 28.02/4.03  --sat_out_clauses                       false
% 28.02/4.03  
% 28.02/4.03  ------ QBF Options
% 28.02/4.03  
% 28.02/4.03  --qbf_mode                              false
% 28.02/4.03  --qbf_elim_univ                         false
% 28.02/4.03  --qbf_dom_inst                          none
% 28.02/4.03  --qbf_dom_pre_inst                      false
% 28.02/4.03  --qbf_sk_in                             false
% 28.02/4.03  --qbf_pred_elim                         true
% 28.02/4.03  --qbf_split                             512
% 28.02/4.03  
% 28.02/4.03  ------ BMC1 Options
% 28.02/4.03  
% 28.02/4.03  --bmc1_incremental                      false
% 28.02/4.03  --bmc1_axioms                           reachable_all
% 28.02/4.03  --bmc1_min_bound                        0
% 28.02/4.03  --bmc1_max_bound                        -1
% 28.02/4.03  --bmc1_max_bound_default                -1
% 28.02/4.03  --bmc1_symbol_reachability              true
% 28.02/4.03  --bmc1_property_lemmas                  false
% 28.02/4.03  --bmc1_k_induction                      false
% 28.02/4.03  --bmc1_non_equiv_states                 false
% 28.02/4.03  --bmc1_deadlock                         false
% 28.02/4.03  --bmc1_ucm                              false
% 28.02/4.03  --bmc1_add_unsat_core                   none
% 28.02/4.03  --bmc1_unsat_core_children              false
% 28.02/4.03  --bmc1_unsat_core_extrapolate_axioms    false
% 28.02/4.03  --bmc1_out_stat                         full
% 28.02/4.03  --bmc1_ground_init                      false
% 28.02/4.03  --bmc1_pre_inst_next_state              false
% 28.02/4.03  --bmc1_pre_inst_state                   false
% 28.02/4.03  --bmc1_pre_inst_reach_state             false
% 28.02/4.03  --bmc1_out_unsat_core                   false
% 28.02/4.03  --bmc1_aig_witness_out                  false
% 28.02/4.03  --bmc1_verbose                          false
% 28.02/4.03  --bmc1_dump_clauses_tptp                false
% 28.02/4.03  --bmc1_dump_unsat_core_tptp             false
% 28.02/4.03  --bmc1_dump_file                        -
% 28.02/4.03  --bmc1_ucm_expand_uc_limit              128
% 28.02/4.03  --bmc1_ucm_n_expand_iterations          6
% 28.02/4.03  --bmc1_ucm_extend_mode                  1
% 28.02/4.03  --bmc1_ucm_init_mode                    2
% 28.02/4.03  --bmc1_ucm_cone_mode                    none
% 28.02/4.03  --bmc1_ucm_reduced_relation_type        0
% 28.02/4.03  --bmc1_ucm_relax_model                  4
% 28.02/4.03  --bmc1_ucm_full_tr_after_sat            true
% 28.02/4.03  --bmc1_ucm_expand_neg_assumptions       false
% 28.02/4.03  --bmc1_ucm_layered_model                none
% 28.02/4.03  --bmc1_ucm_max_lemma_size               10
% 28.02/4.03  
% 28.02/4.03  ------ AIG Options
% 28.02/4.03  
% 28.02/4.03  --aig_mode                              false
% 28.02/4.03  
% 28.02/4.03  ------ Instantiation Options
% 28.02/4.03  
% 28.02/4.03  --instantiation_flag                    true
% 28.02/4.03  --inst_sos_flag                         false
% 28.02/4.03  --inst_sos_phase                        true
% 28.02/4.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 28.02/4.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 28.02/4.03  --inst_lit_sel_side                     num_symb
% 28.02/4.03  --inst_solver_per_active                1400
% 28.02/4.03  --inst_solver_calls_frac                1.
% 28.02/4.03  --inst_passive_queue_type               priority_queues
% 28.02/4.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 28.02/4.03  --inst_passive_queues_freq              [25;2]
% 28.02/4.03  --inst_dismatching                      true
% 28.02/4.03  --inst_eager_unprocessed_to_passive     true
% 28.02/4.03  --inst_prop_sim_given                   true
% 28.02/4.03  --inst_prop_sim_new                     false
% 28.02/4.03  --inst_subs_new                         false
% 28.02/4.03  --inst_eq_res_simp                      false
% 28.02/4.03  --inst_subs_given                       false
% 28.02/4.03  --inst_orphan_elimination               true
% 28.02/4.03  --inst_learning_loop_flag               true
% 28.02/4.03  --inst_learning_start                   3000
% 28.02/4.03  --inst_learning_factor                  2
% 28.02/4.03  --inst_start_prop_sim_after_learn       3
% 28.02/4.03  --inst_sel_renew                        solver
% 28.02/4.03  --inst_lit_activity_flag                true
% 28.02/4.03  --inst_restr_to_given                   false
% 28.02/4.03  --inst_activity_threshold               500
% 28.02/4.03  --inst_out_proof                        true
% 28.02/4.03  
% 28.02/4.03  ------ Resolution Options
% 28.02/4.03  
% 28.02/4.03  --resolution_flag                       true
% 28.02/4.03  --res_lit_sel                           adaptive
% 28.02/4.03  --res_lit_sel_side                      none
% 28.02/4.03  --res_ordering                          kbo
% 28.02/4.03  --res_to_prop_solver                    active
% 28.02/4.03  --res_prop_simpl_new                    false
% 28.02/4.03  --res_prop_simpl_given                  true
% 28.02/4.03  --res_passive_queue_type                priority_queues
% 28.02/4.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 28.02/4.03  --res_passive_queues_freq               [15;5]
% 28.02/4.03  --res_forward_subs                      full
% 28.02/4.03  --res_backward_subs                     full
% 28.02/4.03  --res_forward_subs_resolution           true
% 28.02/4.03  --res_backward_subs_resolution          true
% 28.02/4.03  --res_orphan_elimination                true
% 28.02/4.03  --res_time_limit                        2.
% 28.02/4.03  --res_out_proof                         true
% 28.02/4.03  
% 28.02/4.03  ------ Superposition Options
% 28.02/4.03  
% 28.02/4.03  --superposition_flag                    true
% 28.02/4.03  --sup_passive_queue_type                priority_queues
% 28.02/4.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 28.02/4.03  --sup_passive_queues_freq               [8;1;4]
% 28.02/4.03  --demod_completeness_check              fast
% 28.02/4.03  --demod_use_ground                      true
% 28.02/4.03  --sup_to_prop_solver                    passive
% 28.02/4.03  --sup_prop_simpl_new                    true
% 28.02/4.03  --sup_prop_simpl_given                  true
% 28.02/4.03  --sup_fun_splitting                     false
% 28.02/4.03  --sup_smt_interval                      50000
% 28.02/4.03  
% 28.02/4.03  ------ Superposition Simplification Setup
% 28.02/4.03  
% 28.02/4.03  --sup_indices_passive                   []
% 28.02/4.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 28.02/4.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 28.02/4.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 28.02/4.03  --sup_full_triv                         [TrivRules;PropSubs]
% 28.02/4.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 28.02/4.03  --sup_full_bw                           [BwDemod]
% 28.02/4.03  --sup_immed_triv                        [TrivRules]
% 28.02/4.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 28.02/4.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 28.02/4.03  --sup_immed_bw_main                     []
% 28.02/4.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 28.02/4.03  --sup_input_triv                        [Unflattening;TrivRules]
% 28.02/4.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 28.02/4.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 28.02/4.03  
% 28.02/4.03  ------ Combination Options
% 28.02/4.03  
% 28.02/4.03  --comb_res_mult                         3
% 28.02/4.03  --comb_sup_mult                         2
% 28.02/4.03  --comb_inst_mult                        10
% 28.02/4.03  
% 28.02/4.03  ------ Debug Options
% 28.02/4.03  
% 28.02/4.03  --dbg_backtrace                         false
% 28.02/4.03  --dbg_dump_prop_clauses                 false
% 28.02/4.03  --dbg_dump_prop_clauses_file            -
% 28.02/4.03  --dbg_out_stat                          false
% 28.02/4.03  ------ Parsing...
% 28.02/4.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 28.02/4.03  
% 28.02/4.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 28.02/4.03  
% 28.02/4.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 28.02/4.03  
% 28.02/4.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 28.02/4.03  ------ Proving...
% 28.02/4.03  ------ Problem Properties 
% 28.02/4.03  
% 28.02/4.03  
% 28.02/4.03  clauses                                 22
% 28.02/4.03  conjectures                             2
% 28.02/4.03  EPR                                     3
% 28.02/4.03  Horn                                    22
% 28.02/4.03  unary                                   18
% 28.02/4.03  binary                                  0
% 28.02/4.03  lits                                    30
% 28.02/4.03  lits eq                                 14
% 28.02/4.03  fd_pure                                 0
% 28.02/4.03  fd_pseudo                               0
% 28.02/4.03  fd_cond                                 0
% 28.02/4.03  fd_pseudo_cond                          1
% 28.02/4.03  AC symbols                              0
% 28.02/4.03  
% 28.02/4.03  ------ Schedule dynamic 5 is on 
% 28.02/4.03  
% 28.02/4.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 28.02/4.03  
% 28.02/4.03  
% 28.02/4.03  ------ 
% 28.02/4.03  Current options:
% 28.02/4.03  ------ 
% 28.02/4.03  
% 28.02/4.03  ------ Input Options
% 28.02/4.03  
% 28.02/4.03  --out_options                           all
% 28.02/4.03  --tptp_safe_out                         true
% 28.02/4.03  --problem_path                          ""
% 28.02/4.03  --include_path                          ""
% 28.02/4.03  --clausifier                            res/vclausify_rel
% 28.02/4.03  --clausifier_options                    --mode clausify
% 28.02/4.03  --stdin                                 false
% 28.02/4.03  --stats_out                             all
% 28.02/4.03  
% 28.02/4.03  ------ General Options
% 28.02/4.03  
% 28.02/4.03  --fof                                   false
% 28.02/4.03  --time_out_real                         305.
% 28.02/4.03  --time_out_virtual                      -1.
% 28.02/4.03  --symbol_type_check                     false
% 28.02/4.03  --clausify_out                          false
% 28.02/4.03  --sig_cnt_out                           false
% 28.02/4.03  --trig_cnt_out                          false
% 28.02/4.03  --trig_cnt_out_tolerance                1.
% 28.02/4.03  --trig_cnt_out_sk_spl                   false
% 28.02/4.03  --abstr_cl_out                          false
% 28.02/4.03  
% 28.02/4.03  ------ Global Options
% 28.02/4.03  
% 28.02/4.03  --schedule                              default
% 28.02/4.03  --add_important_lit                     false
% 28.02/4.03  --prop_solver_per_cl                    1000
% 28.02/4.03  --min_unsat_core                        false
% 28.02/4.03  --soft_assumptions                      false
% 28.02/4.03  --soft_lemma_size                       3
% 28.02/4.03  --prop_impl_unit_size                   0
% 28.02/4.03  --prop_impl_unit                        []
% 28.02/4.03  --share_sel_clauses                     true
% 28.02/4.03  --reset_solvers                         false
% 28.02/4.03  --bc_imp_inh                            [conj_cone]
% 28.02/4.03  --conj_cone_tolerance                   3.
% 28.02/4.03  --extra_neg_conj                        none
% 28.02/4.03  --large_theory_mode                     true
% 28.02/4.03  --prolific_symb_bound                   200
% 28.02/4.03  --lt_threshold                          2000
% 28.02/4.03  --clause_weak_htbl                      true
% 28.02/4.03  --gc_record_bc_elim                     false
% 28.02/4.03  
% 28.02/4.03  ------ Preprocessing Options
% 28.02/4.03  
% 28.02/4.03  --preprocessing_flag                    true
% 28.02/4.03  --time_out_prep_mult                    0.1
% 28.02/4.03  --splitting_mode                        input
% 28.02/4.03  --splitting_grd                         true
% 28.02/4.03  --splitting_cvd                         false
% 28.02/4.03  --splitting_cvd_svl                     false
% 28.02/4.03  --splitting_nvd                         32
% 28.02/4.03  --sub_typing                            true
% 28.02/4.03  --prep_gs_sim                           true
% 28.02/4.03  --prep_unflatten                        true
% 28.02/4.03  --prep_res_sim                          true
% 28.02/4.03  --prep_upred                            true
% 28.02/4.03  --prep_sem_filter                       exhaustive
% 28.02/4.03  --prep_sem_filter_out                   false
% 28.02/4.03  --pred_elim                             true
% 28.02/4.03  --res_sim_input                         true
% 28.02/4.03  --eq_ax_congr_red                       true
% 28.02/4.03  --pure_diseq_elim                       true
% 28.02/4.03  --brand_transform                       false
% 28.02/4.03  --non_eq_to_eq                          false
% 28.02/4.03  --prep_def_merge                        true
% 28.02/4.03  --prep_def_merge_prop_impl              false
% 28.02/4.03  --prep_def_merge_mbd                    true
% 28.02/4.03  --prep_def_merge_tr_red                 false
% 28.02/4.03  --prep_def_merge_tr_cl                  false
% 28.02/4.03  --smt_preprocessing                     true
% 28.02/4.03  --smt_ac_axioms                         fast
% 28.02/4.03  --preprocessed_out                      false
% 28.02/4.03  --preprocessed_stats                    false
% 28.02/4.03  
% 28.02/4.03  ------ Abstraction refinement Options
% 28.02/4.03  
% 28.02/4.03  --abstr_ref                             []
% 28.02/4.03  --abstr_ref_prep                        false
% 28.02/4.03  --abstr_ref_until_sat                   false
% 28.02/4.03  --abstr_ref_sig_restrict                funpre
% 28.02/4.03  --abstr_ref_af_restrict_to_split_sk     false
% 28.02/4.03  --abstr_ref_under                       []
% 28.02/4.03  
% 28.02/4.03  ------ SAT Options
% 28.02/4.03  
% 28.02/4.03  --sat_mode                              false
% 28.02/4.03  --sat_fm_restart_options                ""
% 28.02/4.03  --sat_gr_def                            false
% 28.02/4.03  --sat_epr_types                         true
% 28.02/4.03  --sat_non_cyclic_types                  false
% 28.02/4.03  --sat_finite_models                     false
% 28.02/4.03  --sat_fm_lemmas                         false
% 28.02/4.03  --sat_fm_prep                           false
% 28.02/4.03  --sat_fm_uc_incr                        true
% 28.02/4.03  --sat_out_model                         small
% 28.02/4.03  --sat_out_clauses                       false
% 28.02/4.03  
% 28.02/4.03  ------ QBF Options
% 28.02/4.03  
% 28.02/4.03  --qbf_mode                              false
% 28.02/4.03  --qbf_elim_univ                         false
% 28.02/4.03  --qbf_dom_inst                          none
% 28.02/4.03  --qbf_dom_pre_inst                      false
% 28.02/4.03  --qbf_sk_in                             false
% 28.02/4.03  --qbf_pred_elim                         true
% 28.02/4.03  --qbf_split                             512
% 28.02/4.03  
% 28.02/4.03  ------ BMC1 Options
% 28.02/4.03  
% 28.02/4.03  --bmc1_incremental                      false
% 28.02/4.03  --bmc1_axioms                           reachable_all
% 28.02/4.03  --bmc1_min_bound                        0
% 28.02/4.03  --bmc1_max_bound                        -1
% 28.02/4.03  --bmc1_max_bound_default                -1
% 28.02/4.03  --bmc1_symbol_reachability              true
% 28.02/4.03  --bmc1_property_lemmas                  false
% 28.02/4.03  --bmc1_k_induction                      false
% 28.02/4.03  --bmc1_non_equiv_states                 false
% 28.02/4.03  --bmc1_deadlock                         false
% 28.02/4.03  --bmc1_ucm                              false
% 28.02/4.03  --bmc1_add_unsat_core                   none
% 28.02/4.03  --bmc1_unsat_core_children              false
% 28.02/4.03  --bmc1_unsat_core_extrapolate_axioms    false
% 28.02/4.03  --bmc1_out_stat                         full
% 28.02/4.03  --bmc1_ground_init                      false
% 28.02/4.03  --bmc1_pre_inst_next_state              false
% 28.02/4.03  --bmc1_pre_inst_state                   false
% 28.02/4.03  --bmc1_pre_inst_reach_state             false
% 28.02/4.03  --bmc1_out_unsat_core                   false
% 28.02/4.03  --bmc1_aig_witness_out                  false
% 28.02/4.03  --bmc1_verbose                          false
% 28.02/4.03  --bmc1_dump_clauses_tptp                false
% 28.02/4.03  --bmc1_dump_unsat_core_tptp             false
% 28.02/4.03  --bmc1_dump_file                        -
% 28.02/4.03  --bmc1_ucm_expand_uc_limit              128
% 28.02/4.03  --bmc1_ucm_n_expand_iterations          6
% 28.02/4.03  --bmc1_ucm_extend_mode                  1
% 28.02/4.03  --bmc1_ucm_init_mode                    2
% 28.02/4.03  --bmc1_ucm_cone_mode                    none
% 28.02/4.03  --bmc1_ucm_reduced_relation_type        0
% 28.02/4.03  --bmc1_ucm_relax_model                  4
% 28.02/4.03  --bmc1_ucm_full_tr_after_sat            true
% 28.02/4.03  --bmc1_ucm_expand_neg_assumptions       false
% 28.02/4.03  --bmc1_ucm_layered_model                none
% 28.02/4.03  --bmc1_ucm_max_lemma_size               10
% 28.02/4.03  
% 28.02/4.03  ------ AIG Options
% 28.02/4.03  
% 28.02/4.03  --aig_mode                              false
% 28.02/4.03  
% 28.02/4.03  ------ Instantiation Options
% 28.02/4.03  
% 28.02/4.03  --instantiation_flag                    true
% 28.02/4.03  --inst_sos_flag                         false
% 28.02/4.03  --inst_sos_phase                        true
% 28.02/4.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 28.02/4.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 28.02/4.03  --inst_lit_sel_side                     none
% 28.02/4.03  --inst_solver_per_active                1400
% 28.02/4.03  --inst_solver_calls_frac                1.
% 28.02/4.03  --inst_passive_queue_type               priority_queues
% 28.02/4.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 28.02/4.03  --inst_passive_queues_freq              [25;2]
% 28.02/4.03  --inst_dismatching                      true
% 28.02/4.03  --inst_eager_unprocessed_to_passive     true
% 28.02/4.03  --inst_prop_sim_given                   true
% 28.02/4.03  --inst_prop_sim_new                     false
% 28.02/4.03  --inst_subs_new                         false
% 28.02/4.03  --inst_eq_res_simp                      false
% 28.02/4.03  --inst_subs_given                       false
% 28.02/4.03  --inst_orphan_elimination               true
% 28.02/4.03  --inst_learning_loop_flag               true
% 28.02/4.03  --inst_learning_start                   3000
% 28.02/4.03  --inst_learning_factor                  2
% 28.02/4.03  --inst_start_prop_sim_after_learn       3
% 28.02/4.03  --inst_sel_renew                        solver
% 28.02/4.03  --inst_lit_activity_flag                true
% 28.02/4.03  --inst_restr_to_given                   false
% 28.02/4.03  --inst_activity_threshold               500
% 28.02/4.03  --inst_out_proof                        true
% 28.02/4.03  
% 28.02/4.03  ------ Resolution Options
% 28.02/4.03  
% 28.02/4.03  --resolution_flag                       false
% 28.02/4.03  --res_lit_sel                           adaptive
% 28.02/4.03  --res_lit_sel_side                      none
% 28.02/4.03  --res_ordering                          kbo
% 28.02/4.03  --res_to_prop_solver                    active
% 28.02/4.03  --res_prop_simpl_new                    false
% 28.02/4.03  --res_prop_simpl_given                  true
% 28.02/4.03  --res_passive_queue_type                priority_queues
% 28.02/4.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 28.02/4.03  --res_passive_queues_freq               [15;5]
% 28.02/4.03  --res_forward_subs                      full
% 28.02/4.03  --res_backward_subs                     full
% 28.02/4.03  --res_forward_subs_resolution           true
% 28.02/4.03  --res_backward_subs_resolution          true
% 28.02/4.03  --res_orphan_elimination                true
% 28.02/4.03  --res_time_limit                        2.
% 28.02/4.03  --res_out_proof                         true
% 28.02/4.03  
% 28.02/4.03  ------ Superposition Options
% 28.02/4.03  
% 28.02/4.03  --superposition_flag                    true
% 28.02/4.03  --sup_passive_queue_type                priority_queues
% 28.02/4.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 28.02/4.03  --sup_passive_queues_freq               [8;1;4]
% 28.02/4.03  --demod_completeness_check              fast
% 28.02/4.03  --demod_use_ground                      true
% 28.02/4.03  --sup_to_prop_solver                    passive
% 28.02/4.03  --sup_prop_simpl_new                    true
% 28.02/4.03  --sup_prop_simpl_given                  true
% 28.02/4.03  --sup_fun_splitting                     false
% 28.02/4.03  --sup_smt_interval                      50000
% 28.02/4.03  
% 28.02/4.03  ------ Superposition Simplification Setup
% 28.02/4.03  
% 28.02/4.03  --sup_indices_passive                   []
% 28.02/4.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 28.02/4.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 28.02/4.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 28.02/4.03  --sup_full_triv                         [TrivRules;PropSubs]
% 28.02/4.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 28.02/4.03  --sup_full_bw                           [BwDemod]
% 28.02/4.03  --sup_immed_triv                        [TrivRules]
% 28.02/4.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 28.02/4.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 28.02/4.03  --sup_immed_bw_main                     []
% 28.02/4.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 28.02/4.03  --sup_input_triv                        [Unflattening;TrivRules]
% 28.02/4.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 28.02/4.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 28.02/4.03  
% 28.02/4.03  ------ Combination Options
% 28.02/4.03  
% 28.02/4.03  --comb_res_mult                         3
% 28.02/4.03  --comb_sup_mult                         2
% 28.02/4.03  --comb_inst_mult                        10
% 28.02/4.03  
% 28.02/4.03  ------ Debug Options
% 28.02/4.03  
% 28.02/4.03  --dbg_backtrace                         false
% 28.02/4.03  --dbg_dump_prop_clauses                 false
% 28.02/4.03  --dbg_dump_prop_clauses_file            -
% 28.02/4.03  --dbg_out_stat                          false
% 28.02/4.03  
% 28.02/4.03  
% 28.02/4.03  
% 28.02/4.03  
% 28.02/4.03  ------ Proving...
% 28.02/4.03  
% 28.02/4.03  
% 28.02/4.03  % SZS status Theorem for theBenchmark.p
% 28.02/4.03  
% 28.02/4.03  % SZS output start CNFRefutation for theBenchmark.p
% 28.02/4.03  
% 28.02/4.03  fof(f16,conjecture,(
% 28.02/4.03    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 28.02/4.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 28.02/4.03  
% 28.02/4.03  fof(f17,negated_conjecture,(
% 28.02/4.03    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 28.02/4.03    inference(negated_conjecture,[],[f16])).
% 28.02/4.03  
% 28.02/4.03  fof(f29,plain,(
% 28.02/4.03    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 28.02/4.03    inference(ennf_transformation,[],[f17])).
% 28.02/4.03  
% 28.02/4.03  fof(f30,plain,(
% 28.02/4.03    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 28.02/4.03    inference(flattening,[],[f29])).
% 28.02/4.03  
% 28.02/4.03  fof(f34,plain,(
% 28.02/4.03    ( ! [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) => (k10_relat_1(X0,sK2) != k10_relat_1(k7_relat_1(X0,sK1),sK2) & r1_tarski(k10_relat_1(X0,sK2),sK1))) )),
% 28.02/4.03    introduced(choice_axiom,[])).
% 28.02/4.03  
% 28.02/4.03  fof(f33,plain,(
% 28.02/4.03    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X2,X1] : (k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(k10_relat_1(sK0,X2),X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 28.02/4.03    introduced(choice_axiom,[])).
% 28.02/4.03  
% 28.02/4.03  fof(f35,plain,(
% 28.02/4.03    (k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(k10_relat_1(sK0,sK2),sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 28.02/4.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f34,f33])).
% 28.02/4.03  
% 28.02/4.03  fof(f57,plain,(
% 28.02/4.03    r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 28.02/4.03    inference(cnf_transformation,[],[f35])).
% 28.02/4.03  
% 28.02/4.03  fof(f1,axiom,(
% 28.02/4.03    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 28.02/4.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 28.02/4.03  
% 28.02/4.03  fof(f18,plain,(
% 28.02/4.03    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 28.02/4.03    inference(rectify,[],[f1])).
% 28.02/4.03  
% 28.02/4.03  fof(f36,plain,(
% 28.02/4.03    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 28.02/4.03    inference(cnf_transformation,[],[f18])).
% 28.02/4.03  
% 28.02/4.03  fof(f6,axiom,(
% 28.02/4.03    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 28.02/4.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 28.02/4.03  
% 28.02/4.03  fof(f43,plain,(
% 28.02/4.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 28.02/4.03    inference(cnf_transformation,[],[f6])).
% 28.02/4.03  
% 28.02/4.03  fof(f5,axiom,(
% 28.02/4.03    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 28.02/4.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 28.02/4.03  
% 28.02/4.03  fof(f42,plain,(
% 28.02/4.03    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 28.02/4.03    inference(cnf_transformation,[],[f5])).
% 28.02/4.03  
% 28.02/4.03  fof(f59,plain,(
% 28.02/4.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 28.02/4.03    inference(definition_unfolding,[],[f43,f42])).
% 28.02/4.03  
% 28.02/4.03  fof(f60,plain,(
% 28.02/4.03    ( ! [X0] : (k1_setfam_1(k1_enumset1(X0,X0,X0)) = X0) )),
% 28.02/4.03    inference(definition_unfolding,[],[f36,f59])).
% 28.02/4.03  
% 28.02/4.03  fof(f15,axiom,(
% 28.02/4.03    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))),
% 28.02/4.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 28.02/4.03  
% 28.02/4.03  fof(f54,plain,(
% 28.02/4.03    ( ! [X0,X1] : (k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) )),
% 28.02/4.03    inference(cnf_transformation,[],[f15])).
% 28.02/4.03  
% 28.02/4.03  fof(f64,plain,(
% 28.02/4.03    ( ! [X0,X1] : (k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) )),
% 28.02/4.03    inference(definition_unfolding,[],[f54,f59])).
% 28.02/4.03  
% 28.02/4.03  fof(f10,axiom,(
% 28.02/4.03    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 28.02/4.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 28.02/4.03  
% 28.02/4.03  fof(f23,plain,(
% 28.02/4.03    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 28.02/4.03    inference(ennf_transformation,[],[f10])).
% 28.02/4.03  
% 28.02/4.03  fof(f48,plain,(
% 28.02/4.03    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 28.02/4.03    inference(cnf_transformation,[],[f23])).
% 28.02/4.03  
% 28.02/4.03  fof(f11,axiom,(
% 28.02/4.03    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 28.02/4.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 28.02/4.03  
% 28.02/4.03  fof(f49,plain,(
% 28.02/4.03    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 28.02/4.03    inference(cnf_transformation,[],[f11])).
% 28.02/4.03  
% 28.02/4.03  fof(f7,axiom,(
% 28.02/4.03    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 28.02/4.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 28.02/4.03  
% 28.02/4.03  fof(f21,plain,(
% 28.02/4.03    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 28.02/4.03    inference(ennf_transformation,[],[f7])).
% 28.02/4.03  
% 28.02/4.03  fof(f44,plain,(
% 28.02/4.03    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 28.02/4.03    inference(cnf_transformation,[],[f21])).
% 28.02/4.03  
% 28.02/4.03  fof(f9,axiom,(
% 28.02/4.03    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 28.02/4.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 28.02/4.03  
% 28.02/4.03  fof(f47,plain,(
% 28.02/4.03    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 28.02/4.03    inference(cnf_transformation,[],[f9])).
% 28.02/4.03  
% 28.02/4.03  fof(f50,plain,(
% 28.02/4.03    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 28.02/4.03    inference(cnf_transformation,[],[f11])).
% 28.02/4.03  
% 28.02/4.03  fof(f14,axiom,(
% 28.02/4.03    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 28.02/4.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 28.02/4.03  
% 28.02/4.03  fof(f27,plain,(
% 28.02/4.03    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 28.02/4.03    inference(ennf_transformation,[],[f14])).
% 28.02/4.03  
% 28.02/4.03  fof(f28,plain,(
% 28.02/4.03    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 28.02/4.03    inference(flattening,[],[f27])).
% 28.02/4.03  
% 28.02/4.03  fof(f53,plain,(
% 28.02/4.03    ( ! [X2,X0,X1] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 28.02/4.03    inference(cnf_transformation,[],[f28])).
% 28.02/4.03  
% 28.02/4.03  fof(f46,plain,(
% 28.02/4.03    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 28.02/4.03    inference(cnf_transformation,[],[f9])).
% 28.02/4.03  
% 28.02/4.03  fof(f2,axiom,(
% 28.02/4.03    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 28.02/4.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 28.02/4.03  
% 28.02/4.03  fof(f31,plain,(
% 28.02/4.03    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 28.02/4.03    inference(nnf_transformation,[],[f2])).
% 28.02/4.03  
% 28.02/4.03  fof(f32,plain,(
% 28.02/4.03    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 28.02/4.03    inference(flattening,[],[f31])).
% 28.02/4.03  
% 28.02/4.03  fof(f37,plain,(
% 28.02/4.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 28.02/4.03    inference(cnf_transformation,[],[f32])).
% 28.02/4.03  
% 28.02/4.03  fof(f66,plain,(
% 28.02/4.03    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 28.02/4.03    inference(equality_resolution,[],[f37])).
% 28.02/4.03  
% 28.02/4.03  fof(f12,axiom,(
% 28.02/4.03    ! [X0,X1,X2] : (v1_relat_1(X2) => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1))),
% 28.02/4.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 28.02/4.03  
% 28.02/4.03  fof(f24,plain,(
% 28.02/4.03    ! [X0,X1,X2] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 28.02/4.03    inference(ennf_transformation,[],[f12])).
% 28.02/4.03  
% 28.02/4.03  fof(f51,plain,(
% 28.02/4.03    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 28.02/4.03    inference(cnf_transformation,[],[f24])).
% 28.02/4.03  
% 28.02/4.03  fof(f62,plain,(
% 28.02/4.03    ( ! [X2,X0,X1] : (k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(X2,X1))) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 28.02/4.03    inference(definition_unfolding,[],[f51,f59])).
% 28.02/4.03  
% 28.02/4.03  fof(f13,axiom,(
% 28.02/4.03    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)))),
% 28.02/4.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 28.02/4.03  
% 28.02/4.03  fof(f25,plain,(
% 28.02/4.03    ! [X0,X1] : (k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 28.02/4.03    inference(ennf_transformation,[],[f13])).
% 28.02/4.03  
% 28.02/4.03  fof(f26,plain,(
% 28.02/4.03    ! [X0,X1] : (k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 28.02/4.03    inference(flattening,[],[f25])).
% 28.02/4.03  
% 28.02/4.03  fof(f52,plain,(
% 28.02/4.03    ( ! [X0,X1] : (k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 28.02/4.03    inference(cnf_transformation,[],[f26])).
% 28.02/4.03  
% 28.02/4.03  fof(f63,plain,(
% 28.02/4.03    ( ! [X0,X1] : (k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(X1,k1_relat_1(X1)))) = k9_relat_1(X1,k10_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 28.02/4.03    inference(definition_unfolding,[],[f52,f59])).
% 28.02/4.03  
% 28.02/4.03  fof(f39,plain,(
% 28.02/4.03    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 28.02/4.03    inference(cnf_transformation,[],[f32])).
% 28.02/4.03  
% 28.02/4.03  fof(f3,axiom,(
% 28.02/4.03    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 28.02/4.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 28.02/4.03  
% 28.02/4.03  fof(f40,plain,(
% 28.02/4.03    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 28.02/4.03    inference(cnf_transformation,[],[f3])).
% 28.02/4.03  
% 28.02/4.03  fof(f61,plain,(
% 28.02/4.03    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0)) )),
% 28.02/4.03    inference(definition_unfolding,[],[f40,f59])).
% 28.02/4.03  
% 28.02/4.03  fof(f55,plain,(
% 28.02/4.03    v1_relat_1(sK0)),
% 28.02/4.03    inference(cnf_transformation,[],[f35])).
% 28.02/4.03  
% 28.02/4.03  fof(f58,plain,(
% 28.02/4.03    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 28.02/4.03    inference(cnf_transformation,[],[f35])).
% 28.02/4.03  
% 28.02/4.03  cnf(c_18,negated_conjecture,
% 28.02/4.03      ( r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
% 28.02/4.03      inference(cnf_transformation,[],[f57]) ).
% 28.02/4.03  
% 28.02/4.03  cnf(c_495,plain,
% 28.02/4.03      ( r1_tarski(k10_relat_1(sK0,sK2),sK1) = iProver_top ),
% 28.02/4.03      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 28.02/4.03  
% 28.02/4.03  cnf(c_0,plain,
% 28.02/4.03      ( k1_setfam_1(k1_enumset1(X0,X0,X0)) = X0 ),
% 28.02/4.03      inference(cnf_transformation,[],[f60]) ).
% 28.02/4.03  
% 28.02/4.03  cnf(c_16,plain,
% 28.02/4.03      ( k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
% 28.02/4.03      inference(cnf_transformation,[],[f64]) ).
% 28.02/4.03  
% 28.02/4.03  cnf(c_10,plain,
% 28.02/4.03      ( ~ v1_relat_1(X0)
% 28.02/4.03      | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
% 28.02/4.03      inference(cnf_transformation,[],[f48]) ).
% 28.02/4.03  
% 28.02/4.03  cnf(c_12,plain,
% 28.02/4.03      ( v1_relat_1(k6_relat_1(X0)) ),
% 28.02/4.03      inference(cnf_transformation,[],[f49]) ).
% 28.02/4.03  
% 28.02/4.03  cnf(c_269,plain,
% 28.02/4.03      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
% 28.02/4.03      | k6_relat_1(X2) != X1 ),
% 28.02/4.03      inference(resolution_lifted,[status(thm)],[c_10,c_12]) ).
% 28.02/4.03  
% 28.02/4.03  cnf(c_270,plain,
% 28.02/4.03      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
% 28.02/4.03      inference(unflattening,[status(thm)],[c_269]) ).
% 28.02/4.03  
% 28.02/4.03  cnf(c_527,plain,
% 28.02/4.03      ( k6_relat_1(k1_setfam_1(k1_enumset1(X0,X0,X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
% 28.02/4.03      inference(demodulation,[status(thm)],[c_16,c_270]) ).
% 28.02/4.03  
% 28.02/4.03  cnf(c_1897,plain,
% 28.02/4.03      ( k7_relat_1(k6_relat_1(X0),X0) = k6_relat_1(X0) ),
% 28.02/4.03      inference(superposition,[status(thm)],[c_0,c_527]) ).
% 28.02/4.03  
% 28.02/4.03  cnf(c_6,plain,
% 28.02/4.03      ( ~ v1_relat_1(X0)
% 28.02/4.03      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 28.02/4.03      inference(cnf_transformation,[],[f44]) ).
% 28.02/4.03  
% 28.02/4.03  cnf(c_284,plain,
% 28.02/4.03      ( k6_relat_1(X0) != X1
% 28.02/4.03      | k2_relat_1(k7_relat_1(X1,X2)) = k9_relat_1(X1,X2) ),
% 28.02/4.03      inference(resolution_lifted,[status(thm)],[c_6,c_12]) ).
% 28.02/4.03  
% 28.02/4.03  cnf(c_285,plain,
% 28.02/4.03      ( k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1) ),
% 28.02/4.03      inference(unflattening,[status(thm)],[c_284]) ).
% 28.02/4.03  
% 28.02/4.03  cnf(c_2853,plain,
% 28.02/4.03      ( k9_relat_1(k6_relat_1(X0),X0) = k2_relat_1(k6_relat_1(X0)) ),
% 28.02/4.03      inference(superposition,[status(thm)],[c_1897,c_285]) ).
% 28.02/4.03  
% 28.02/4.03  cnf(c_8,plain,
% 28.02/4.03      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 28.02/4.03      inference(cnf_transformation,[],[f47]) ).
% 28.02/4.03  
% 28.02/4.03  cnf(c_2867,plain,
% 28.02/4.03      ( k9_relat_1(k6_relat_1(X0),X0) = X0 ),
% 28.02/4.03      inference(light_normalisation,[status(thm)],[c_2853,c_8]) ).
% 28.02/4.03  
% 28.02/4.03  cnf(c_11,plain,
% 28.02/4.03      ( v1_funct_1(k6_relat_1(X0)) ),
% 28.02/4.03      inference(cnf_transformation,[],[f50]) ).
% 28.02/4.03  
% 28.02/4.03  cnf(c_15,plain,
% 28.02/4.03      ( r1_tarski(X0,k10_relat_1(X1,X2))
% 28.02/4.03      | ~ r1_tarski(X0,k1_relat_1(X1))
% 28.02/4.03      | ~ r1_tarski(k9_relat_1(X1,X0),X2)
% 28.02/4.03      | ~ v1_funct_1(X1)
% 28.02/4.03      | ~ v1_relat_1(X1) ),
% 28.02/4.03      inference(cnf_transformation,[],[f53]) ).
% 28.02/4.03  
% 28.02/4.03  cnf(c_190,plain,
% 28.02/4.03      ( r1_tarski(X0,k10_relat_1(X1,X2))
% 28.02/4.03      | ~ r1_tarski(X0,k1_relat_1(X1))
% 28.02/4.03      | ~ r1_tarski(k9_relat_1(X1,X0),X2)
% 28.02/4.03      | ~ v1_relat_1(X1)
% 28.02/4.03      | k6_relat_1(X3) != X1 ),
% 28.02/4.03      inference(resolution_lifted,[status(thm)],[c_11,c_15]) ).
% 28.02/4.03  
% 28.02/4.03  cnf(c_191,plain,
% 28.02/4.03      ( r1_tarski(X0,k10_relat_1(k6_relat_1(X1),X2))
% 28.02/4.03      | ~ r1_tarski(X0,k1_relat_1(k6_relat_1(X1)))
% 28.02/4.03      | ~ r1_tarski(k9_relat_1(k6_relat_1(X1),X0),X2)
% 28.02/4.03      | ~ v1_relat_1(k6_relat_1(X1)) ),
% 28.02/4.03      inference(unflattening,[status(thm)],[c_190]) ).
% 28.02/4.03  
% 28.02/4.03  cnf(c_203,plain,
% 28.02/4.03      ( r1_tarski(X0,k10_relat_1(k6_relat_1(X1),X2))
% 28.02/4.03      | ~ r1_tarski(X0,k1_relat_1(k6_relat_1(X1)))
% 28.02/4.03      | ~ r1_tarski(k9_relat_1(k6_relat_1(X1),X0),X2) ),
% 28.02/4.03      inference(forward_subsumption_resolution,
% 28.02/4.03                [status(thm)],
% 28.02/4.03                [c_191,c_12]) ).
% 28.02/4.03  
% 28.02/4.03  cnf(c_494,plain,
% 28.02/4.03      ( r1_tarski(X0,k10_relat_1(k6_relat_1(X1),X2)) = iProver_top
% 28.02/4.03      | r1_tarski(X0,k1_relat_1(k6_relat_1(X1))) != iProver_top
% 28.02/4.03      | r1_tarski(k9_relat_1(k6_relat_1(X1),X0),X2) != iProver_top ),
% 28.02/4.03      inference(predicate_to_equality,[status(thm)],[c_203]) ).
% 28.02/4.03  
% 28.02/4.03  cnf(c_9,plain,
% 28.02/4.03      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 28.02/4.03      inference(cnf_transformation,[],[f46]) ).
% 28.02/4.03  
% 28.02/4.03  cnf(c_557,plain,
% 28.02/4.03      ( r1_tarski(X0,X1) != iProver_top
% 28.02/4.03      | r1_tarski(X0,k10_relat_1(k6_relat_1(X1),X2)) = iProver_top
% 28.02/4.03      | r1_tarski(k9_relat_1(k6_relat_1(X1),X0),X2) != iProver_top ),
% 28.02/4.03      inference(demodulation,[status(thm)],[c_494,c_9]) ).
% 28.02/4.03  
% 28.02/4.03  cnf(c_6043,plain,
% 28.02/4.03      ( r1_tarski(X0,X1) != iProver_top
% 28.02/4.03      | r1_tarski(X0,X0) != iProver_top
% 28.02/4.03      | r1_tarski(X0,k10_relat_1(k6_relat_1(X0),X1)) = iProver_top ),
% 28.02/4.03      inference(superposition,[status(thm)],[c_2867,c_557]) ).
% 28.02/4.03  
% 28.02/4.03  cnf(c_3,plain,
% 28.02/4.03      ( r1_tarski(X0,X0) ),
% 28.02/4.03      inference(cnf_transformation,[],[f66]) ).
% 28.02/4.03  
% 28.02/4.03  cnf(c_55,plain,
% 28.02/4.03      ( r1_tarski(X0,X0) = iProver_top ),
% 28.02/4.03      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 28.02/4.03  
% 28.02/4.03  cnf(c_48742,plain,
% 28.02/4.03      ( r1_tarski(X0,X1) != iProver_top
% 28.02/4.03      | r1_tarski(X0,k10_relat_1(k6_relat_1(X0),X1)) = iProver_top ),
% 28.02/4.03      inference(global_propositional_subsumption,
% 28.02/4.03                [status(thm)],
% 28.02/4.03                [c_6043,c_55]) ).
% 28.02/4.03  
% 28.02/4.03  cnf(c_1904,plain,
% 28.02/4.03      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
% 28.02/4.03      inference(superposition,[status(thm)],[c_527,c_8]) ).
% 28.02/4.03  
% 28.02/4.03  cnf(c_3012,plain,
% 28.02/4.03      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k9_relat_1(k6_relat_1(X0),X1) ),
% 28.02/4.03      inference(light_normalisation,[status(thm)],[c_1904,c_285]) ).
% 28.02/4.03  
% 28.02/4.03  cnf(c_13,plain,
% 28.02/4.03      ( ~ v1_relat_1(X0)
% 28.02/4.03      | k1_setfam_1(k1_enumset1(X1,X1,k10_relat_1(X0,X2))) = k10_relat_1(k7_relat_1(X0,X1),X2) ),
% 28.02/4.03      inference(cnf_transformation,[],[f62]) ).
% 28.02/4.03  
% 28.02/4.03  cnf(c_263,plain,
% 28.02/4.03      ( k6_relat_1(X0) != X1
% 28.02/4.03      | k1_setfam_1(k1_enumset1(X2,X2,k10_relat_1(X1,X3))) = k10_relat_1(k7_relat_1(X1,X2),X3) ),
% 28.02/4.03      inference(resolution_lifted,[status(thm)],[c_13,c_12]) ).
% 28.02/4.03  
% 28.02/4.03  cnf(c_264,plain,
% 28.02/4.03      ( k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(k6_relat_1(X1),X2))) = k10_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2) ),
% 28.02/4.03      inference(unflattening,[status(thm)],[c_263]) ).
% 28.02/4.03  
% 28.02/4.03  cnf(c_3045,plain,
% 28.02/4.03      ( k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X1),X2)) = k10_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2) ),
% 28.02/4.03      inference(superposition,[status(thm)],[c_3012,c_264]) ).
% 28.02/4.03  
% 28.02/4.03  cnf(c_14,plain,
% 28.02/4.03      ( ~ v1_funct_1(X0)
% 28.02/4.03      | ~ v1_relat_1(X0)
% 28.02/4.03      | k1_setfam_1(k1_enumset1(X1,X1,k9_relat_1(X0,k1_relat_1(X0)))) = k9_relat_1(X0,k10_relat_1(X0,X1)) ),
% 28.02/4.03      inference(cnf_transformation,[],[f63]) ).
% 28.02/4.03  
% 28.02/4.03  cnf(c_210,plain,
% 28.02/4.03      ( ~ v1_relat_1(X0)
% 28.02/4.03      | k6_relat_1(X1) != X0
% 28.02/4.03      | k1_setfam_1(k1_enumset1(X2,X2,k9_relat_1(X0,k1_relat_1(X0)))) = k9_relat_1(X0,k10_relat_1(X0,X2)) ),
% 28.02/4.03      inference(resolution_lifted,[status(thm)],[c_11,c_14]) ).
% 28.02/4.03  
% 28.02/4.03  cnf(c_211,plain,
% 28.02/4.03      ( ~ v1_relat_1(k6_relat_1(X0))
% 28.02/4.03      | k1_setfam_1(k1_enumset1(X1,X1,k9_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0))))) = k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) ),
% 28.02/4.03      inference(unflattening,[status(thm)],[c_210]) ).
% 28.02/4.03  
% 28.02/4.03  cnf(c_215,plain,
% 28.02/4.03      ( k1_setfam_1(k1_enumset1(X1,X1,k9_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0))))) = k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) ),
% 28.02/4.03      inference(global_propositional_subsumption,
% 28.02/4.03                [status(thm)],
% 28.02/4.03                [c_211,c_12]) ).
% 28.02/4.03  
% 28.02/4.03  cnf(c_216,plain,
% 28.02/4.03      ( k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(k6_relat_1(X1),k1_relat_1(k6_relat_1(X1))))) = k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X0)) ),
% 28.02/4.03      inference(renaming,[status(thm)],[c_215]) ).
% 28.02/4.03  
% 28.02/4.03  cnf(c_542,plain,
% 28.02/4.03      ( k1_setfam_1(k1_enumset1(X0,X0,k9_relat_1(k6_relat_1(X1),X1))) = k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X0)) ),
% 28.02/4.03      inference(demodulation,[status(thm)],[c_216,c_9]) ).
% 28.02/4.03  
% 28.02/4.03  cnf(c_4624,plain,
% 28.02/4.03      ( k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X1),X0) ),
% 28.02/4.03      inference(demodulation,[status(thm)],[c_542,c_2867,c_3012]) ).
% 28.02/4.03  
% 28.02/4.03  cnf(c_31320,plain,
% 28.02/4.03      ( k10_relat_1(k7_relat_1(k6_relat_1(X0),X0),X1) = k9_relat_1(k6_relat_1(X1),X0) ),
% 28.02/4.03      inference(superposition,[status(thm)],[c_3045,c_4624]) ).
% 28.02/4.03  
% 28.02/4.03  cnf(c_31360,plain,
% 28.02/4.03      ( k10_relat_1(k6_relat_1(X0),X1) = k9_relat_1(k6_relat_1(X1),X0) ),
% 28.02/4.03      inference(light_normalisation,[status(thm)],[c_31320,c_1897]) ).
% 28.02/4.03  
% 28.02/4.03  cnf(c_48746,plain,
% 28.02/4.03      ( r1_tarski(X0,X1) != iProver_top
% 28.02/4.03      | r1_tarski(X0,k9_relat_1(k6_relat_1(X1),X0)) = iProver_top ),
% 28.02/4.03      inference(light_normalisation,[status(thm)],[c_48742,c_31360]) ).
% 28.02/4.03  
% 28.02/4.03  cnf(c_1,plain,
% 28.02/4.03      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 28.02/4.03      inference(cnf_transformation,[],[f39]) ).
% 28.02/4.03  
% 28.02/4.03  cnf(c_499,plain,
% 28.02/4.03      ( X0 = X1
% 28.02/4.03      | r1_tarski(X0,X1) != iProver_top
% 28.02/4.03      | r1_tarski(X1,X0) != iProver_top ),
% 28.02/4.03      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 28.02/4.03  
% 28.02/4.03  cnf(c_48757,plain,
% 28.02/4.03      ( k9_relat_1(k6_relat_1(X0),X1) = X1
% 28.02/4.03      | r1_tarski(X1,X0) != iProver_top
% 28.02/4.03      | r1_tarski(k9_relat_1(k6_relat_1(X0),X1),X1) != iProver_top ),
% 28.02/4.03      inference(superposition,[status(thm)],[c_48746,c_499]) ).
% 28.02/4.03  
% 28.02/4.03  cnf(c_4,plain,
% 28.02/4.03      ( r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) ),
% 28.02/4.03      inference(cnf_transformation,[],[f61]) ).
% 28.02/4.03  
% 28.02/4.03  cnf(c_497,plain,
% 28.02/4.03      ( r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X1)),X0) = iProver_top ),
% 28.02/4.03      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 28.02/4.03  
% 28.02/4.03  cnf(c_3020,plain,
% 28.02/4.03      ( r1_tarski(k9_relat_1(k6_relat_1(X0),X1),X0) = iProver_top ),
% 28.02/4.03      inference(demodulation,[status(thm)],[c_3012,c_497]) ).
% 28.02/4.03  
% 28.02/4.03  cnf(c_6316,plain,
% 28.02/4.03      ( r1_tarski(k9_relat_1(k6_relat_1(X0),X1),X1) = iProver_top ),
% 28.02/4.03      inference(superposition,[status(thm)],[c_4624,c_3020]) ).
% 28.02/4.03  
% 28.02/4.03  cnf(c_106305,plain,
% 28.02/4.03      ( r1_tarski(X1,X0) != iProver_top
% 28.02/4.03      | k9_relat_1(k6_relat_1(X0),X1) = X1 ),
% 28.02/4.03      inference(global_propositional_subsumption,
% 28.02/4.03                [status(thm)],
% 28.02/4.03                [c_48757,c_6316]) ).
% 28.02/4.03  
% 28.02/4.03  cnf(c_106306,plain,
% 28.02/4.03      ( k9_relat_1(k6_relat_1(X0),X1) = X1
% 28.02/4.03      | r1_tarski(X1,X0) != iProver_top ),
% 28.02/4.03      inference(renaming,[status(thm)],[c_106305]) ).
% 28.02/4.03  
% 28.02/4.03  cnf(c_106312,plain,
% 28.02/4.03      ( k9_relat_1(k6_relat_1(sK1),k10_relat_1(sK0,sK2)) = k10_relat_1(sK0,sK2) ),
% 28.02/4.03      inference(superposition,[status(thm)],[c_495,c_106306]) ).
% 28.02/4.03  
% 28.02/4.03  cnf(c_20,negated_conjecture,
% 28.02/4.03      ( v1_relat_1(sK0) ),
% 28.02/4.03      inference(cnf_transformation,[],[f55]) ).
% 28.02/4.03  
% 28.02/4.03  cnf(c_290,plain,
% 28.02/4.03      ( k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(X1,X2))) = k10_relat_1(k7_relat_1(X1,X0),X2)
% 28.02/4.03      | sK0 != X1 ),
% 28.02/4.03      inference(resolution_lifted,[status(thm)],[c_13,c_20]) ).
% 28.02/4.03  
% 28.02/4.03  cnf(c_291,plain,
% 28.02/4.03      ( k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(sK0,X1))) = k10_relat_1(k7_relat_1(sK0,X0),X1) ),
% 28.02/4.03      inference(unflattening,[status(thm)],[c_290]) ).
% 28.02/4.03  
% 28.02/4.03  cnf(c_1900,plain,
% 28.02/4.03      ( k6_relat_1(k10_relat_1(k7_relat_1(sK0,X0),X1)) = k7_relat_1(k6_relat_1(X0),k10_relat_1(sK0,X1)) ),
% 28.02/4.03      inference(superposition,[status(thm)],[c_291,c_527]) ).
% 28.02/4.03  
% 28.02/4.03  cnf(c_2855,plain,
% 28.02/4.03      ( k2_relat_1(k6_relat_1(k10_relat_1(k7_relat_1(sK0,X0),X1))) = k9_relat_1(k6_relat_1(X0),k10_relat_1(sK0,X1)) ),
% 28.02/4.03      inference(superposition,[status(thm)],[c_1900,c_285]) ).
% 28.02/4.03  
% 28.02/4.03  cnf(c_2861,plain,
% 28.02/4.03      ( k9_relat_1(k6_relat_1(X0),k10_relat_1(sK0,X1)) = k10_relat_1(k7_relat_1(sK0,X0),X1) ),
% 28.02/4.03      inference(demodulation,[status(thm)],[c_2855,c_8]) ).
% 28.02/4.03  
% 28.02/4.03  cnf(c_107328,plain,
% 28.02/4.03      ( k10_relat_1(k7_relat_1(sK0,sK1),sK2) = k10_relat_1(sK0,sK2) ),
% 28.02/4.03      inference(superposition,[status(thm)],[c_106312,c_2861]) ).
% 28.02/4.03  
% 28.02/4.03  cnf(c_328,plain,( X0 = X0 ),theory(equality) ).
% 28.02/4.03  
% 28.02/4.03  cnf(c_687,plain,
% 28.02/4.03      ( k10_relat_1(sK0,sK2) = k10_relat_1(sK0,sK2) ),
% 28.02/4.03      inference(instantiation,[status(thm)],[c_328]) ).
% 28.02/4.03  
% 28.02/4.03  cnf(c_329,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 28.02/4.03  
% 28.02/4.03  cnf(c_623,plain,
% 28.02/4.03      ( k10_relat_1(k7_relat_1(sK0,sK1),sK2) != X0
% 28.02/4.03      | k10_relat_1(sK0,sK2) != X0
% 28.02/4.03      | k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
% 28.02/4.03      inference(instantiation,[status(thm)],[c_329]) ).
% 28.02/4.03  
% 28.02/4.03  cnf(c_686,plain,
% 28.02/4.03      ( k10_relat_1(k7_relat_1(sK0,sK1),sK2) != k10_relat_1(sK0,sK2)
% 28.02/4.03      | k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2)
% 28.02/4.03      | k10_relat_1(sK0,sK2) != k10_relat_1(sK0,sK2) ),
% 28.02/4.03      inference(instantiation,[status(thm)],[c_623]) ).
% 28.02/4.03  
% 28.02/4.03  cnf(c_17,negated_conjecture,
% 28.02/4.03      ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
% 28.02/4.03      inference(cnf_transformation,[],[f58]) ).
% 28.02/4.03  
% 28.02/4.03  cnf(contradiction,plain,
% 28.02/4.03      ( $false ),
% 28.02/4.03      inference(minisat,[status(thm)],[c_107328,c_687,c_686,c_17]) ).
% 28.02/4.03  
% 28.02/4.03  
% 28.02/4.03  % SZS output end CNFRefutation for theBenchmark.p
% 28.02/4.03  
% 28.02/4.03  ------                               Statistics
% 28.02/4.03  
% 28.02/4.03  ------ General
% 28.02/4.03  
% 28.02/4.03  abstr_ref_over_cycles:                  0
% 28.02/4.03  abstr_ref_under_cycles:                 0
% 28.02/4.03  gc_basic_clause_elim:                   0
% 28.02/4.03  forced_gc_time:                         0
% 28.02/4.03  parsing_time:                           0.009
% 28.02/4.03  unif_index_cands_time:                  0.
% 28.02/4.03  unif_index_add_time:                    0.
% 28.02/4.03  orderings_time:                         0.
% 28.02/4.03  out_proof_time:                         0.018
% 28.02/4.03  total_time:                             3.486
% 28.02/4.03  num_of_symbols:                         46
% 28.02/4.03  num_of_terms:                           125251
% 28.02/4.03  
% 28.02/4.03  ------ Preprocessing
% 28.02/4.03  
% 28.02/4.03  num_of_splits:                          0
% 28.02/4.03  num_of_split_atoms:                     0
% 28.02/4.03  num_of_reused_defs:                     0
% 28.02/4.03  num_eq_ax_congr_red:                    5
% 28.02/4.03  num_of_sem_filtered_clauses:            1
% 28.02/4.03  num_of_subtypes:                        0
% 28.02/4.03  monotx_restored_types:                  0
% 28.02/4.03  sat_num_of_epr_types:                   0
% 28.02/4.03  sat_num_of_non_cyclic_types:            0
% 28.02/4.03  sat_guarded_non_collapsed_types:        0
% 28.02/4.03  num_pure_diseq_elim:                    0
% 28.02/4.03  simp_replaced_by:                       0
% 28.02/4.03  res_preprocessed:                       89
% 28.02/4.03  prep_upred:                             0
% 28.02/4.03  prep_unflattend:                        12
% 28.02/4.03  smt_new_axioms:                         0
% 28.02/4.03  pred_elim_cands:                        3
% 28.02/4.03  pred_elim:                              2
% 28.02/4.03  pred_elim_cl:                           -2
% 28.02/4.03  pred_elim_cycles:                       3
% 28.02/4.03  merged_defs:                            0
% 28.02/4.03  merged_defs_ncl:                        0
% 28.02/4.03  bin_hyper_res:                          0
% 28.02/4.03  prep_cycles:                            3
% 28.02/4.03  pred_elim_time:                         0.004
% 28.02/4.03  splitting_time:                         0.
% 28.02/4.03  sem_filter_time:                        0.
% 28.02/4.03  monotx_time:                            0.
% 28.02/4.03  subtype_inf_time:                       0.
% 28.02/4.03  
% 28.02/4.03  ------ Problem properties
% 28.02/4.03  
% 28.02/4.03  clauses:                                22
% 28.02/4.03  conjectures:                            2
% 28.02/4.03  epr:                                    3
% 28.02/4.03  horn:                                   22
% 28.02/4.03  ground:                                 2
% 28.02/4.03  unary:                                  18
% 28.02/4.03  binary:                                 0
% 28.02/4.03  lits:                                   30
% 28.02/4.03  lits_eq:                                14
% 28.02/4.03  fd_pure:                                0
% 28.02/4.03  fd_pseudo:                              0
% 28.02/4.03  fd_cond:                                0
% 28.02/4.03  fd_pseudo_cond:                         1
% 28.02/4.03  ac_symbols:                             0
% 28.02/4.03  
% 28.02/4.03  ------ Propositional Solver
% 28.02/4.03  
% 28.02/4.03  prop_solver_calls:                      40
% 28.02/4.03  prop_fast_solver_calls:                 1289
% 28.02/4.03  smt_solver_calls:                       0
% 28.02/4.03  smt_fast_solver_calls:                  0
% 28.02/4.03  prop_num_of_clauses:                    39961
% 28.02/4.03  prop_preprocess_simplified:             46687
% 28.02/4.03  prop_fo_subsumed:                       11
% 28.02/4.03  prop_solver_time:                       0.
% 28.02/4.03  smt_solver_time:                        0.
% 28.02/4.03  smt_fast_solver_time:                   0.
% 28.02/4.03  prop_fast_solver_time:                  0.
% 28.02/4.03  prop_unsat_core_time:                   0.005
% 28.02/4.03  
% 28.02/4.03  ------ QBF
% 28.02/4.03  
% 28.02/4.03  qbf_q_res:                              0
% 28.02/4.03  qbf_num_tautologies:                    0
% 28.02/4.03  qbf_prep_cycles:                        0
% 28.02/4.03  
% 28.02/4.03  ------ BMC1
% 28.02/4.03  
% 28.02/4.03  bmc1_current_bound:                     -1
% 28.02/4.03  bmc1_last_solved_bound:                 -1
% 28.02/4.03  bmc1_unsat_core_size:                   -1
% 28.02/4.03  bmc1_unsat_core_parents_size:           -1
% 28.02/4.03  bmc1_merge_next_fun:                    0
% 28.02/4.03  bmc1_unsat_core_clauses_time:           0.
% 28.02/4.03  
% 28.02/4.03  ------ Instantiation
% 28.02/4.03  
% 28.02/4.03  inst_num_of_clauses:                    7368
% 28.02/4.03  inst_num_in_passive:                    2898
% 28.02/4.03  inst_num_in_active:                     2052
% 28.02/4.03  inst_num_in_unprocessed:                2418
% 28.02/4.03  inst_num_of_loops:                      2120
% 28.02/4.03  inst_num_of_learning_restarts:          0
% 28.02/4.03  inst_num_moves_active_passive:          66
% 28.02/4.03  inst_lit_activity:                      0
% 28.02/4.03  inst_lit_activity_moves:                0
% 28.02/4.03  inst_num_tautologies:                   0
% 28.02/4.03  inst_num_prop_implied:                  0
% 28.02/4.03  inst_num_existing_simplified:           0
% 28.02/4.03  inst_num_eq_res_simplified:             0
% 28.02/4.03  inst_num_child_elim:                    0
% 28.02/4.03  inst_num_of_dismatching_blockings:      8059
% 28.02/4.03  inst_num_of_non_proper_insts:           8753
% 28.02/4.03  inst_num_of_duplicates:                 0
% 28.02/4.03  inst_inst_num_from_inst_to_res:         0
% 28.02/4.03  inst_dismatching_checking_time:         0.
% 28.02/4.03  
% 28.02/4.03  ------ Resolution
% 28.02/4.03  
% 28.02/4.03  res_num_of_clauses:                     0
% 28.02/4.03  res_num_in_passive:                     0
% 28.02/4.03  res_num_in_active:                      0
% 28.02/4.03  res_num_of_loops:                       92
% 28.02/4.03  res_forward_subset_subsumed:            611
% 28.02/4.03  res_backward_subset_subsumed:           2
% 28.02/4.03  res_forward_subsumed:                   0
% 28.02/4.03  res_backward_subsumed:                  0
% 28.02/4.03  res_forward_subsumption_resolution:     1
% 28.02/4.03  res_backward_subsumption_resolution:    0
% 28.02/4.03  res_clause_to_clause_subsumption:       38334
% 28.02/4.03  res_orphan_elimination:                 0
% 28.02/4.03  res_tautology_del:                      800
% 28.02/4.03  res_num_eq_res_simplified:              0
% 28.02/4.03  res_num_sel_changes:                    0
% 28.02/4.03  res_moves_from_active_to_pass:          0
% 28.02/4.03  
% 28.02/4.03  ------ Superposition
% 28.02/4.03  
% 28.02/4.03  sup_time_total:                         0.
% 28.02/4.03  sup_time_generating:                    0.
% 28.02/4.03  sup_time_sim_full:                      0.
% 28.02/4.03  sup_time_sim_immed:                     0.
% 28.02/4.03  
% 28.02/4.03  sup_num_of_clauses:                     4900
% 28.02/4.03  sup_num_in_active:                      301
% 28.02/4.03  sup_num_in_passive:                     4599
% 28.02/4.03  sup_num_of_loops:                       423
% 28.02/4.03  sup_fw_superposition:                   4550
% 28.02/4.03  sup_bw_superposition:                   2987
% 28.02/4.03  sup_immediate_simplified:               3221
% 28.02/4.03  sup_given_eliminated:                   3
% 28.02/4.03  comparisons_done:                       0
% 28.02/4.03  comparisons_avoided:                    0
% 28.02/4.03  
% 28.02/4.03  ------ Simplifications
% 28.02/4.03  
% 28.02/4.03  
% 28.02/4.03  sim_fw_subset_subsumed:                 150
% 28.02/4.03  sim_bw_subset_subsumed:                 42
% 28.02/4.03  sim_fw_subsumed:                        733
% 28.02/4.03  sim_bw_subsumed:                        46
% 28.02/4.03  sim_fw_subsumption_res:                 17
% 28.02/4.03  sim_bw_subsumption_res:                 0
% 28.02/4.03  sim_tautology_del:                      29
% 28.02/4.03  sim_eq_tautology_del:                   338
% 28.02/4.03  sim_eq_res_simp:                        0
% 28.02/4.03  sim_fw_demodulated:                     1725
% 28.02/4.03  sim_bw_demodulated:                     173
% 28.02/4.03  sim_light_normalised:                   1533
% 28.02/4.03  sim_joinable_taut:                      0
% 28.02/4.03  sim_joinable_simp:                      0
% 28.02/4.03  sim_ac_normalised:                      0
% 28.02/4.03  sim_smt_subsumption:                    0
% 28.02/4.03  
%------------------------------------------------------------------------------
