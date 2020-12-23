%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:49:57 EST 2020

% Result     : Theorem 19.07s
% Output     : CNFRefutation 19.07s
% Verified   : 
% Statistics : Number of formulae       :  226 (37717 expanded)
%              Number of clauses        :  164 (13907 expanded)
%              Number of leaves         :   19 (9043 expanded)
%              Depth                    :   39
%              Number of atoms          :  351 (51818 expanded)
%              Number of equality atoms :  256 (34891 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    5 (   1 average)
%              Maximal term depth       :    8 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f65,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f44,f45])).

fof(f68,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f43,f65,f65])).

fof(f7,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f66,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f46,f65])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f50,f66])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f63,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f14,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f57,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f42,f66])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f49,f66])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k5_relat_1(k7_relat_1(X1,X0),X2) = k7_relat_1(k5_relat_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k5_relat_1(k7_relat_1(X1,X0),X2) = k7_relat_1(k5_relat_1(X1,X2),X0)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k7_relat_1(X1,X0),X2) = k7_relat_1(k5_relat_1(X1,X2),X0)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f20,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f20])).

fof(f39,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f21])).

fof(f40,plain,
    ( ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))
   => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f39,f40])).

fof(f64,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f41])).

fof(f71,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f64,f66])).

cnf(c_1,plain,
    ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_3,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_492,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_490,plain,
    ( k7_relat_1(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1323,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) ),
    inference(superposition,[status(thm)],[c_492,c_490])).

cnf(c_18,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_479,plain,
    ( k7_relat_1(X0,k1_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_710,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0))) = k6_relat_1(X0) ),
    inference(superposition,[status(thm)],[c_492,c_479])).

cnf(c_12,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_711,plain,
    ( k7_relat_1(k6_relat_1(X0),X0) = k6_relat_1(X0) ),
    inference(light_normalisation,[status(thm)],[c_710,c_12])).

cnf(c_1513,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X0),X1) = k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
    inference(superposition,[status(thm)],[c_1323,c_711])).

cnf(c_7317,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X1),X0) = k6_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) ),
    inference(superposition,[status(thm)],[c_1,c_1513])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k8_relat_1(X1,k7_relat_1(X0,X2)) = k7_relat_1(k8_relat_1(X1,X0),X2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_487,plain,
    ( k8_relat_1(X0,k7_relat_1(X1,X2)) = k7_relat_1(k8_relat_1(X0,X1),X2)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1244,plain,
    ( k8_relat_1(X0,k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k8_relat_1(X0,k6_relat_1(X1)),X2) ),
    inference(superposition,[status(thm)],[c_492,c_487])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_488,plain,
    ( k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_896,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0)) ),
    inference(superposition,[status(thm)],[c_492,c_488])).

cnf(c_16,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_481,plain,
    ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_772,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[status(thm)],[c_492,c_481])).

cnf(c_897,plain,
    ( k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_896,c_772])).

cnf(c_1247,plain,
    ( k8_relat_1(X0,k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) ),
    inference(light_normalisation,[status(thm)],[c_1244,c_897])).

cnf(c_1379,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X1) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(superposition,[status(thm)],[c_711,c_1247])).

cnf(c_1380,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X1) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_1379,c_897])).

cnf(c_11,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_7620,plain,
    ( k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X1),X0)) = k1_setfam_1(k2_enumset1(X1,X1,X1,X0)) ),
    inference(superposition,[status(thm)],[c_7317,c_11])).

cnf(c_1511,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1) ),
    inference(superposition,[status(thm)],[c_1,c_1323])).

cnf(c_1719,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X1),X0) = k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
    inference(superposition,[status(thm)],[c_1511,c_711])).

cnf(c_7647,plain,
    ( k2_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) = k1_setfam_1(k2_enumset1(X1,X1,X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_7620,c_1719])).

cnf(c_13,plain,
    ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_484,plain,
    ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_949,plain,
    ( r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X0)) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_772,c_484])).

cnf(c_61,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1409,plain,
    ( r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_949,c_61])).

cnf(c_15,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_482,plain,
    ( k5_relat_1(X0,k6_relat_1(X1)) = X0
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_767,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_482])).

cnf(c_1685,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_767,c_61])).

cnf(c_1686,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_1685])).

cnf(c_1691,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1686,c_772])).

cnf(c_1696,plain,
    ( k7_relat_1(k6_relat_1(k6_relat_1(X0)),k7_relat_1(k6_relat_1(X0),X1)) = k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(superposition,[status(thm)],[c_1409,c_1691])).

cnf(c_1982,plain,
    ( k6_relat_1(k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))) = k7_relat_1(k6_relat_1(k6_relat_1(X0)),k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) ),
    inference(superposition,[status(thm)],[c_1323,c_1696])).

cnf(c_1514,plain,
    ( r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),k6_relat_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1323,c_1409])).

cnf(c_1698,plain,
    ( k7_relat_1(k6_relat_1(k6_relat_1(X0)),k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) = k6_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) ),
    inference(superposition,[status(thm)],[c_1514,c_1691])).

cnf(c_1999,plain,
    ( k6_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) = k6_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1)) ),
    inference(light_normalisation,[status(thm)],[c_1982,c_1511,c_1698])).

cnf(c_7508,plain,
    ( k6_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X0),X1)) = k6_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X0)))) ),
    inference(superposition,[status(thm)],[c_7317,c_1999])).

cnf(c_7716,plain,
    ( k6_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) = k6_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X0)))) ),
    inference(light_normalisation,[status(thm)],[c_7508,c_1513])).

cnf(c_9159,plain,
    ( k1_relat_1(k6_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))))) = k6_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) ),
    inference(superposition,[status(thm)],[c_7716,c_12])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_494,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1022,plain,
    ( k1_setfam_1(k2_enumset1(k5_relat_1(k6_relat_1(X0),X1),k5_relat_1(k6_relat_1(X0),X1),k5_relat_1(k6_relat_1(X0),X1),X1)) = k5_relat_1(k6_relat_1(X0),X1)
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_484,c_494])).

cnf(c_7822,plain,
    ( k2_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,k5_relat_1(k6_relat_1(X1),X0))))) = k5_relat_1(k6_relat_1(X1),X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7647,c_1022])).

cnf(c_7825,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,k5_relat_1(k6_relat_1(X1),X0))) = k5_relat_1(k6_relat_1(X1),X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7822,c_11])).

cnf(c_8721,plain,
    ( k1_setfam_1(k2_enumset1(k6_relat_1(X0),k6_relat_1(X0),k6_relat_1(X0),k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(superposition,[status(thm)],[c_492,c_7825])).

cnf(c_8724,plain,
    ( k1_setfam_1(k2_enumset1(k6_relat_1(X0),k6_relat_1(X0),k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(demodulation,[status(thm)],[c_8721,c_772])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_491,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_9864,plain,
    ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8724,c_491])).

cnf(c_9897,plain,
    ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9864,c_61])).

cnf(c_9924,plain,
    ( k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0) ),
    inference(superposition,[status(thm)],[c_9897,c_481])).

cnf(c_11642,plain,
    ( k5_relat_1(k1_relat_1(k6_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))))),k7_relat_1(k6_relat_1(X2),X3)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X3),k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) ),
    inference(superposition,[status(thm)],[c_9159,c_9924])).

cnf(c_9930,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k1_setfam_1(k2_enumset1(X2,X2,X2,X3))) = k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),X3) ),
    inference(superposition,[status(thm)],[c_9897,c_490])).

cnf(c_11691,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k1_setfam_1(k2_enumset1(X2,X2,X2,X3))) = k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X3),X2) ),
    inference(demodulation,[status(thm)],[c_11642,c_12,c_9924,c_9930])).

cnf(c_12773,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k2_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X2,X2,X2,X3))))) = k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),X3) ),
    inference(superposition,[status(thm)],[c_7647,c_11691])).

cnf(c_12840,plain,
    ( k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),X3) = k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X3),X2) ),
    inference(demodulation,[status(thm)],[c_12773,c_11,c_11691])).

cnf(c_13007,plain,
    ( k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) ),
    inference(superposition,[status(thm)],[c_1380,c_12840])).

cnf(c_1727,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1) ),
    inference(superposition,[status(thm)],[c_1511,c_1323])).

cnf(c_1912,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[status(thm)],[c_711,c_1727])).

cnf(c_1970,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) = k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),X0) ),
    inference(superposition,[status(thm)],[c_1323,c_1912])).

cnf(c_1977,plain,
    ( k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),X0) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1) ),
    inference(light_normalisation,[status(thm)],[c_1970,c_1511])).

cnf(c_2735,plain,
    ( k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),X0) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) ),
    inference(superposition,[status(thm)],[c_1727,c_1977])).

cnf(c_3864,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X1,X1,X1,X2))),X3) = k7_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),X3),X0) ),
    inference(superposition,[status(thm)],[c_1323,c_2735])).

cnf(c_2738,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k1_setfam_1(k2_enumset1(X2,X2,X2,X3))) = k7_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X3),X1),X0) ),
    inference(superposition,[status(thm)],[c_1323,c_1977])).

cnf(c_1914,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k1_setfam_1(k2_enumset1(X2,X2,X2,X3))) = k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X3),X1) ),
    inference(superposition,[status(thm)],[c_1323,c_1727])).

cnf(c_2745,plain,
    ( k7_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),X3),X0) = k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),X3) ),
    inference(light_normalisation,[status(thm)],[c_2738,c_1914])).

cnf(c_3875,plain,
    ( k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),X3) = k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1),X3) ),
    inference(light_normalisation,[status(thm)],[c_3864,c_1511,c_2745])).

cnf(c_14632,plain,
    ( k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),X2) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1) ),
    inference(superposition,[status(thm)],[c_13007,c_3875])).

cnf(c_17354,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X0),X1) = k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X0))),X0) ),
    inference(superposition,[status(thm)],[c_7317,c_14632])).

cnf(c_14,plain,
    ( r1_tarski(k5_relat_1(X0,k6_relat_1(X1)),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_483,plain,
    ( r1_tarski(k5_relat_1(X0,k6_relat_1(X1)),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_948,plain,
    ( r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X1)) = iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_772,c_483])).

cnf(c_1113,plain,
    ( r1_tarski(k6_relat_1(X0),k6_relat_1(X0)) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_711,c_948])).

cnf(c_1172,plain,
    ( r1_tarski(k6_relat_1(X0),k6_relat_1(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1113,c_61])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_485,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1843,plain,
    ( r1_tarski(X0,k1_relat_1(X1)) = iProver_top
    | r1_tarski(k6_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12,c_485])).

cnf(c_2428,plain,
    ( v1_relat_1(X1) != iProver_top
    | r1_tarski(k6_relat_1(X0),X1) != iProver_top
    | r1_tarski(X0,k1_relat_1(X1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1843,c_61])).

cnf(c_2429,plain,
    ( r1_tarski(X0,k1_relat_1(X1)) = iProver_top
    | r1_tarski(k6_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_2428])).

cnf(c_2434,plain,
    ( r1_tarski(X0,k1_relat_1(k6_relat_1(X0))) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1172,c_2429])).

cnf(c_2441,plain,
    ( r1_tarski(X0,X0) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2434,c_12])).

cnf(c_2446,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2441,c_61])).

cnf(c_2453,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_2446,c_494])).

cnf(c_12774,plain,
    ( k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),X2) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) ),
    inference(superposition,[status(thm)],[c_2453,c_11691])).

cnf(c_14492,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X0),X1) = k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X1) ),
    inference(superposition,[status(thm)],[c_1513,c_12774])).

cnf(c_14562,plain,
    ( k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X1) = k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
    inference(light_normalisation,[status(thm)],[c_14492,c_1513])).

cnf(c_14578,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X0),X1) = k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X0) ),
    inference(superposition,[status(thm)],[c_1513,c_13007])).

cnf(c_14659,plain,
    ( k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X0) = k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
    inference(light_normalisation,[status(thm)],[c_14578,c_1513])).

cnf(c_17426,plain,
    ( k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X1) = k6_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) ),
    inference(light_normalisation,[status(thm)],[c_17354,c_1513,c_14562,c_14659])).

cnf(c_1694,plain,
    ( k7_relat_1(k6_relat_1(X0),k5_relat_1(X0,k6_relat_1(X1))) = k6_relat_1(k5_relat_1(X0,k6_relat_1(X1)))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_483,c_1691])).

cnf(c_47204,plain,
    ( k7_relat_1(k6_relat_1(k6_relat_1(X0)),k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k6_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ),
    inference(superposition,[status(thm)],[c_492,c_1694])).

cnf(c_47219,plain,
    ( k7_relat_1(k6_relat_1(k6_relat_1(X0)),k7_relat_1(k6_relat_1(X1),X0)) = k6_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(light_normalisation,[status(thm)],[c_47204,c_772])).

cnf(c_1023,plain,
    ( k1_setfam_1(k2_enumset1(k5_relat_1(X0,k6_relat_1(X1)),k5_relat_1(X0,k6_relat_1(X1)),k5_relat_1(X0,k6_relat_1(X1)),X0)) = k5_relat_1(X0,k6_relat_1(X1))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_483,c_494])).

cnf(c_7823,plain,
    ( k2_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,k5_relat_1(X0,k6_relat_1(X1)))))) = k5_relat_1(X0,k6_relat_1(X1))
    | v1_relat_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7647,c_1023])).

cnf(c_7824,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,k5_relat_1(X0,k6_relat_1(X1)))) = k5_relat_1(X0,k6_relat_1(X1))
    | v1_relat_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7823,c_11])).

cnf(c_8707,plain,
    ( k1_setfam_1(k2_enumset1(k6_relat_1(X0),k6_relat_1(X0),k6_relat_1(X0),k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ),
    inference(superposition,[status(thm)],[c_492,c_7824])).

cnf(c_8710,plain,
    ( k1_setfam_1(k2_enumset1(k6_relat_1(X0),k6_relat_1(X0),k6_relat_1(X0),k7_relat_1(k6_relat_1(X1),X0))) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(light_normalisation,[status(thm)],[c_8707,c_772])).

cnf(c_9594,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X1),X2)),k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X1),X2)) ),
    inference(superposition,[status(thm)],[c_8710,c_1511])).

cnf(c_2454,plain,
    ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2446,c_482])).

cnf(c_9929,plain,
    ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[status(thm)],[c_9897,c_2454])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k7_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(k7_relat_1(X0,X2),X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_489,plain,
    ( k7_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(k7_relat_1(X0,X2),X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1181,plain,
    ( k7_relat_1(k5_relat_1(k6_relat_1(X0),X1),X2) = k5_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1)
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_492,c_489])).

cnf(c_7297,plain,
    ( k7_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),X2) = k5_relat_1(k7_relat_1(k6_relat_1(X0),X2),k6_relat_1(X1)) ),
    inference(superposition,[status(thm)],[c_492,c_1181])).

cnf(c_7300,plain,
    ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_7297,c_772])).

cnf(c_12249,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0),X1) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[status(thm)],[c_9929,c_7300])).

cnf(c_1531,plain,
    ( r1_tarski(k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),X3),k6_relat_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1323,c_1514])).

cnf(c_12333,plain,
    ( r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_12249,c_1531])).

cnf(c_13959,plain,
    ( r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X2)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1727,c_12333])).

cnf(c_32012,plain,
    ( r1_tarski(k7_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X1),X2)),k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),k6_relat_1(X2))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_9594,c_13959])).

cnf(c_47585,plain,
    ( r1_tarski(k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)),k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(k6_relat_1(X1)),k6_relat_1(X1))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_47219,c_32012])).

cnf(c_47612,plain,
    ( r1_tarski(k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)),k6_relat_1(k6_relat_1(X1))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_47585,c_11,c_711])).

cnf(c_47847,plain,
    ( r1_tarski(k6_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))),k6_relat_1(k6_relat_1(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_17426,c_47612])).

cnf(c_48957,plain,
    ( r1_tarski(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),k1_relat_1(k6_relat_1(k6_relat_1(X0)))) = iProver_top
    | v1_relat_1(k6_relat_1(k6_relat_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_47847,c_2429])).

cnf(c_48962,plain,
    ( r1_tarski(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),k6_relat_1(X0)) = iProver_top
    | v1_relat_1(k6_relat_1(k6_relat_1(X0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_48957,c_12])).

cnf(c_23477,plain,
    ( r1_tarski(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),k6_relat_1(X0)) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_14659,c_948])).

cnf(c_49902,plain,
    ( r1_tarski(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),k6_relat_1(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_48962,c_61,c_23477])).

cnf(c_49951,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_relat_1(k6_relat_1(X0))) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_49902,c_2429])).

cnf(c_49956,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_49951,c_12])).

cnf(c_53020,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_49956,c_61])).

cnf(c_53037,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
    inference(superposition,[status(thm)],[c_53020,c_1691])).

cnf(c_9904,plain,
    ( v1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1511,c_9897])).

cnf(c_10038,plain,
    ( k5_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),k6_relat_1(X3)) = k8_relat_1(X3,k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) ),
    inference(superposition,[status(thm)],[c_9904,c_488])).

cnf(c_7964,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k1_setfam_1(k2_enumset1(X2,X2,X2,X3))) = k5_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3),k6_relat_1(X0)) ),
    inference(superposition,[status(thm)],[c_1323,c_7300])).

cnf(c_7992,plain,
    ( k5_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),k6_relat_1(X3)) = k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X3),X1),X2),X0) ),
    inference(light_normalisation,[status(thm)],[c_7964,c_1914])).

cnf(c_10041,plain,
    ( k8_relat_1(X0,k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3)) = k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X3),X1) ),
    inference(light_normalisation,[status(thm)],[c_10038,c_7992])).

cnf(c_17687,plain,
    ( k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X1),X2) = k8_relat_1(X0,k7_relat_1(k6_relat_1(X2),X1)) ),
    inference(superposition,[status(thm)],[c_1380,c_10041])).

cnf(c_17769,plain,
    ( k8_relat_1(X0,k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1) ),
    inference(light_normalisation,[status(thm)],[c_17687,c_1380])).

cnf(c_23082,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k1_setfam_1(k2_enumset1(X2,X2,X2,X1))) = k8_relat_1(X0,k6_relat_1(k1_setfam_1(k2_enumset1(X2,X2,X2,X1)))) ),
    inference(superposition,[status(thm)],[c_14562,c_17769])).

cnf(c_7633,plain,
    ( k7_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X1),X0),X1),X0) = k6_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) ),
    inference(superposition,[status(thm)],[c_7317,c_1513])).

cnf(c_7634,plain,
    ( k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k6_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) ),
    inference(light_normalisation,[status(thm)],[c_7633,c_1719])).

cnf(c_8300,plain,
    ( k8_relat_1(X0,k6_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))) = k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X2,X2,X2,X1))) ),
    inference(superposition,[status(thm)],[c_7634,c_897])).

cnf(c_8307,plain,
    ( k8_relat_1(X0,k6_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) ),
    inference(demodulation,[status(thm)],[c_8300,c_897,c_1511])).

cnf(c_8416,plain,
    ( k8_relat_1(X0,k6_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1) ),
    inference(superposition,[status(thm)],[c_1,c_8307])).

cnf(c_23151,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k1_setfam_1(k2_enumset1(X2,X2,X2,X1))) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) ),
    inference(demodulation,[status(thm)],[c_23082,c_8416,c_11691])).

cnf(c_35734,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X0),X1) ),
    inference(superposition,[status(thm)],[c_711,c_23151])).

cnf(c_35959,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_35734,c_711])).

cnf(c_36017,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[status(thm)],[c_1,c_35959])).

cnf(c_53040,plain,
    ( k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_53037,c_36017])).

cnf(c_58963,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
    inference(superposition,[status(thm)],[c_53040,c_711])).

cnf(c_36673,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
    inference(superposition,[status(thm)],[c_36017,c_1380])).

cnf(c_36691,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k1_setfam_1(k2_enumset1(X0,X0,X0,X2))) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1) ),
    inference(superposition,[status(thm)],[c_36017,c_1727])).

cnf(c_36849,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(demodulation,[status(thm)],[c_36673,c_36017,c_36691])).

cnf(c_53033,plain,
    ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_53020])).

cnf(c_53304,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) = k6_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) ),
    inference(superposition,[status(thm)],[c_53033,c_1691])).

cnf(c_53307,plain,
    ( k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(light_normalisation,[status(thm)],[c_53304,c_35959])).

cnf(c_59167,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(light_normalisation,[status(thm)],[c_58963,c_36849,c_53307])).

cnf(c_19,negated_conjecture,
    ( k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_665,plain,
    ( k6_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK0))) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
    inference(demodulation,[status(thm)],[c_1,c_19])).

cnf(c_947,plain,
    ( k6_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK0))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_772,c_665])).

cnf(c_58565,plain,
    ( k7_relat_1(k6_relat_1(sK1),sK0) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_53040,c_947])).

cnf(c_59168,plain,
    ( k7_relat_1(k6_relat_1(sK1),sK0) != k7_relat_1(k6_relat_1(sK1),sK0) ),
    inference(demodulation,[status(thm)],[c_59167,c_58565])).

cnf(c_59169,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_59168])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : iproveropt_run.sh %d %s
% 0.11/0.32  % Computer   : n011.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 17:49:12 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  % Running in FOF mode
% 19.07/2.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.07/2.98  
% 19.07/2.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.07/2.98  
% 19.07/2.98  ------  iProver source info
% 19.07/2.98  
% 19.07/2.98  git: date: 2020-06-30 10:37:57 +0100
% 19.07/2.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.07/2.98  git: non_committed_changes: false
% 19.07/2.98  git: last_make_outside_of_git: false
% 19.07/2.98  
% 19.07/2.98  ------ 
% 19.07/2.98  
% 19.07/2.98  ------ Input Options
% 19.07/2.98  
% 19.07/2.98  --out_options                           all
% 19.07/2.98  --tptp_safe_out                         true
% 19.07/2.98  --problem_path                          ""
% 19.07/2.98  --include_path                          ""
% 19.07/2.98  --clausifier                            res/vclausify_rel
% 19.07/2.98  --clausifier_options                    ""
% 19.07/2.98  --stdin                                 false
% 19.07/2.98  --stats_out                             all
% 19.07/2.98  
% 19.07/2.98  ------ General Options
% 19.07/2.98  
% 19.07/2.98  --fof                                   false
% 19.07/2.98  --time_out_real                         305.
% 19.07/2.98  --time_out_virtual                      -1.
% 19.07/2.98  --symbol_type_check                     false
% 19.07/2.98  --clausify_out                          false
% 19.07/2.98  --sig_cnt_out                           false
% 19.07/2.98  --trig_cnt_out                          false
% 19.07/2.98  --trig_cnt_out_tolerance                1.
% 19.07/2.98  --trig_cnt_out_sk_spl                   false
% 19.07/2.98  --abstr_cl_out                          false
% 19.07/2.98  
% 19.07/2.98  ------ Global Options
% 19.07/2.98  
% 19.07/2.98  --schedule                              default
% 19.07/2.98  --add_important_lit                     false
% 19.07/2.98  --prop_solver_per_cl                    1000
% 19.07/2.98  --min_unsat_core                        false
% 19.07/2.98  --soft_assumptions                      false
% 19.07/2.98  --soft_lemma_size                       3
% 19.07/2.98  --prop_impl_unit_size                   0
% 19.07/2.98  --prop_impl_unit                        []
% 19.07/2.98  --share_sel_clauses                     true
% 19.07/2.98  --reset_solvers                         false
% 19.07/2.98  --bc_imp_inh                            [conj_cone]
% 19.07/2.98  --conj_cone_tolerance                   3.
% 19.07/2.98  --extra_neg_conj                        none
% 19.07/2.98  --large_theory_mode                     true
% 19.07/2.98  --prolific_symb_bound                   200
% 19.07/2.98  --lt_threshold                          2000
% 19.07/2.98  --clause_weak_htbl                      true
% 19.07/2.98  --gc_record_bc_elim                     false
% 19.07/2.98  
% 19.07/2.98  ------ Preprocessing Options
% 19.07/2.98  
% 19.07/2.98  --preprocessing_flag                    true
% 19.07/2.98  --time_out_prep_mult                    0.1
% 19.07/2.98  --splitting_mode                        input
% 19.07/2.98  --splitting_grd                         true
% 19.07/2.98  --splitting_cvd                         false
% 19.07/2.98  --splitting_cvd_svl                     false
% 19.07/2.98  --splitting_nvd                         32
% 19.07/2.98  --sub_typing                            true
% 19.07/2.98  --prep_gs_sim                           true
% 19.07/2.98  --prep_unflatten                        true
% 19.07/2.98  --prep_res_sim                          true
% 19.07/2.98  --prep_upred                            true
% 19.07/2.98  --prep_sem_filter                       exhaustive
% 19.07/2.98  --prep_sem_filter_out                   false
% 19.07/2.98  --pred_elim                             true
% 19.07/2.98  --res_sim_input                         true
% 19.07/2.98  --eq_ax_congr_red                       true
% 19.07/2.98  --pure_diseq_elim                       true
% 19.07/2.98  --brand_transform                       false
% 19.07/2.98  --non_eq_to_eq                          false
% 19.07/2.98  --prep_def_merge                        true
% 19.07/2.98  --prep_def_merge_prop_impl              false
% 19.07/2.98  --prep_def_merge_mbd                    true
% 19.07/2.98  --prep_def_merge_tr_red                 false
% 19.07/2.98  --prep_def_merge_tr_cl                  false
% 19.07/2.98  --smt_preprocessing                     true
% 19.07/2.98  --smt_ac_axioms                         fast
% 19.07/2.98  --preprocessed_out                      false
% 19.07/2.98  --preprocessed_stats                    false
% 19.07/2.98  
% 19.07/2.98  ------ Abstraction refinement Options
% 19.07/2.98  
% 19.07/2.98  --abstr_ref                             []
% 19.07/2.98  --abstr_ref_prep                        false
% 19.07/2.98  --abstr_ref_until_sat                   false
% 19.07/2.98  --abstr_ref_sig_restrict                funpre
% 19.07/2.98  --abstr_ref_af_restrict_to_split_sk     false
% 19.07/2.98  --abstr_ref_under                       []
% 19.07/2.98  
% 19.07/2.98  ------ SAT Options
% 19.07/2.98  
% 19.07/2.98  --sat_mode                              false
% 19.07/2.98  --sat_fm_restart_options                ""
% 19.07/2.98  --sat_gr_def                            false
% 19.07/2.98  --sat_epr_types                         true
% 19.07/2.98  --sat_non_cyclic_types                  false
% 19.07/2.98  --sat_finite_models                     false
% 19.07/2.98  --sat_fm_lemmas                         false
% 19.07/2.98  --sat_fm_prep                           false
% 19.07/2.98  --sat_fm_uc_incr                        true
% 19.07/2.98  --sat_out_model                         small
% 19.07/2.98  --sat_out_clauses                       false
% 19.07/2.98  
% 19.07/2.98  ------ QBF Options
% 19.07/2.98  
% 19.07/2.98  --qbf_mode                              false
% 19.07/2.98  --qbf_elim_univ                         false
% 19.07/2.98  --qbf_dom_inst                          none
% 19.07/2.98  --qbf_dom_pre_inst                      false
% 19.07/2.98  --qbf_sk_in                             false
% 19.07/2.98  --qbf_pred_elim                         true
% 19.07/2.98  --qbf_split                             512
% 19.07/2.98  
% 19.07/2.98  ------ BMC1 Options
% 19.07/2.98  
% 19.07/2.98  --bmc1_incremental                      false
% 19.07/2.98  --bmc1_axioms                           reachable_all
% 19.07/2.98  --bmc1_min_bound                        0
% 19.07/2.98  --bmc1_max_bound                        -1
% 19.07/2.98  --bmc1_max_bound_default                -1
% 19.07/2.98  --bmc1_symbol_reachability              true
% 19.07/2.98  --bmc1_property_lemmas                  false
% 19.07/2.98  --bmc1_k_induction                      false
% 19.07/2.98  --bmc1_non_equiv_states                 false
% 19.07/2.98  --bmc1_deadlock                         false
% 19.07/2.98  --bmc1_ucm                              false
% 19.07/2.98  --bmc1_add_unsat_core                   none
% 19.07/2.98  --bmc1_unsat_core_children              false
% 19.07/2.98  --bmc1_unsat_core_extrapolate_axioms    false
% 19.07/2.98  --bmc1_out_stat                         full
% 19.07/2.98  --bmc1_ground_init                      false
% 19.07/2.98  --bmc1_pre_inst_next_state              false
% 19.07/2.98  --bmc1_pre_inst_state                   false
% 19.07/2.98  --bmc1_pre_inst_reach_state             false
% 19.07/2.98  --bmc1_out_unsat_core                   false
% 19.07/2.98  --bmc1_aig_witness_out                  false
% 19.07/2.98  --bmc1_verbose                          false
% 19.07/2.98  --bmc1_dump_clauses_tptp                false
% 19.07/2.98  --bmc1_dump_unsat_core_tptp             false
% 19.07/2.98  --bmc1_dump_file                        -
% 19.07/2.98  --bmc1_ucm_expand_uc_limit              128
% 19.07/2.98  --bmc1_ucm_n_expand_iterations          6
% 19.07/2.98  --bmc1_ucm_extend_mode                  1
% 19.07/2.98  --bmc1_ucm_init_mode                    2
% 19.07/2.98  --bmc1_ucm_cone_mode                    none
% 19.07/2.98  --bmc1_ucm_reduced_relation_type        0
% 19.07/2.98  --bmc1_ucm_relax_model                  4
% 19.07/2.98  --bmc1_ucm_full_tr_after_sat            true
% 19.07/2.98  --bmc1_ucm_expand_neg_assumptions       false
% 19.07/2.98  --bmc1_ucm_layered_model                none
% 19.07/2.98  --bmc1_ucm_max_lemma_size               10
% 19.07/2.98  
% 19.07/2.98  ------ AIG Options
% 19.07/2.98  
% 19.07/2.98  --aig_mode                              false
% 19.07/2.98  
% 19.07/2.98  ------ Instantiation Options
% 19.07/2.98  
% 19.07/2.98  --instantiation_flag                    true
% 19.07/2.98  --inst_sos_flag                         true
% 19.07/2.98  --inst_sos_phase                        true
% 19.07/2.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.07/2.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.07/2.98  --inst_lit_sel_side                     num_symb
% 19.07/2.98  --inst_solver_per_active                1400
% 19.07/2.98  --inst_solver_calls_frac                1.
% 19.07/2.98  --inst_passive_queue_type               priority_queues
% 19.07/2.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.07/2.98  --inst_passive_queues_freq              [25;2]
% 19.07/2.98  --inst_dismatching                      true
% 19.07/2.98  --inst_eager_unprocessed_to_passive     true
% 19.07/2.98  --inst_prop_sim_given                   true
% 19.07/2.98  --inst_prop_sim_new                     false
% 19.07/2.98  --inst_subs_new                         false
% 19.07/2.98  --inst_eq_res_simp                      false
% 19.07/2.98  --inst_subs_given                       false
% 19.07/2.98  --inst_orphan_elimination               true
% 19.07/2.98  --inst_learning_loop_flag               true
% 19.07/2.98  --inst_learning_start                   3000
% 19.07/2.98  --inst_learning_factor                  2
% 19.07/2.98  --inst_start_prop_sim_after_learn       3
% 19.07/2.98  --inst_sel_renew                        solver
% 19.07/2.98  --inst_lit_activity_flag                true
% 19.07/2.98  --inst_restr_to_given                   false
% 19.07/2.98  --inst_activity_threshold               500
% 19.07/2.98  --inst_out_proof                        true
% 19.07/2.98  
% 19.07/2.98  ------ Resolution Options
% 19.07/2.98  
% 19.07/2.98  --resolution_flag                       true
% 19.07/2.98  --res_lit_sel                           adaptive
% 19.07/2.98  --res_lit_sel_side                      none
% 19.07/2.98  --res_ordering                          kbo
% 19.07/2.98  --res_to_prop_solver                    active
% 19.07/2.98  --res_prop_simpl_new                    false
% 19.07/2.98  --res_prop_simpl_given                  true
% 19.07/2.98  --res_passive_queue_type                priority_queues
% 19.07/2.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.07/2.98  --res_passive_queues_freq               [15;5]
% 19.07/2.98  --res_forward_subs                      full
% 19.07/2.98  --res_backward_subs                     full
% 19.07/2.98  --res_forward_subs_resolution           true
% 19.07/2.98  --res_backward_subs_resolution          true
% 19.07/2.98  --res_orphan_elimination                true
% 19.07/2.98  --res_time_limit                        2.
% 19.07/2.98  --res_out_proof                         true
% 19.07/2.98  
% 19.07/2.98  ------ Superposition Options
% 19.07/2.98  
% 19.07/2.98  --superposition_flag                    true
% 19.07/2.98  --sup_passive_queue_type                priority_queues
% 19.07/2.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.07/2.98  --sup_passive_queues_freq               [8;1;4]
% 19.07/2.98  --demod_completeness_check              fast
% 19.07/2.98  --demod_use_ground                      true
% 19.07/2.98  --sup_to_prop_solver                    passive
% 19.07/2.98  --sup_prop_simpl_new                    true
% 19.07/2.98  --sup_prop_simpl_given                  true
% 19.07/2.98  --sup_fun_splitting                     true
% 19.07/2.98  --sup_smt_interval                      50000
% 19.07/2.98  
% 19.07/2.98  ------ Superposition Simplification Setup
% 19.07/2.98  
% 19.07/2.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.07/2.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.07/2.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.07/2.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.07/2.98  --sup_full_triv                         [TrivRules;PropSubs]
% 19.07/2.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.07/2.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.07/2.98  --sup_immed_triv                        [TrivRules]
% 19.07/2.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.07/2.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.07/2.98  --sup_immed_bw_main                     []
% 19.07/2.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.07/2.98  --sup_input_triv                        [Unflattening;TrivRules]
% 19.07/2.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.07/2.98  --sup_input_bw                          []
% 19.07/2.98  
% 19.07/2.98  ------ Combination Options
% 19.07/2.98  
% 19.07/2.98  --comb_res_mult                         3
% 19.07/2.98  --comb_sup_mult                         2
% 19.07/2.98  --comb_inst_mult                        10
% 19.07/2.98  
% 19.07/2.98  ------ Debug Options
% 19.07/2.98  
% 19.07/2.98  --dbg_backtrace                         false
% 19.07/2.98  --dbg_dump_prop_clauses                 false
% 19.07/2.98  --dbg_dump_prop_clauses_file            -
% 19.07/2.98  --dbg_out_stat                          false
% 19.07/2.98  ------ Parsing...
% 19.07/2.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.07/2.98  
% 19.07/2.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 19.07/2.98  
% 19.07/2.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.07/2.98  
% 19.07/2.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.07/2.98  ------ Proving...
% 19.07/2.98  ------ Problem Properties 
% 19.07/2.98  
% 19.07/2.98  
% 19.07/2.98  clauses                                 20
% 19.07/2.98  conjectures                             1
% 19.07/2.98  EPR                                     0
% 19.07/2.98  Horn                                    20
% 19.07/2.98  unary                                   5
% 19.07/2.98  binary                                  9
% 19.07/2.98  lits                                    43
% 19.07/2.98  lits eq                                 13
% 19.07/2.98  fd_pure                                 0
% 19.07/2.98  fd_pseudo                               0
% 19.07/2.98  fd_cond                                 0
% 19.07/2.98  fd_pseudo_cond                          0
% 19.07/2.98  AC symbols                              0
% 19.07/2.98  
% 19.07/2.98  ------ Schedule dynamic 5 is on 
% 19.07/2.98  
% 19.07/2.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 19.07/2.98  
% 19.07/2.98  
% 19.07/2.98  ------ 
% 19.07/2.98  Current options:
% 19.07/2.98  ------ 
% 19.07/2.98  
% 19.07/2.98  ------ Input Options
% 19.07/2.98  
% 19.07/2.98  --out_options                           all
% 19.07/2.98  --tptp_safe_out                         true
% 19.07/2.98  --problem_path                          ""
% 19.07/2.98  --include_path                          ""
% 19.07/2.98  --clausifier                            res/vclausify_rel
% 19.07/2.98  --clausifier_options                    ""
% 19.07/2.98  --stdin                                 false
% 19.07/2.98  --stats_out                             all
% 19.07/2.98  
% 19.07/2.98  ------ General Options
% 19.07/2.98  
% 19.07/2.98  --fof                                   false
% 19.07/2.98  --time_out_real                         305.
% 19.07/2.98  --time_out_virtual                      -1.
% 19.07/2.98  --symbol_type_check                     false
% 19.07/2.98  --clausify_out                          false
% 19.07/2.98  --sig_cnt_out                           false
% 19.07/2.98  --trig_cnt_out                          false
% 19.07/2.98  --trig_cnt_out_tolerance                1.
% 19.07/2.98  --trig_cnt_out_sk_spl                   false
% 19.07/2.98  --abstr_cl_out                          false
% 19.07/2.98  
% 19.07/2.98  ------ Global Options
% 19.07/2.98  
% 19.07/2.98  --schedule                              default
% 19.07/2.98  --add_important_lit                     false
% 19.07/2.98  --prop_solver_per_cl                    1000
% 19.07/2.98  --min_unsat_core                        false
% 19.07/2.98  --soft_assumptions                      false
% 19.07/2.98  --soft_lemma_size                       3
% 19.07/2.98  --prop_impl_unit_size                   0
% 19.07/2.98  --prop_impl_unit                        []
% 19.07/2.98  --share_sel_clauses                     true
% 19.07/2.98  --reset_solvers                         false
% 19.07/2.98  --bc_imp_inh                            [conj_cone]
% 19.07/2.98  --conj_cone_tolerance                   3.
% 19.07/2.98  --extra_neg_conj                        none
% 19.07/2.98  --large_theory_mode                     true
% 19.07/2.98  --prolific_symb_bound                   200
% 19.07/2.98  --lt_threshold                          2000
% 19.07/2.98  --clause_weak_htbl                      true
% 19.07/2.98  --gc_record_bc_elim                     false
% 19.07/2.98  
% 19.07/2.98  ------ Preprocessing Options
% 19.07/2.98  
% 19.07/2.98  --preprocessing_flag                    true
% 19.07/2.98  --time_out_prep_mult                    0.1
% 19.07/2.98  --splitting_mode                        input
% 19.07/2.98  --splitting_grd                         true
% 19.07/2.98  --splitting_cvd                         false
% 19.07/2.98  --splitting_cvd_svl                     false
% 19.07/2.98  --splitting_nvd                         32
% 19.07/2.98  --sub_typing                            true
% 19.07/2.98  --prep_gs_sim                           true
% 19.07/2.98  --prep_unflatten                        true
% 19.07/2.98  --prep_res_sim                          true
% 19.07/2.98  --prep_upred                            true
% 19.07/2.98  --prep_sem_filter                       exhaustive
% 19.07/2.98  --prep_sem_filter_out                   false
% 19.07/2.98  --pred_elim                             true
% 19.07/2.98  --res_sim_input                         true
% 19.07/2.98  --eq_ax_congr_red                       true
% 19.07/2.98  --pure_diseq_elim                       true
% 19.07/2.98  --brand_transform                       false
% 19.07/2.98  --non_eq_to_eq                          false
% 19.07/2.98  --prep_def_merge                        true
% 19.07/2.98  --prep_def_merge_prop_impl              false
% 19.07/2.98  --prep_def_merge_mbd                    true
% 19.07/2.98  --prep_def_merge_tr_red                 false
% 19.07/2.98  --prep_def_merge_tr_cl                  false
% 19.07/2.98  --smt_preprocessing                     true
% 19.07/2.98  --smt_ac_axioms                         fast
% 19.07/2.98  --preprocessed_out                      false
% 19.07/2.98  --preprocessed_stats                    false
% 19.07/2.98  
% 19.07/2.98  ------ Abstraction refinement Options
% 19.07/2.98  
% 19.07/2.98  --abstr_ref                             []
% 19.07/2.98  --abstr_ref_prep                        false
% 19.07/2.98  --abstr_ref_until_sat                   false
% 19.07/2.98  --abstr_ref_sig_restrict                funpre
% 19.07/2.98  --abstr_ref_af_restrict_to_split_sk     false
% 19.07/2.98  --abstr_ref_under                       []
% 19.07/2.98  
% 19.07/2.98  ------ SAT Options
% 19.07/2.98  
% 19.07/2.98  --sat_mode                              false
% 19.07/2.98  --sat_fm_restart_options                ""
% 19.07/2.98  --sat_gr_def                            false
% 19.07/2.98  --sat_epr_types                         true
% 19.07/2.98  --sat_non_cyclic_types                  false
% 19.07/2.98  --sat_finite_models                     false
% 19.07/2.98  --sat_fm_lemmas                         false
% 19.07/2.98  --sat_fm_prep                           false
% 19.07/2.98  --sat_fm_uc_incr                        true
% 19.07/2.98  --sat_out_model                         small
% 19.07/2.98  --sat_out_clauses                       false
% 19.07/2.98  
% 19.07/2.98  ------ QBF Options
% 19.07/2.98  
% 19.07/2.98  --qbf_mode                              false
% 19.07/2.98  --qbf_elim_univ                         false
% 19.07/2.98  --qbf_dom_inst                          none
% 19.07/2.98  --qbf_dom_pre_inst                      false
% 19.07/2.98  --qbf_sk_in                             false
% 19.07/2.98  --qbf_pred_elim                         true
% 19.07/2.98  --qbf_split                             512
% 19.07/2.98  
% 19.07/2.98  ------ BMC1 Options
% 19.07/2.98  
% 19.07/2.98  --bmc1_incremental                      false
% 19.07/2.98  --bmc1_axioms                           reachable_all
% 19.07/2.98  --bmc1_min_bound                        0
% 19.07/2.98  --bmc1_max_bound                        -1
% 19.07/2.98  --bmc1_max_bound_default                -1
% 19.07/2.98  --bmc1_symbol_reachability              true
% 19.07/2.98  --bmc1_property_lemmas                  false
% 19.07/2.98  --bmc1_k_induction                      false
% 19.07/2.98  --bmc1_non_equiv_states                 false
% 19.07/2.98  --bmc1_deadlock                         false
% 19.07/2.98  --bmc1_ucm                              false
% 19.07/2.98  --bmc1_add_unsat_core                   none
% 19.07/2.98  --bmc1_unsat_core_children              false
% 19.07/2.98  --bmc1_unsat_core_extrapolate_axioms    false
% 19.07/2.98  --bmc1_out_stat                         full
% 19.07/2.98  --bmc1_ground_init                      false
% 19.07/2.98  --bmc1_pre_inst_next_state              false
% 19.07/2.98  --bmc1_pre_inst_state                   false
% 19.07/2.98  --bmc1_pre_inst_reach_state             false
% 19.07/2.98  --bmc1_out_unsat_core                   false
% 19.07/2.98  --bmc1_aig_witness_out                  false
% 19.07/2.98  --bmc1_verbose                          false
% 19.07/2.98  --bmc1_dump_clauses_tptp                false
% 19.07/2.98  --bmc1_dump_unsat_core_tptp             false
% 19.07/2.98  --bmc1_dump_file                        -
% 19.07/2.98  --bmc1_ucm_expand_uc_limit              128
% 19.07/2.98  --bmc1_ucm_n_expand_iterations          6
% 19.07/2.98  --bmc1_ucm_extend_mode                  1
% 19.07/2.98  --bmc1_ucm_init_mode                    2
% 19.07/2.98  --bmc1_ucm_cone_mode                    none
% 19.07/2.98  --bmc1_ucm_reduced_relation_type        0
% 19.07/2.98  --bmc1_ucm_relax_model                  4
% 19.07/2.98  --bmc1_ucm_full_tr_after_sat            true
% 19.07/2.98  --bmc1_ucm_expand_neg_assumptions       false
% 19.07/2.98  --bmc1_ucm_layered_model                none
% 19.07/2.98  --bmc1_ucm_max_lemma_size               10
% 19.07/2.98  
% 19.07/2.98  ------ AIG Options
% 19.07/2.98  
% 19.07/2.98  --aig_mode                              false
% 19.07/2.98  
% 19.07/2.98  ------ Instantiation Options
% 19.07/2.98  
% 19.07/2.98  --instantiation_flag                    true
% 19.07/2.98  --inst_sos_flag                         true
% 19.07/2.98  --inst_sos_phase                        true
% 19.07/2.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.07/2.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.07/2.98  --inst_lit_sel_side                     none
% 19.07/2.98  --inst_solver_per_active                1400
% 19.07/2.98  --inst_solver_calls_frac                1.
% 19.07/2.98  --inst_passive_queue_type               priority_queues
% 19.07/2.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.07/2.98  --inst_passive_queues_freq              [25;2]
% 19.07/2.98  --inst_dismatching                      true
% 19.07/2.98  --inst_eager_unprocessed_to_passive     true
% 19.07/2.98  --inst_prop_sim_given                   true
% 19.07/2.98  --inst_prop_sim_new                     false
% 19.07/2.98  --inst_subs_new                         false
% 19.07/2.98  --inst_eq_res_simp                      false
% 19.07/2.98  --inst_subs_given                       false
% 19.07/2.98  --inst_orphan_elimination               true
% 19.07/2.98  --inst_learning_loop_flag               true
% 19.07/2.98  --inst_learning_start                   3000
% 19.07/2.98  --inst_learning_factor                  2
% 19.07/2.98  --inst_start_prop_sim_after_learn       3
% 19.07/2.98  --inst_sel_renew                        solver
% 19.07/2.98  --inst_lit_activity_flag                true
% 19.07/2.98  --inst_restr_to_given                   false
% 19.07/2.98  --inst_activity_threshold               500
% 19.07/2.98  --inst_out_proof                        true
% 19.07/2.98  
% 19.07/2.98  ------ Resolution Options
% 19.07/2.98  
% 19.07/2.98  --resolution_flag                       false
% 19.07/2.98  --res_lit_sel                           adaptive
% 19.07/2.98  --res_lit_sel_side                      none
% 19.07/2.98  --res_ordering                          kbo
% 19.07/2.98  --res_to_prop_solver                    active
% 19.07/2.98  --res_prop_simpl_new                    false
% 19.07/2.98  --res_prop_simpl_given                  true
% 19.07/2.98  --res_passive_queue_type                priority_queues
% 19.07/2.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.07/2.98  --res_passive_queues_freq               [15;5]
% 19.07/2.98  --res_forward_subs                      full
% 19.07/2.98  --res_backward_subs                     full
% 19.07/2.98  --res_forward_subs_resolution           true
% 19.07/2.98  --res_backward_subs_resolution          true
% 19.07/2.98  --res_orphan_elimination                true
% 19.07/2.98  --res_time_limit                        2.
% 19.07/2.98  --res_out_proof                         true
% 19.07/2.98  
% 19.07/2.98  ------ Superposition Options
% 19.07/2.98  
% 19.07/2.98  --superposition_flag                    true
% 19.07/2.98  --sup_passive_queue_type                priority_queues
% 19.07/2.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.07/2.98  --sup_passive_queues_freq               [8;1;4]
% 19.07/2.98  --demod_completeness_check              fast
% 19.07/2.98  --demod_use_ground                      true
% 19.07/2.98  --sup_to_prop_solver                    passive
% 19.07/2.98  --sup_prop_simpl_new                    true
% 19.07/2.98  --sup_prop_simpl_given                  true
% 19.07/2.98  --sup_fun_splitting                     true
% 19.07/2.98  --sup_smt_interval                      50000
% 19.07/2.98  
% 19.07/2.98  ------ Superposition Simplification Setup
% 19.07/2.98  
% 19.07/2.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.07/2.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.07/2.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.07/2.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.07/2.98  --sup_full_triv                         [TrivRules;PropSubs]
% 19.07/2.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.07/2.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.07/2.98  --sup_immed_triv                        [TrivRules]
% 19.07/2.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.07/2.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.07/2.98  --sup_immed_bw_main                     []
% 19.07/2.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.07/2.98  --sup_input_triv                        [Unflattening;TrivRules]
% 19.07/2.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.07/2.98  --sup_input_bw                          []
% 19.07/2.98  
% 19.07/2.98  ------ Combination Options
% 19.07/2.98  
% 19.07/2.98  --comb_res_mult                         3
% 19.07/2.98  --comb_sup_mult                         2
% 19.07/2.98  --comb_inst_mult                        10
% 19.07/2.98  
% 19.07/2.98  ------ Debug Options
% 19.07/2.98  
% 19.07/2.98  --dbg_backtrace                         false
% 19.07/2.98  --dbg_dump_prop_clauses                 false
% 19.07/2.98  --dbg_dump_prop_clauses_file            -
% 19.07/2.98  --dbg_out_stat                          false
% 19.07/2.98  
% 19.07/2.98  
% 19.07/2.98  
% 19.07/2.98  
% 19.07/2.98  ------ Proving...
% 19.07/2.98  
% 19.07/2.98  
% 19.07/2.98  % SZS status Theorem for theBenchmark.p
% 19.07/2.98  
% 19.07/2.98   Resolution empty clause
% 19.07/2.98  
% 19.07/2.98  % SZS output start CNFRefutation for theBenchmark.p
% 19.07/2.98  
% 19.07/2.98  fof(f2,axiom,(
% 19.07/2.98    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 19.07/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.07/2.98  
% 19.07/2.98  fof(f43,plain,(
% 19.07/2.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 19.07/2.98    inference(cnf_transformation,[],[f2])).
% 19.07/2.98  
% 19.07/2.98  fof(f3,axiom,(
% 19.07/2.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 19.07/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.07/2.98  
% 19.07/2.98  fof(f44,plain,(
% 19.07/2.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 19.07/2.98    inference(cnf_transformation,[],[f3])).
% 19.07/2.98  
% 19.07/2.98  fof(f4,axiom,(
% 19.07/2.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 19.07/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.07/2.98  
% 19.07/2.98  fof(f45,plain,(
% 19.07/2.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 19.07/2.98    inference(cnf_transformation,[],[f4])).
% 19.07/2.98  
% 19.07/2.98  fof(f65,plain,(
% 19.07/2.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 19.07/2.98    inference(definition_unfolding,[],[f44,f45])).
% 19.07/2.98  
% 19.07/2.98  fof(f68,plain,(
% 19.07/2.98    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 19.07/2.98    inference(definition_unfolding,[],[f43,f65,f65])).
% 19.07/2.98  
% 19.07/2.98  fof(f7,axiom,(
% 19.07/2.98    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 19.07/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.07/2.98  
% 19.07/2.98  fof(f48,plain,(
% 19.07/2.98    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 19.07/2.98    inference(cnf_transformation,[],[f7])).
% 19.07/2.98  
% 19.07/2.98  fof(f9,axiom,(
% 19.07/2.98    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1))),
% 19.07/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.07/2.98  
% 19.07/2.98  fof(f26,plain,(
% 19.07/2.98    ! [X0,X1,X2] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 19.07/2.98    inference(ennf_transformation,[],[f9])).
% 19.07/2.98  
% 19.07/2.98  fof(f50,plain,(
% 19.07/2.98    ( ! [X2,X0,X1] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 19.07/2.98    inference(cnf_transformation,[],[f26])).
% 19.07/2.98  
% 19.07/2.98  fof(f5,axiom,(
% 19.07/2.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 19.07/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.07/2.98  
% 19.07/2.98  fof(f46,plain,(
% 19.07/2.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 19.07/2.98    inference(cnf_transformation,[],[f5])).
% 19.07/2.98  
% 19.07/2.98  fof(f66,plain,(
% 19.07/2.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 19.07/2.98    inference(definition_unfolding,[],[f46,f65])).
% 19.07/2.98  
% 19.07/2.98  fof(f70,plain,(
% 19.07/2.98    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) | ~v1_relat_1(X2)) )),
% 19.07/2.98    inference(definition_unfolding,[],[f50,f66])).
% 19.07/2.98  
% 19.07/2.98  fof(f19,axiom,(
% 19.07/2.98    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 19.07/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.07/2.98  
% 19.07/2.98  fof(f38,plain,(
% 19.07/2.98    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 19.07/2.98    inference(ennf_transformation,[],[f19])).
% 19.07/2.98  
% 19.07/2.98  fof(f63,plain,(
% 19.07/2.98    ( ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 19.07/2.98    inference(cnf_transformation,[],[f38])).
% 19.07/2.98  
% 19.07/2.98  fof(f14,axiom,(
% 19.07/2.98    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 19.07/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.07/2.98  
% 19.07/2.98  fof(f56,plain,(
% 19.07/2.98    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 19.07/2.98    inference(cnf_transformation,[],[f14])).
% 19.07/2.98  
% 19.07/2.98  fof(f12,axiom,(
% 19.07/2.98    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)))),
% 19.07/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.07/2.98  
% 19.07/2.98  fof(f29,plain,(
% 19.07/2.98    ! [X0,X1,X2] : (k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 19.07/2.98    inference(ennf_transformation,[],[f12])).
% 19.07/2.98  
% 19.07/2.98  fof(f53,plain,(
% 19.07/2.98    ( ! [X2,X0,X1] : (k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 19.07/2.98    inference(cnf_transformation,[],[f29])).
% 19.07/2.98  
% 19.07/2.98  fof(f11,axiom,(
% 19.07/2.98    ! [X0,X1] : (v1_relat_1(X1) => k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1))),
% 19.07/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.07/2.98  
% 19.07/2.98  fof(f28,plain,(
% 19.07/2.98    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1) | ~v1_relat_1(X1))),
% 19.07/2.98    inference(ennf_transformation,[],[f11])).
% 19.07/2.98  
% 19.07/2.98  fof(f52,plain,(
% 19.07/2.98    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = k8_relat_1(X0,X1) | ~v1_relat_1(X1)) )),
% 19.07/2.98    inference(cnf_transformation,[],[f28])).
% 19.07/2.98  
% 19.07/2.98  fof(f17,axiom,(
% 19.07/2.98    ! [X0,X1] : (v1_relat_1(X1) => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0))),
% 19.07/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.07/2.98  
% 19.07/2.98  fof(f35,plain,(
% 19.07/2.98    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 19.07/2.98    inference(ennf_transformation,[],[f17])).
% 19.07/2.98  
% 19.07/2.98  fof(f61,plain,(
% 19.07/2.98    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 19.07/2.98    inference(cnf_transformation,[],[f35])).
% 19.07/2.98  
% 19.07/2.98  fof(f57,plain,(
% 19.07/2.98    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 19.07/2.98    inference(cnf_transformation,[],[f14])).
% 19.07/2.98  
% 19.07/2.98  fof(f15,axiom,(
% 19.07/2.98    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 19.07/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.07/2.98  
% 19.07/2.98  fof(f32,plain,(
% 19.07/2.98    ! [X0,X1] : ((r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) | ~v1_relat_1(X1))),
% 19.07/2.98    inference(ennf_transformation,[],[f15])).
% 19.07/2.98  
% 19.07/2.98  fof(f59,plain,(
% 19.07/2.98    ( ! [X0,X1] : (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) | ~v1_relat_1(X1)) )),
% 19.07/2.98    inference(cnf_transformation,[],[f32])).
% 19.07/2.98  
% 19.07/2.98  fof(f16,axiom,(
% 19.07/2.98    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 19.07/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.07/2.98  
% 19.07/2.98  fof(f33,plain,(
% 19.07/2.98    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 19.07/2.98    inference(ennf_transformation,[],[f16])).
% 19.07/2.98  
% 19.07/2.98  fof(f34,plain,(
% 19.07/2.98    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 19.07/2.98    inference(flattening,[],[f33])).
% 19.07/2.98  
% 19.07/2.98  fof(f60,plain,(
% 19.07/2.98    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 19.07/2.98    inference(cnf_transformation,[],[f34])).
% 19.07/2.98  
% 19.07/2.98  fof(f1,axiom,(
% 19.07/2.98    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 19.07/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.07/2.98  
% 19.07/2.98  fof(f22,plain,(
% 19.07/2.98    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 19.07/2.98    inference(ennf_transformation,[],[f1])).
% 19.07/2.98  
% 19.07/2.98  fof(f42,plain,(
% 19.07/2.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 19.07/2.98    inference(cnf_transformation,[],[f22])).
% 19.07/2.98  
% 19.07/2.98  fof(f67,plain,(
% 19.07/2.98    ( ! [X0,X1] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 19.07/2.98    inference(definition_unfolding,[],[f42,f66])).
% 19.07/2.98  
% 19.07/2.98  fof(f8,axiom,(
% 19.07/2.98    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 19.07/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.07/2.98  
% 19.07/2.98  fof(f25,plain,(
% 19.07/2.98    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 19.07/2.98    inference(ennf_transformation,[],[f8])).
% 19.07/2.98  
% 19.07/2.98  fof(f49,plain,(
% 19.07/2.98    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 19.07/2.98    inference(cnf_transformation,[],[f25])).
% 19.07/2.98  
% 19.07/2.98  fof(f69,plain,(
% 19.07/2.98    ( ! [X0,X1] : (v1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) | ~v1_relat_1(X0)) )),
% 19.07/2.98    inference(definition_unfolding,[],[f49,f66])).
% 19.07/2.98  
% 19.07/2.98  fof(f58,plain,(
% 19.07/2.98    ( ! [X0,X1] : (r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) | ~v1_relat_1(X1)) )),
% 19.07/2.98    inference(cnf_transformation,[],[f32])).
% 19.07/2.98  
% 19.07/2.98  fof(f13,axiom,(
% 19.07/2.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 19.07/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.07/2.98  
% 19.07/2.98  fof(f30,plain,(
% 19.07/2.98    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 19.07/2.98    inference(ennf_transformation,[],[f13])).
% 19.07/2.98  
% 19.07/2.98  fof(f31,plain,(
% 19.07/2.98    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 19.07/2.98    inference(flattening,[],[f30])).
% 19.07/2.98  
% 19.07/2.98  fof(f54,plain,(
% 19.07/2.98    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 19.07/2.98    inference(cnf_transformation,[],[f31])).
% 19.07/2.98  
% 19.07/2.98  fof(f10,axiom,(
% 19.07/2.98    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k7_relat_1(X1,X0),X2) = k7_relat_1(k5_relat_1(X1,X2),X0)))),
% 19.07/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.07/2.98  
% 19.07/2.98  fof(f27,plain,(
% 19.07/2.98    ! [X0,X1] : (! [X2] : (k5_relat_1(k7_relat_1(X1,X0),X2) = k7_relat_1(k5_relat_1(X1,X2),X0) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 19.07/2.98    inference(ennf_transformation,[],[f10])).
% 19.07/2.98  
% 19.07/2.98  fof(f51,plain,(
% 19.07/2.98    ( ! [X2,X0,X1] : (k5_relat_1(k7_relat_1(X1,X0),X2) = k7_relat_1(k5_relat_1(X1,X2),X0) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 19.07/2.98    inference(cnf_transformation,[],[f27])).
% 19.07/2.98  
% 19.07/2.98  fof(f20,conjecture,(
% 19.07/2.98    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 19.07/2.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.07/2.98  
% 19.07/2.98  fof(f21,negated_conjecture,(
% 19.07/2.98    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 19.07/2.98    inference(negated_conjecture,[],[f20])).
% 19.07/2.98  
% 19.07/2.98  fof(f39,plain,(
% 19.07/2.98    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 19.07/2.98    inference(ennf_transformation,[],[f21])).
% 19.07/2.98  
% 19.07/2.98  fof(f40,plain,(
% 19.07/2.98    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 19.07/2.98    introduced(choice_axiom,[])).
% 19.07/2.98  
% 19.07/2.98  fof(f41,plain,(
% 19.07/2.98    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 19.07/2.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f39,f40])).
% 19.07/2.98  
% 19.07/2.98  fof(f64,plain,(
% 19.07/2.98    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 19.07/2.98    inference(cnf_transformation,[],[f41])).
% 19.07/2.98  
% 19.07/2.98  fof(f71,plain,(
% 19.07/2.98    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))),
% 19.07/2.98    inference(definition_unfolding,[],[f64,f66])).
% 19.07/2.98  
% 19.07/2.98  cnf(c_1,plain,
% 19.07/2.98      ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
% 19.07/2.98      inference(cnf_transformation,[],[f68]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_3,plain,
% 19.07/2.98      ( v1_relat_1(k6_relat_1(X0)) ),
% 19.07/2.98      inference(cnf_transformation,[],[f48]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_492,plain,
% 19.07/2.98      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 19.07/2.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_5,plain,
% 19.07/2.98      ( ~ v1_relat_1(X0)
% 19.07/2.98      | k7_relat_1(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2) ),
% 19.07/2.98      inference(cnf_transformation,[],[f70]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_490,plain,
% 19.07/2.98      ( k7_relat_1(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2)
% 19.07/2.98      | v1_relat_1(X0) != iProver_top ),
% 19.07/2.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_1323,plain,
% 19.07/2.98      ( k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_492,c_490]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_18,plain,
% 19.07/2.98      ( ~ v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0 ),
% 19.07/2.98      inference(cnf_transformation,[],[f63]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_479,plain,
% 19.07/2.98      ( k7_relat_1(X0,k1_relat_1(X0)) = X0 | v1_relat_1(X0) != iProver_top ),
% 19.07/2.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_710,plain,
% 19.07/2.98      ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0))) = k6_relat_1(X0) ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_492,c_479]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_12,plain,
% 19.07/2.98      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 19.07/2.98      inference(cnf_transformation,[],[f56]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_711,plain,
% 19.07/2.98      ( k7_relat_1(k6_relat_1(X0),X0) = k6_relat_1(X0) ),
% 19.07/2.98      inference(light_normalisation,[status(thm)],[c_710,c_12]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_1513,plain,
% 19.07/2.98      ( k7_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X0),X1) = k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_1323,c_711]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_7317,plain,
% 19.07/2.98      ( k7_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X1),X0) = k6_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_1,c_1513]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_8,plain,
% 19.07/2.98      ( ~ v1_relat_1(X0)
% 19.07/2.98      | k8_relat_1(X1,k7_relat_1(X0,X2)) = k7_relat_1(k8_relat_1(X1,X0),X2) ),
% 19.07/2.98      inference(cnf_transformation,[],[f53]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_487,plain,
% 19.07/2.98      ( k8_relat_1(X0,k7_relat_1(X1,X2)) = k7_relat_1(k8_relat_1(X0,X1),X2)
% 19.07/2.98      | v1_relat_1(X1) != iProver_top ),
% 19.07/2.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_1244,plain,
% 19.07/2.98      ( k8_relat_1(X0,k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k8_relat_1(X0,k6_relat_1(X1)),X2) ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_492,c_487]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_7,plain,
% 19.07/2.98      ( ~ v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0) ),
% 19.07/2.98      inference(cnf_transformation,[],[f52]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_488,plain,
% 19.07/2.98      ( k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0)
% 19.07/2.98      | v1_relat_1(X0) != iProver_top ),
% 19.07/2.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_896,plain,
% 19.07/2.98      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0)) ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_492,c_488]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_16,plain,
% 19.07/2.98      ( ~ v1_relat_1(X0) | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
% 19.07/2.98      inference(cnf_transformation,[],[f61]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_481,plain,
% 19.07/2.98      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
% 19.07/2.98      | v1_relat_1(X1) != iProver_top ),
% 19.07/2.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_772,plain,
% 19.07/2.98      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_492,c_481]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_897,plain,
% 19.07/2.98      ( k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
% 19.07/2.98      inference(light_normalisation,[status(thm)],[c_896,c_772]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_1247,plain,
% 19.07/2.98      ( k8_relat_1(X0,k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) ),
% 19.07/2.98      inference(light_normalisation,[status(thm)],[c_1244,c_897]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_1379,plain,
% 19.07/2.98      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X1) = k8_relat_1(X0,k6_relat_1(X1)) ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_711,c_1247]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_1380,plain,
% 19.07/2.98      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X1) = k7_relat_1(k6_relat_1(X0),X1) ),
% 19.07/2.98      inference(light_normalisation,[status(thm)],[c_1379,c_897]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_11,plain,
% 19.07/2.98      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 19.07/2.98      inference(cnf_transformation,[],[f57]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_7620,plain,
% 19.07/2.98      ( k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X1),X0)) = k1_setfam_1(k2_enumset1(X1,X1,X1,X0)) ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_7317,c_11]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_1511,plain,
% 19.07/2.98      ( k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1) ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_1,c_1323]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_1719,plain,
% 19.07/2.98      ( k7_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X1),X0) = k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_1511,c_711]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_7647,plain,
% 19.07/2.98      ( k2_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) = k1_setfam_1(k2_enumset1(X1,X1,X1,X0)) ),
% 19.07/2.98      inference(light_normalisation,[status(thm)],[c_7620,c_1719]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_13,plain,
% 19.07/2.98      ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) | ~ v1_relat_1(X1) ),
% 19.07/2.98      inference(cnf_transformation,[],[f59]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_484,plain,
% 19.07/2.98      ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) = iProver_top
% 19.07/2.98      | v1_relat_1(X1) != iProver_top ),
% 19.07/2.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_949,plain,
% 19.07/2.98      ( r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X0)) = iProver_top
% 19.07/2.98      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_772,c_484]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_61,plain,
% 19.07/2.98      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 19.07/2.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_1409,plain,
% 19.07/2.98      ( r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X0)) = iProver_top ),
% 19.07/2.98      inference(global_propositional_subsumption,[status(thm)],[c_949,c_61]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_15,plain,
% 19.07/2.98      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 19.07/2.98      | ~ v1_relat_1(X0)
% 19.07/2.98      | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
% 19.07/2.98      inference(cnf_transformation,[],[f60]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_482,plain,
% 19.07/2.98      ( k5_relat_1(X0,k6_relat_1(X1)) = X0
% 19.07/2.98      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 19.07/2.98      | v1_relat_1(X0) != iProver_top ),
% 19.07/2.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_767,plain,
% 19.07/2.98      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X0)
% 19.07/2.98      | r1_tarski(X0,X1) != iProver_top
% 19.07/2.98      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_11,c_482]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_1685,plain,
% 19.07/2.98      ( r1_tarski(X0,X1) != iProver_top
% 19.07/2.98      | k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X0) ),
% 19.07/2.98      inference(global_propositional_subsumption,[status(thm)],[c_767,c_61]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_1686,plain,
% 19.07/2.98      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X0)
% 19.07/2.98      | r1_tarski(X0,X1) != iProver_top ),
% 19.07/2.98      inference(renaming,[status(thm)],[c_1685]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_1691,plain,
% 19.07/2.98      ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X1)
% 19.07/2.98      | r1_tarski(X1,X0) != iProver_top ),
% 19.07/2.98      inference(demodulation,[status(thm)],[c_1686,c_772]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_1696,plain,
% 19.07/2.98      ( k7_relat_1(k6_relat_1(k6_relat_1(X0)),k7_relat_1(k6_relat_1(X0),X1)) = k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_1409,c_1691]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_1982,plain,
% 19.07/2.98      ( k6_relat_1(k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))) = k7_relat_1(k6_relat_1(k6_relat_1(X0)),k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_1323,c_1696]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_1514,plain,
% 19.07/2.98      ( r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),k6_relat_1(X0)) = iProver_top ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_1323,c_1409]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_1698,plain,
% 19.07/2.98      ( k7_relat_1(k6_relat_1(k6_relat_1(X0)),k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) = k6_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_1514,c_1691]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_1999,plain,
% 19.07/2.98      ( k6_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) = k6_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1)) ),
% 19.07/2.98      inference(light_normalisation,[status(thm)],[c_1982,c_1511,c_1698]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_7508,plain,
% 19.07/2.98      ( k6_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X0),X1)) = k6_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X0)))) ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_7317,c_1999]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_7716,plain,
% 19.07/2.98      ( k6_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) = k6_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X0)))) ),
% 19.07/2.98      inference(light_normalisation,[status(thm)],[c_7508,c_1513]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_9159,plain,
% 19.07/2.98      ( k1_relat_1(k6_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))))) = k6_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_7716,c_12]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_0,plain,
% 19.07/2.98      ( ~ r1_tarski(X0,X1) | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X0 ),
% 19.07/2.98      inference(cnf_transformation,[],[f67]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_494,plain,
% 19.07/2.98      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X0
% 19.07/2.98      | r1_tarski(X0,X1) != iProver_top ),
% 19.07/2.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_1022,plain,
% 19.07/2.98      ( k1_setfam_1(k2_enumset1(k5_relat_1(k6_relat_1(X0),X1),k5_relat_1(k6_relat_1(X0),X1),k5_relat_1(k6_relat_1(X0),X1),X1)) = k5_relat_1(k6_relat_1(X0),X1)
% 19.07/2.98      | v1_relat_1(X1) != iProver_top ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_484,c_494]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_7822,plain,
% 19.07/2.98      ( k2_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,k5_relat_1(k6_relat_1(X1),X0))))) = k5_relat_1(k6_relat_1(X1),X0)
% 19.07/2.98      | v1_relat_1(X0) != iProver_top ),
% 19.07/2.98      inference(demodulation,[status(thm)],[c_7647,c_1022]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_7825,plain,
% 19.07/2.98      ( k1_setfam_1(k2_enumset1(X0,X0,X0,k5_relat_1(k6_relat_1(X1),X0))) = k5_relat_1(k6_relat_1(X1),X0)
% 19.07/2.98      | v1_relat_1(X0) != iProver_top ),
% 19.07/2.98      inference(demodulation,[status(thm)],[c_7822,c_11]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_8721,plain,
% 19.07/2.98      ( k1_setfam_1(k2_enumset1(k6_relat_1(X0),k6_relat_1(X0),k6_relat_1(X0),k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_492,c_7825]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_8724,plain,
% 19.07/2.98      ( k1_setfam_1(k2_enumset1(k6_relat_1(X0),k6_relat_1(X0),k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
% 19.07/2.98      inference(demodulation,[status(thm)],[c_8721,c_772]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_4,plain,
% 19.07/2.98      ( ~ v1_relat_1(X0) | v1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
% 19.07/2.98      inference(cnf_transformation,[],[f69]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_491,plain,
% 19.07/2.98      ( v1_relat_1(X0) != iProver_top
% 19.07/2.98      | v1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = iProver_top ),
% 19.07/2.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_9864,plain,
% 19.07/2.98      ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top
% 19.07/2.98      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_8724,c_491]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_9897,plain,
% 19.07/2.98      ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top ),
% 19.07/2.98      inference(global_propositional_subsumption,[status(thm)],[c_9864,c_61]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_9924,plain,
% 19.07/2.98      ( k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0) ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_9897,c_481]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_11642,plain,
% 19.07/2.98      ( k5_relat_1(k1_relat_1(k6_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))))),k7_relat_1(k6_relat_1(X2),X3)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X3),k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_9159,c_9924]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_9930,plain,
% 19.07/2.98      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k1_setfam_1(k2_enumset1(X2,X2,X2,X3))) = k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),X3) ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_9897,c_490]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_11691,plain,
% 19.07/2.98      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k1_setfam_1(k2_enumset1(X2,X2,X2,X3))) = k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X3),X2) ),
% 19.07/2.98      inference(demodulation,[status(thm)],[c_11642,c_12,c_9924,c_9930]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_12773,plain,
% 19.07/2.98      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k2_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X2,X2,X2,X3))))) = k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),X3) ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_7647,c_11691]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_12840,plain,
% 19.07/2.98      ( k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),X3) = k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X3),X2) ),
% 19.07/2.98      inference(demodulation,[status(thm)],[c_12773,c_11,c_11691]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_13007,plain,
% 19.07/2.98      ( k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_1380,c_12840]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_1727,plain,
% 19.07/2.98      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1) ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_1511,c_1323]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_1912,plain,
% 19.07/2.98      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) = k7_relat_1(k6_relat_1(X0),X1) ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_711,c_1727]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_1970,plain,
% 19.07/2.98      ( k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) = k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),X0) ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_1323,c_1912]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_1977,plain,
% 19.07/2.98      ( k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),X0) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1) ),
% 19.07/2.98      inference(light_normalisation,[status(thm)],[c_1970,c_1511]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_2735,plain,
% 19.07/2.98      ( k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),X0) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_1727,c_1977]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_3864,plain,
% 19.07/2.98      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X1,X1,X1,X2))),X3) = k7_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),X3),X0) ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_1323,c_2735]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_2738,plain,
% 19.07/2.98      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k1_setfam_1(k2_enumset1(X2,X2,X2,X3))) = k7_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X3),X1),X0) ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_1323,c_1977]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_1914,plain,
% 19.07/2.98      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k1_setfam_1(k2_enumset1(X2,X2,X2,X3))) = k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X3),X1) ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_1323,c_1727]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_2745,plain,
% 19.07/2.98      ( k7_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),X3),X0) = k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),X3) ),
% 19.07/2.98      inference(light_normalisation,[status(thm)],[c_2738,c_1914]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_3875,plain,
% 19.07/2.98      ( k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),X3) = k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1),X3) ),
% 19.07/2.98      inference(light_normalisation,[status(thm)],[c_3864,c_1511,c_2745]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_14632,plain,
% 19.07/2.98      ( k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),X2) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1) ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_13007,c_3875]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_17354,plain,
% 19.07/2.98      ( k7_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X0),X1) = k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X0))),X0) ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_7317,c_14632]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_14,plain,
% 19.07/2.98      ( r1_tarski(k5_relat_1(X0,k6_relat_1(X1)),X0) | ~ v1_relat_1(X0) ),
% 19.07/2.98      inference(cnf_transformation,[],[f58]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_483,plain,
% 19.07/2.98      ( r1_tarski(k5_relat_1(X0,k6_relat_1(X1)),X0) = iProver_top
% 19.07/2.98      | v1_relat_1(X0) != iProver_top ),
% 19.07/2.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_948,plain,
% 19.07/2.98      ( r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X1)) = iProver_top
% 19.07/2.98      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_772,c_483]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_1113,plain,
% 19.07/2.98      ( r1_tarski(k6_relat_1(X0),k6_relat_1(X0)) = iProver_top
% 19.07/2.98      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_711,c_948]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_1172,plain,
% 19.07/2.98      ( r1_tarski(k6_relat_1(X0),k6_relat_1(X0)) = iProver_top ),
% 19.07/2.98      inference(global_propositional_subsumption,[status(thm)],[c_1113,c_61]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_10,plain,
% 19.07/2.98      ( ~ r1_tarski(X0,X1)
% 19.07/2.98      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 19.07/2.98      | ~ v1_relat_1(X1)
% 19.07/2.98      | ~ v1_relat_1(X0) ),
% 19.07/2.98      inference(cnf_transformation,[],[f54]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_485,plain,
% 19.07/2.98      ( r1_tarski(X0,X1) != iProver_top
% 19.07/2.98      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) = iProver_top
% 19.07/2.98      | v1_relat_1(X0) != iProver_top
% 19.07/2.98      | v1_relat_1(X1) != iProver_top ),
% 19.07/2.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_1843,plain,
% 19.07/2.98      ( r1_tarski(X0,k1_relat_1(X1)) = iProver_top
% 19.07/2.98      | r1_tarski(k6_relat_1(X0),X1) != iProver_top
% 19.07/2.98      | v1_relat_1(X1) != iProver_top
% 19.07/2.98      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_12,c_485]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_2428,plain,
% 19.07/2.98      ( v1_relat_1(X1) != iProver_top
% 19.07/2.98      | r1_tarski(k6_relat_1(X0),X1) != iProver_top
% 19.07/2.98      | r1_tarski(X0,k1_relat_1(X1)) = iProver_top ),
% 19.07/2.98      inference(global_propositional_subsumption,[status(thm)],[c_1843,c_61]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_2429,plain,
% 19.07/2.98      ( r1_tarski(X0,k1_relat_1(X1)) = iProver_top
% 19.07/2.98      | r1_tarski(k6_relat_1(X0),X1) != iProver_top
% 19.07/2.98      | v1_relat_1(X1) != iProver_top ),
% 19.07/2.98      inference(renaming,[status(thm)],[c_2428]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_2434,plain,
% 19.07/2.98      ( r1_tarski(X0,k1_relat_1(k6_relat_1(X0))) = iProver_top
% 19.07/2.98      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_1172,c_2429]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_2441,plain,
% 19.07/2.98      ( r1_tarski(X0,X0) = iProver_top
% 19.07/2.98      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 19.07/2.98      inference(light_normalisation,[status(thm)],[c_2434,c_12]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_2446,plain,
% 19.07/2.98      ( r1_tarski(X0,X0) = iProver_top ),
% 19.07/2.98      inference(global_propositional_subsumption,[status(thm)],[c_2441,c_61]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_2453,plain,
% 19.07/2.98      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X0 ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_2446,c_494]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_12774,plain,
% 19.07/2.98      ( k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),X2) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_2453,c_11691]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_14492,plain,
% 19.07/2.98      ( k7_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X0),X1) = k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X1) ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_1513,c_12774]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_14562,plain,
% 19.07/2.98      ( k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X1) = k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
% 19.07/2.98      inference(light_normalisation,[status(thm)],[c_14492,c_1513]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_14578,plain,
% 19.07/2.98      ( k7_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X0),X1) = k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X0) ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_1513,c_13007]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_14659,plain,
% 19.07/2.98      ( k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X0) = k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
% 19.07/2.98      inference(light_normalisation,[status(thm)],[c_14578,c_1513]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_17426,plain,
% 19.07/2.98      ( k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X1) = k6_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) ),
% 19.07/2.98      inference(light_normalisation,
% 19.07/2.98                [status(thm)],
% 19.07/2.98                [c_17354,c_1513,c_14562,c_14659]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_1694,plain,
% 19.07/2.98      ( k7_relat_1(k6_relat_1(X0),k5_relat_1(X0,k6_relat_1(X1))) = k6_relat_1(k5_relat_1(X0,k6_relat_1(X1)))
% 19.07/2.98      | v1_relat_1(X0) != iProver_top ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_483,c_1691]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_47204,plain,
% 19.07/2.98      ( k7_relat_1(k6_relat_1(k6_relat_1(X0)),k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k6_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_492,c_1694]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_47219,plain,
% 19.07/2.98      ( k7_relat_1(k6_relat_1(k6_relat_1(X0)),k7_relat_1(k6_relat_1(X1),X0)) = k6_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
% 19.07/2.98      inference(light_normalisation,[status(thm)],[c_47204,c_772]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_1023,plain,
% 19.07/2.98      ( k1_setfam_1(k2_enumset1(k5_relat_1(X0,k6_relat_1(X1)),k5_relat_1(X0,k6_relat_1(X1)),k5_relat_1(X0,k6_relat_1(X1)),X0)) = k5_relat_1(X0,k6_relat_1(X1))
% 19.07/2.98      | v1_relat_1(X0) != iProver_top ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_483,c_494]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_7823,plain,
% 19.07/2.98      ( k2_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,k5_relat_1(X0,k6_relat_1(X1)))))) = k5_relat_1(X0,k6_relat_1(X1))
% 19.07/2.98      | v1_relat_1(X0) != iProver_top ),
% 19.07/2.98      inference(demodulation,[status(thm)],[c_7647,c_1023]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_7824,plain,
% 19.07/2.98      ( k1_setfam_1(k2_enumset1(X0,X0,X0,k5_relat_1(X0,k6_relat_1(X1)))) = k5_relat_1(X0,k6_relat_1(X1))
% 19.07/2.98      | v1_relat_1(X0) != iProver_top ),
% 19.07/2.98      inference(demodulation,[status(thm)],[c_7823,c_11]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_8707,plain,
% 19.07/2.98      ( k1_setfam_1(k2_enumset1(k6_relat_1(X0),k6_relat_1(X0),k6_relat_1(X0),k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_492,c_7824]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_8710,plain,
% 19.07/2.98      ( k1_setfam_1(k2_enumset1(k6_relat_1(X0),k6_relat_1(X0),k6_relat_1(X0),k7_relat_1(k6_relat_1(X1),X0))) = k7_relat_1(k6_relat_1(X1),X0) ),
% 19.07/2.98      inference(light_normalisation,[status(thm)],[c_8707,c_772]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_9594,plain,
% 19.07/2.98      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X1),X2)),k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X1),X2)) ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_8710,c_1511]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_2454,plain,
% 19.07/2.98      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
% 19.07/2.98      | v1_relat_1(X0) != iProver_top ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_2446,c_482]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_9929,plain,
% 19.07/2.98      ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) = k7_relat_1(k6_relat_1(X0),X1) ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_9897,c_2454]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_6,plain,
% 19.07/2.98      ( ~ v1_relat_1(X0)
% 19.07/2.98      | ~ v1_relat_1(X1)
% 19.07/2.98      | k7_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(k7_relat_1(X0,X2),X1) ),
% 19.07/2.98      inference(cnf_transformation,[],[f51]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_489,plain,
% 19.07/2.98      ( k7_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(k7_relat_1(X0,X2),X1)
% 19.07/2.98      | v1_relat_1(X0) != iProver_top
% 19.07/2.98      | v1_relat_1(X1) != iProver_top ),
% 19.07/2.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_1181,plain,
% 19.07/2.98      ( k7_relat_1(k5_relat_1(k6_relat_1(X0),X1),X2) = k5_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1)
% 19.07/2.98      | v1_relat_1(X1) != iProver_top ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_492,c_489]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_7297,plain,
% 19.07/2.98      ( k7_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),X2) = k5_relat_1(k7_relat_1(k6_relat_1(X0),X2),k6_relat_1(X1)) ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_492,c_1181]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_7300,plain,
% 19.07/2.98      ( k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1) ),
% 19.07/2.98      inference(light_normalisation,[status(thm)],[c_7297,c_772]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_12249,plain,
% 19.07/2.98      ( k7_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0),X1) = k7_relat_1(k6_relat_1(X0),X1) ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_9929,c_7300]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_1531,plain,
% 19.07/2.98      ( r1_tarski(k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),X3),k6_relat_1(X0)) = iProver_top ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_1323,c_1514]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_12333,plain,
% 19.07/2.98      ( r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) = iProver_top ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_12249,c_1531]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_13959,plain,
% 19.07/2.98      ( r1_tarski(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),X2)))) = iProver_top ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_1727,c_12333]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_32012,plain,
% 19.07/2.98      ( r1_tarski(k7_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X1),X2)),k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X0),k6_relat_1(X2))))) = iProver_top ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_9594,c_13959]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_47585,plain,
% 19.07/2.98      ( r1_tarski(k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)),k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(k6_relat_1(X1)),k6_relat_1(X1))))) = iProver_top ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_47219,c_32012]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_47612,plain,
% 19.07/2.98      ( r1_tarski(k6_relat_1(k7_relat_1(k6_relat_1(X0),X1)),k6_relat_1(k6_relat_1(X1))) = iProver_top ),
% 19.07/2.98      inference(demodulation,[status(thm)],[c_47585,c_11,c_711]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_47847,plain,
% 19.07/2.98      ( r1_tarski(k6_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))),k6_relat_1(k6_relat_1(X0))) = iProver_top ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_17426,c_47612]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_48957,plain,
% 19.07/2.98      ( r1_tarski(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),k1_relat_1(k6_relat_1(k6_relat_1(X0)))) = iProver_top
% 19.07/2.98      | v1_relat_1(k6_relat_1(k6_relat_1(X0))) != iProver_top ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_47847,c_2429]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_48962,plain,
% 19.07/2.98      ( r1_tarski(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),k6_relat_1(X0)) = iProver_top
% 19.07/2.98      | v1_relat_1(k6_relat_1(k6_relat_1(X0))) != iProver_top ),
% 19.07/2.98      inference(demodulation,[status(thm)],[c_48957,c_12]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_23477,plain,
% 19.07/2.98      ( r1_tarski(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),k6_relat_1(X0)) = iProver_top
% 19.07/2.98      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_14659,c_948]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_49902,plain,
% 19.07/2.98      ( r1_tarski(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),k6_relat_1(X0)) = iProver_top ),
% 19.07/2.98      inference(global_propositional_subsumption,
% 19.07/2.98                [status(thm)],
% 19.07/2.98                [c_48962,c_61,c_23477]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_49951,plain,
% 19.07/2.98      ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),k1_relat_1(k6_relat_1(X0))) = iProver_top
% 19.07/2.98      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_49902,c_2429]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_49956,plain,
% 19.07/2.98      ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) = iProver_top
% 19.07/2.98      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 19.07/2.98      inference(light_normalisation,[status(thm)],[c_49951,c_12]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_53020,plain,
% 19.07/2.98      ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) = iProver_top ),
% 19.07/2.98      inference(global_propositional_subsumption,[status(thm)],[c_49956,c_61]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_53037,plain,
% 19.07/2.98      ( k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_53020,c_1691]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_9904,plain,
% 19.07/2.98      ( v1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) = iProver_top ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_1511,c_9897]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_10038,plain,
% 19.07/2.98      ( k5_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),k6_relat_1(X3)) = k8_relat_1(X3,k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_9904,c_488]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_7964,plain,
% 19.07/2.98      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k1_setfam_1(k2_enumset1(X2,X2,X2,X3))) = k5_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3),k6_relat_1(X0)) ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_1323,c_7300]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_7992,plain,
% 19.07/2.98      ( k5_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2),k6_relat_1(X3)) = k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X3),X1),X2),X0) ),
% 19.07/2.98      inference(light_normalisation,[status(thm)],[c_7964,c_1914]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_10041,plain,
% 19.07/2.98      ( k8_relat_1(X0,k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X3)) = k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X3),X1) ),
% 19.07/2.98      inference(light_normalisation,[status(thm)],[c_10038,c_7992]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_17687,plain,
% 19.07/2.98      ( k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X1),X2) = k8_relat_1(X0,k7_relat_1(k6_relat_1(X2),X1)) ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_1380,c_10041]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_17769,plain,
% 19.07/2.98      ( k8_relat_1(X0,k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1) ),
% 19.07/2.98      inference(light_normalisation,[status(thm)],[c_17687,c_1380]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_23082,plain,
% 19.07/2.98      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k1_setfam_1(k2_enumset1(X2,X2,X2,X1))) = k8_relat_1(X0,k6_relat_1(k1_setfam_1(k2_enumset1(X2,X2,X2,X1)))) ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_14562,c_17769]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_7633,plain,
% 19.07/2.98      ( k7_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X1),X0),X1),X0) = k6_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_7317,c_1513]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_7634,plain,
% 19.07/2.98      ( k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k6_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) ),
% 19.07/2.98      inference(light_normalisation,[status(thm)],[c_7633,c_1719]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_8300,plain,
% 19.07/2.98      ( k8_relat_1(X0,k6_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))) = k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X2,X2,X2,X1))) ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_7634,c_897]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_8307,plain,
% 19.07/2.98      ( k8_relat_1(X0,k6_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) ),
% 19.07/2.98      inference(demodulation,[status(thm)],[c_8300,c_897,c_1511]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_8416,plain,
% 19.07/2.98      ( k8_relat_1(X0,k6_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1) ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_1,c_8307]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_23151,plain,
% 19.07/2.98      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k1_setfam_1(k2_enumset1(X2,X2,X2,X1))) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) ),
% 19.07/2.98      inference(demodulation,[status(thm)],[c_23082,c_8416,c_11691]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_35734,plain,
% 19.07/2.98      ( k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X0),X1) ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_711,c_23151]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_35959,plain,
% 19.07/2.98      ( k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) = k7_relat_1(k6_relat_1(X0),X1) ),
% 19.07/2.98      inference(light_normalisation,[status(thm)],[c_35734,c_711]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_36017,plain,
% 19.07/2.98      ( k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_1,c_35959]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_53040,plain,
% 19.07/2.98      ( k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
% 19.07/2.98      inference(light_normalisation,[status(thm)],[c_53037,c_36017]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_58963,plain,
% 19.07/2.98      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_53040,c_711]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_36673,plain,
% 19.07/2.98      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_36017,c_1380]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_36691,plain,
% 19.07/2.98      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k1_setfam_1(k2_enumset1(X0,X0,X0,X2))) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X2),X1) ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_36017,c_1727]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_36849,plain,
% 19.07/2.98      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
% 19.07/2.98      inference(demodulation,[status(thm)],[c_36673,c_36017,c_36691]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_53033,plain,
% 19.07/2.98      ( r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X1) = iProver_top ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_1,c_53020]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_53304,plain,
% 19.07/2.98      ( k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) = k6_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) ),
% 19.07/2.98      inference(superposition,[status(thm)],[c_53033,c_1691]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_53307,plain,
% 19.07/2.98      ( k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k7_relat_1(k6_relat_1(X1),X0) ),
% 19.07/2.98      inference(light_normalisation,[status(thm)],[c_53304,c_35959]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_59167,plain,
% 19.07/2.98      ( k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X1),X0) ),
% 19.07/2.98      inference(light_normalisation,[status(thm)],[c_58963,c_36849,c_53307]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_19,negated_conjecture,
% 19.07/2.98      ( k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) ),
% 19.07/2.98      inference(cnf_transformation,[],[f71]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_665,plain,
% 19.07/2.98      ( k6_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK0))) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
% 19.07/2.98      inference(demodulation,[status(thm)],[c_1,c_19]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_947,plain,
% 19.07/2.98      ( k6_relat_1(k1_setfam_1(k2_enumset1(sK1,sK1,sK1,sK0))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
% 19.07/2.98      inference(demodulation,[status(thm)],[c_772,c_665]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_58565,plain,
% 19.07/2.98      ( k7_relat_1(k6_relat_1(sK1),sK0) != k7_relat_1(k6_relat_1(sK0),sK1) ),
% 19.07/2.98      inference(demodulation,[status(thm)],[c_53040,c_947]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_59168,plain,
% 19.07/2.98      ( k7_relat_1(k6_relat_1(sK1),sK0) != k7_relat_1(k6_relat_1(sK1),sK0) ),
% 19.07/2.98      inference(demodulation,[status(thm)],[c_59167,c_58565]) ).
% 19.07/2.98  
% 19.07/2.98  cnf(c_59169,plain,
% 19.07/2.98      ( $false ),
% 19.07/2.98      inference(equality_resolution_simp,[status(thm)],[c_59168]) ).
% 19.07/2.98  
% 19.07/2.98  
% 19.07/2.98  % SZS output end CNFRefutation for theBenchmark.p
% 19.07/2.98  
% 19.07/2.98  ------                               Statistics
% 19.07/2.98  
% 19.07/2.98  ------ General
% 19.07/2.98  
% 19.07/2.98  abstr_ref_over_cycles:                  0
% 19.07/2.98  abstr_ref_under_cycles:                 0
% 19.07/2.98  gc_basic_clause_elim:                   0
% 19.07/2.98  forced_gc_time:                         0
% 19.07/2.98  parsing_time:                           0.021
% 19.07/2.98  unif_index_cands_time:                  0.
% 19.07/2.98  unif_index_add_time:                    0.
% 19.07/2.98  orderings_time:                         0.
% 19.07/2.98  out_proof_time:                         0.018
% 19.07/2.98  total_time:                             2.015
% 19.07/2.98  num_of_symbols:                         43
% 19.07/2.98  num_of_terms:                           81018
% 19.07/2.98  
% 19.07/2.98  ------ Preprocessing
% 19.07/2.98  
% 19.07/2.98  num_of_splits:                          0
% 19.07/2.98  num_of_split_atoms:                     0
% 19.07/2.98  num_of_reused_defs:                     0
% 19.07/2.98  num_eq_ax_congr_red:                    2
% 19.07/2.98  num_of_sem_filtered_clauses:            1
% 19.07/2.98  num_of_subtypes:                        0
% 19.07/2.98  monotx_restored_types:                  0
% 19.07/2.98  sat_num_of_epr_types:                   0
% 19.07/2.98  sat_num_of_non_cyclic_types:            0
% 19.07/2.98  sat_guarded_non_collapsed_types:        0
% 19.07/2.98  num_pure_diseq_elim:                    0
% 19.07/2.98  simp_replaced_by:                       0
% 19.07/2.98  res_preprocessed:                       85
% 19.07/2.98  prep_upred:                             0
% 19.07/2.98  prep_unflattend:                        0
% 19.07/2.98  smt_new_axioms:                         0
% 19.07/2.98  pred_elim_cands:                        2
% 19.07/2.98  pred_elim:                              0
% 19.07/2.98  pred_elim_cl:                           0
% 19.07/2.98  pred_elim_cycles:                       1
% 19.07/2.98  merged_defs:                            0
% 19.07/2.98  merged_defs_ncl:                        0
% 19.07/2.98  bin_hyper_res:                          0
% 19.07/2.98  prep_cycles:                            3
% 19.07/2.98  pred_elim_time:                         0.
% 19.07/2.98  splitting_time:                         0.
% 19.07/2.98  sem_filter_time:                        0.
% 19.07/2.98  monotx_time:                            0.001
% 19.07/2.98  subtype_inf_time:                       0.
% 19.07/2.98  
% 19.07/2.98  ------ Problem properties
% 19.07/2.98  
% 19.07/2.98  clauses:                                20
% 19.07/2.98  conjectures:                            1
% 19.07/2.98  epr:                                    0
% 19.07/2.98  horn:                                   20
% 19.07/2.98  ground:                                 1
% 19.07/2.98  unary:                                  5
% 19.07/2.98  binary:                                 9
% 19.07/2.98  lits:                                   43
% 19.07/2.98  lits_eq:                                13
% 19.07/2.98  fd_pure:                                0
% 19.07/2.98  fd_pseudo:                              0
% 19.07/2.98  fd_cond:                                0
% 19.07/2.98  fd_pseudo_cond:                         0
% 19.07/2.98  ac_symbols:                             0
% 19.07/2.98  
% 19.07/2.98  ------ Propositional Solver
% 19.07/2.98  
% 19.07/2.98  prop_solver_calls:                      28
% 19.07/2.98  prop_fast_solver_calls:                 793
% 19.07/2.98  smt_solver_calls:                       0
% 19.07/2.98  smt_fast_solver_calls:                  0
% 19.07/2.98  prop_num_of_clauses:                    18121
% 19.07/2.98  prop_preprocess_simplified:             19047
% 19.07/2.98  prop_fo_subsumed:                       10
% 19.07/2.98  prop_solver_time:                       0.
% 19.07/2.98  smt_solver_time:                        0.
% 19.07/2.98  smt_fast_solver_time:                   0.
% 19.07/2.98  prop_fast_solver_time:                  0.
% 19.07/2.98  prop_unsat_core_time:                   0.
% 19.07/2.98  
% 19.07/2.98  ------ QBF
% 19.07/2.98  
% 19.07/2.98  qbf_q_res:                              0
% 19.07/2.98  qbf_num_tautologies:                    0
% 19.07/2.98  qbf_prep_cycles:                        0
% 19.07/2.98  
% 19.07/2.98  ------ BMC1
% 19.07/2.98  
% 19.07/2.98  bmc1_current_bound:                     -1
% 19.07/2.98  bmc1_last_solved_bound:                 -1
% 19.07/2.98  bmc1_unsat_core_size:                   -1
% 19.07/2.98  bmc1_unsat_core_parents_size:           -1
% 19.07/2.98  bmc1_merge_next_fun:                    0
% 19.07/2.98  bmc1_unsat_core_clauses_time:           0.
% 19.07/2.98  
% 19.07/2.98  ------ Instantiation
% 19.07/2.98  
% 19.07/2.98  inst_num_of_clauses:                    5236
% 19.07/2.98  inst_num_in_passive:                    1338
% 19.07/2.98  inst_num_in_active:                     1418
% 19.07/2.98  inst_num_in_unprocessed:                2482
% 19.07/2.98  inst_num_of_loops:                      1510
% 19.07/2.98  inst_num_of_learning_restarts:          0
% 19.07/2.98  inst_num_moves_active_passive:          90
% 19.07/2.98  inst_lit_activity:                      0
% 19.07/2.98  inst_lit_activity_moves:                0
% 19.07/2.98  inst_num_tautologies:                   0
% 19.07/2.98  inst_num_prop_implied:                  0
% 19.07/2.98  inst_num_existing_simplified:           0
% 19.07/2.98  inst_num_eq_res_simplified:             0
% 19.07/2.98  inst_num_child_elim:                    0
% 19.07/2.98  inst_num_of_dismatching_blockings:      1013
% 19.07/2.98  inst_num_of_non_proper_insts:           4837
% 19.07/2.98  inst_num_of_duplicates:                 0
% 19.07/2.98  inst_inst_num_from_inst_to_res:         0
% 19.07/2.98  inst_dismatching_checking_time:         0.
% 19.07/2.98  
% 19.07/2.98  ------ Resolution
% 19.07/2.98  
% 19.07/2.98  res_num_of_clauses:                     0
% 19.07/2.98  res_num_in_passive:                     0
% 19.07/2.98  res_num_in_active:                      0
% 19.07/2.98  res_num_of_loops:                       88
% 19.07/2.98  res_forward_subset_subsumed:            974
% 19.07/2.98  res_backward_subset_subsumed:           10
% 19.07/2.98  res_forward_subsumed:                   0
% 19.07/2.98  res_backward_subsumed:                  0
% 19.07/2.98  res_forward_subsumption_resolution:     0
% 19.07/2.98  res_backward_subsumption_resolution:    0
% 19.07/2.98  res_clause_to_clause_subsumption:       34902
% 19.07/2.98  res_orphan_elimination:                 0
% 19.07/2.98  res_tautology_del:                      432
% 19.07/2.98  res_num_eq_res_simplified:              0
% 19.07/2.98  res_num_sel_changes:                    0
% 19.07/2.98  res_moves_from_active_to_pass:          0
% 19.07/2.98  
% 19.07/2.98  ------ Superposition
% 19.07/2.98  
% 19.07/2.98  sup_time_total:                         0.
% 19.07/2.98  sup_time_generating:                    0.
% 19.07/2.98  sup_time_sim_full:                      0.
% 19.07/2.98  sup_time_sim_immed:                     0.
% 19.07/2.98  
% 19.07/2.98  sup_num_of_clauses:                     4087
% 19.07/2.98  sup_num_in_active:                      233
% 19.07/2.98  sup_num_in_passive:                     3854
% 19.07/2.98  sup_num_of_loops:                       301
% 19.07/2.98  sup_fw_superposition:                   14630
% 19.07/2.98  sup_bw_superposition:                   12829
% 19.07/2.98  sup_immediate_simplified:               10184
% 19.07/2.98  sup_given_eliminated:                   2
% 19.07/2.98  comparisons_done:                       0
% 19.07/2.98  comparisons_avoided:                    0
% 19.07/2.98  
% 19.07/2.98  ------ Simplifications
% 19.07/2.98  
% 19.07/2.98  
% 19.07/2.98  sim_fw_subset_subsumed:                 62
% 19.07/2.98  sim_bw_subset_subsumed:                 70
% 19.07/2.98  sim_fw_subsumed:                        2957
% 19.07/2.98  sim_bw_subsumed:                        46
% 19.07/2.98  sim_fw_subsumption_res:                 0
% 19.07/2.98  sim_bw_subsumption_res:                 0
% 19.07/2.98  sim_tautology_del:                      8
% 19.07/2.98  sim_eq_tautology_del:                   1142
% 19.07/2.98  sim_eq_res_simp:                        0
% 19.07/2.98  sim_fw_demodulated:                     5677
% 19.07/2.98  sim_bw_demodulated:                     75
% 19.07/2.98  sim_light_normalised:                   3616
% 19.07/2.98  sim_joinable_taut:                      0
% 19.07/2.98  sim_joinable_simp:                      0
% 19.07/2.98  sim_ac_normalised:                      0
% 19.07/2.98  sim_smt_subsumption:                    0
% 19.07/2.98  
%------------------------------------------------------------------------------
