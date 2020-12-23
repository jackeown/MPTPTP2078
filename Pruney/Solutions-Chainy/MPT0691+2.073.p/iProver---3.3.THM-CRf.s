%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:51:51 EST 2020

% Result     : Theorem 3.01s
% Output     : CNFRefutation 3.01s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 235 expanded)
%              Number of clauses        :   65 (  90 expanded)
%              Number of leaves         :   18 (  46 expanded)
%              Depth                    :   14
%              Number of atoms          :  223 ( 544 expanded)
%              Number of equality atoms :  117 ( 139 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f30,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f31,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f32,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f32])).

fof(f50,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f14,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f49,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f10,axiom,(
    ! [X0] : k4_relat_1(k6_relat_1(X0)) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k4_relat_1(k6_relat_1(X0)) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f41,plain,(
    ! [X0] :
      ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f9,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f51,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f33])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k3_xboole_0(k1_relat_1(X1),X0),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_xboole_0(k1_relat_1(X1),X0),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_xboole_0(k1_relat_1(X1),X0),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f52,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_18,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_554,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k4_relat_1(X0)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_569,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_566,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1126,plain,
    ( k2_relat_1(k7_relat_1(k4_relat_1(X0),X1)) = k9_relat_1(k4_relat_1(X0),X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_569,c_566])).

cnf(c_6177,plain,
    ( k2_relat_1(k7_relat_1(k4_relat_1(sK1),X0)) = k9_relat_1(k4_relat_1(sK1),X0) ),
    inference(superposition,[status(thm)],[c_554,c_1126])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_558,plain,
    ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_882,plain,
    ( k5_relat_1(k6_relat_1(X0),k4_relat_1(X1)) = k7_relat_1(k4_relat_1(X1),X0)
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_569,c_558])).

cnf(c_4504,plain,
    ( k5_relat_1(k6_relat_1(X0),k4_relat_1(sK1)) = k7_relat_1(k4_relat_1(sK1),X0) ),
    inference(superposition,[status(thm)],[c_554,c_882])).

cnf(c_15,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_557,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_561,plain,
    ( k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,X0))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3096,plain,
    ( k5_relat_1(k4_relat_1(k6_relat_1(X0)),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,k6_relat_1(X0)))
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_557,c_561])).

cnf(c_11,plain,
    ( k4_relat_1(k6_relat_1(X0)) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_3104,plain,
    ( k5_relat_1(k6_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,k6_relat_1(X0)))
    | v1_relat_1(X1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3096,c_11])).

cnf(c_3135,plain,
    ( k5_relat_1(k6_relat_1(X0),k4_relat_1(sK1)) = k4_relat_1(k5_relat_1(sK1,k6_relat_1(X0))) ),
    inference(superposition,[status(thm)],[c_554,c_3104])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_567,plain,
    ( k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1546,plain,
    ( k5_relat_1(sK1,k6_relat_1(X0)) = k8_relat_1(X0,sK1) ),
    inference(superposition,[status(thm)],[c_554,c_567])).

cnf(c_3137,plain,
    ( k5_relat_1(k6_relat_1(X0),k4_relat_1(sK1)) = k4_relat_1(k8_relat_1(X0,sK1)) ),
    inference(light_normalisation,[status(thm)],[c_3135,c_1546])).

cnf(c_4506,plain,
    ( k7_relat_1(k4_relat_1(sK1),X0) = k4_relat_1(k8_relat_1(X0,sK1)) ),
    inference(light_normalisation,[status(thm)],[c_4504,c_3137])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k8_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_568,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k8_relat_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_563,plain,
    ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1002,plain,
    ( k2_relat_1(k4_relat_1(k8_relat_1(X0,X1))) = k1_relat_1(k8_relat_1(X0,X1))
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_568,c_563])).

cnf(c_4776,plain,
    ( k2_relat_1(k4_relat_1(k8_relat_1(X0,sK1))) = k1_relat_1(k8_relat_1(X0,sK1)) ),
    inference(superposition,[status(thm)],[c_554,c_1002])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_564,plain,
    ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3367,plain,
    ( k10_relat_1(sK1,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(sK1,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_554,c_564])).

cnf(c_3764,plain,
    ( k10_relat_1(sK1,k1_relat_1(k6_relat_1(X0))) = k1_relat_1(k5_relat_1(sK1,k6_relat_1(X0))) ),
    inference(superposition,[status(thm)],[c_557,c_3367])).

cnf(c_10,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_3769,plain,
    ( k1_relat_1(k8_relat_1(X0,sK1)) = k10_relat_1(sK1,X0) ),
    inference(light_normalisation,[status(thm)],[c_3764,c_10,c_1546])).

cnf(c_4778,plain,
    ( k2_relat_1(k4_relat_1(k8_relat_1(X0,sK1))) = k10_relat_1(sK1,X0) ),
    inference(light_normalisation,[status(thm)],[c_4776,c_3769])).

cnf(c_6179,plain,
    ( k9_relat_1(k4_relat_1(sK1),X0) = k10_relat_1(sK1,X0) ),
    inference(light_normalisation,[status(thm)],[c_6177,c_4506,c_4778])).

cnf(c_17,negated_conjecture,
    ( r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_555,plain,
    ( r1_tarski(sK0,k1_relat_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_559,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1764,plain,
    ( k1_relat_1(k7_relat_1(sK1,sK0)) = sK0
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_555,c_559])).

cnf(c_229,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_relat_1(sK1)
    | k1_relat_1(k7_relat_1(X0,X1)) = X1
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_17])).

cnf(c_230,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_relat_1(sK1)
    | k1_relat_1(k7_relat_1(X0,sK0)) = sK0 ),
    inference(unflattening,[status(thm)],[c_229])).

cnf(c_232,plain,
    ( ~ v1_relat_1(sK1)
    | k1_relat_1(k7_relat_1(sK1,sK0)) = sK0
    | k1_relat_1(sK1) != k1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_230])).

cnf(c_271,plain,
    ( X0 != X1
    | k1_relat_1(X0) = k1_relat_1(X1) ),
    theory(equality)).

cnf(c_280,plain,
    ( k1_relat_1(sK1) = k1_relat_1(sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_271])).

cnf(c_264,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_285,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_264])).

cnf(c_2378,plain,
    ( k1_relat_1(k7_relat_1(sK1,sK0)) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1764,c_18,c_232,c_280,c_285])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | k3_xboole_0(k1_relat_1(X0),X1) = k1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_560,plain,
    ( k3_xboole_0(k1_relat_1(X0),X1) = k1_relat_1(k7_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1904,plain,
    ( k3_xboole_0(k1_relat_1(sK1),X0) = k1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_554,c_560])).

cnf(c_4,plain,
    ( r1_tarski(k3_xboole_0(k1_relat_1(X0),X1),k9_relat_1(k4_relat_1(X0),k9_relat_1(X0,X1)))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_565,plain,
    ( r1_tarski(k3_xboole_0(k1_relat_1(X0),X1),k9_relat_1(k4_relat_1(X0),k9_relat_1(X0,X1))) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2363,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,X0))) = iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1904,c_565])).

cnf(c_19,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2782,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2363,c_19])).

cnf(c_2789,plain,
    ( r1_tarski(sK0,k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2378,c_2782])).

cnf(c_6201,plain,
    ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6179,c_2789])).

cnf(c_16,negated_conjecture,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_21,plain,
    ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6201,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:34:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.01/0.94  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.01/0.94  
% 3.01/0.94  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.01/0.94  
% 3.01/0.94  ------  iProver source info
% 3.01/0.94  
% 3.01/0.94  git: date: 2020-06-30 10:37:57 +0100
% 3.01/0.94  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.01/0.94  git: non_committed_changes: false
% 3.01/0.94  git: last_make_outside_of_git: false
% 3.01/0.94  
% 3.01/0.94  ------ 
% 3.01/0.94  
% 3.01/0.94  ------ Input Options
% 3.01/0.94  
% 3.01/0.94  --out_options                           all
% 3.01/0.94  --tptp_safe_out                         true
% 3.01/0.94  --problem_path                          ""
% 3.01/0.94  --include_path                          ""
% 3.01/0.94  --clausifier                            res/vclausify_rel
% 3.01/0.94  --clausifier_options                    --mode clausify
% 3.01/0.94  --stdin                                 false
% 3.01/0.94  --stats_out                             all
% 3.01/0.94  
% 3.01/0.94  ------ General Options
% 3.01/0.94  
% 3.01/0.94  --fof                                   false
% 3.01/0.94  --time_out_real                         305.
% 3.01/0.94  --time_out_virtual                      -1.
% 3.01/0.94  --symbol_type_check                     false
% 3.01/0.94  --clausify_out                          false
% 3.01/0.94  --sig_cnt_out                           false
% 3.01/0.94  --trig_cnt_out                          false
% 3.01/0.94  --trig_cnt_out_tolerance                1.
% 3.01/0.94  --trig_cnt_out_sk_spl                   false
% 3.01/0.94  --abstr_cl_out                          false
% 3.01/0.94  
% 3.01/0.94  ------ Global Options
% 3.01/0.94  
% 3.01/0.94  --schedule                              default
% 3.01/0.94  --add_important_lit                     false
% 3.01/0.94  --prop_solver_per_cl                    1000
% 3.01/0.94  --min_unsat_core                        false
% 3.01/0.94  --soft_assumptions                      false
% 3.01/0.94  --soft_lemma_size                       3
% 3.01/0.94  --prop_impl_unit_size                   0
% 3.01/0.94  --prop_impl_unit                        []
% 3.01/0.94  --share_sel_clauses                     true
% 3.01/0.94  --reset_solvers                         false
% 3.01/0.94  --bc_imp_inh                            [conj_cone]
% 3.01/0.94  --conj_cone_tolerance                   3.
% 3.01/0.94  --extra_neg_conj                        none
% 3.01/0.94  --large_theory_mode                     true
% 3.01/0.94  --prolific_symb_bound                   200
% 3.01/0.94  --lt_threshold                          2000
% 3.01/0.94  --clause_weak_htbl                      true
% 3.01/0.94  --gc_record_bc_elim                     false
% 3.01/0.94  
% 3.01/0.94  ------ Preprocessing Options
% 3.01/0.94  
% 3.01/0.94  --preprocessing_flag                    true
% 3.01/0.94  --time_out_prep_mult                    0.1
% 3.01/0.94  --splitting_mode                        input
% 3.01/0.94  --splitting_grd                         true
% 3.01/0.94  --splitting_cvd                         false
% 3.01/0.94  --splitting_cvd_svl                     false
% 3.01/0.94  --splitting_nvd                         32
% 3.01/0.94  --sub_typing                            true
% 3.01/0.94  --prep_gs_sim                           true
% 3.01/0.94  --prep_unflatten                        true
% 3.01/0.94  --prep_res_sim                          true
% 3.01/0.94  --prep_upred                            true
% 3.01/0.94  --prep_sem_filter                       exhaustive
% 3.01/0.94  --prep_sem_filter_out                   false
% 3.01/0.94  --pred_elim                             true
% 3.01/0.94  --res_sim_input                         true
% 3.01/0.94  --eq_ax_congr_red                       true
% 3.01/0.94  --pure_diseq_elim                       true
% 3.01/0.94  --brand_transform                       false
% 3.01/0.94  --non_eq_to_eq                          false
% 3.01/0.94  --prep_def_merge                        true
% 3.01/0.94  --prep_def_merge_prop_impl              false
% 3.01/0.94  --prep_def_merge_mbd                    true
% 3.01/0.94  --prep_def_merge_tr_red                 false
% 3.01/0.94  --prep_def_merge_tr_cl                  false
% 3.01/0.94  --smt_preprocessing                     true
% 3.01/0.94  --smt_ac_axioms                         fast
% 3.01/0.94  --preprocessed_out                      false
% 3.01/0.94  --preprocessed_stats                    false
% 3.01/0.94  
% 3.01/0.94  ------ Abstraction refinement Options
% 3.01/0.94  
% 3.01/0.94  --abstr_ref                             []
% 3.01/0.94  --abstr_ref_prep                        false
% 3.01/0.94  --abstr_ref_until_sat                   false
% 3.01/0.94  --abstr_ref_sig_restrict                funpre
% 3.01/0.94  --abstr_ref_af_restrict_to_split_sk     false
% 3.01/0.94  --abstr_ref_under                       []
% 3.01/0.94  
% 3.01/0.94  ------ SAT Options
% 3.01/0.94  
% 3.01/0.94  --sat_mode                              false
% 3.01/0.94  --sat_fm_restart_options                ""
% 3.01/0.94  --sat_gr_def                            false
% 3.01/0.94  --sat_epr_types                         true
% 3.01/0.94  --sat_non_cyclic_types                  false
% 3.01/0.94  --sat_finite_models                     false
% 3.01/0.94  --sat_fm_lemmas                         false
% 3.01/0.94  --sat_fm_prep                           false
% 3.01/0.94  --sat_fm_uc_incr                        true
% 3.01/0.94  --sat_out_model                         small
% 3.01/0.94  --sat_out_clauses                       false
% 3.01/0.94  
% 3.01/0.94  ------ QBF Options
% 3.01/0.94  
% 3.01/0.94  --qbf_mode                              false
% 3.01/0.94  --qbf_elim_univ                         false
% 3.01/0.94  --qbf_dom_inst                          none
% 3.01/0.94  --qbf_dom_pre_inst                      false
% 3.01/0.94  --qbf_sk_in                             false
% 3.01/0.94  --qbf_pred_elim                         true
% 3.01/0.94  --qbf_split                             512
% 3.01/0.94  
% 3.01/0.94  ------ BMC1 Options
% 3.01/0.94  
% 3.01/0.94  --bmc1_incremental                      false
% 3.01/0.94  --bmc1_axioms                           reachable_all
% 3.01/0.94  --bmc1_min_bound                        0
% 3.01/0.94  --bmc1_max_bound                        -1
% 3.01/0.94  --bmc1_max_bound_default                -1
% 3.01/0.94  --bmc1_symbol_reachability              true
% 3.01/0.94  --bmc1_property_lemmas                  false
% 3.01/0.94  --bmc1_k_induction                      false
% 3.01/0.94  --bmc1_non_equiv_states                 false
% 3.01/0.94  --bmc1_deadlock                         false
% 3.01/0.94  --bmc1_ucm                              false
% 3.01/0.94  --bmc1_add_unsat_core                   none
% 3.01/0.94  --bmc1_unsat_core_children              false
% 3.01/0.94  --bmc1_unsat_core_extrapolate_axioms    false
% 3.01/0.94  --bmc1_out_stat                         full
% 3.01/0.94  --bmc1_ground_init                      false
% 3.01/0.94  --bmc1_pre_inst_next_state              false
% 3.01/0.94  --bmc1_pre_inst_state                   false
% 3.01/0.94  --bmc1_pre_inst_reach_state             false
% 3.01/0.94  --bmc1_out_unsat_core                   false
% 3.01/0.94  --bmc1_aig_witness_out                  false
% 3.01/0.94  --bmc1_verbose                          false
% 3.01/0.94  --bmc1_dump_clauses_tptp                false
% 3.01/0.94  --bmc1_dump_unsat_core_tptp             false
% 3.01/0.94  --bmc1_dump_file                        -
% 3.01/0.94  --bmc1_ucm_expand_uc_limit              128
% 3.01/0.94  --bmc1_ucm_n_expand_iterations          6
% 3.01/0.94  --bmc1_ucm_extend_mode                  1
% 3.01/0.94  --bmc1_ucm_init_mode                    2
% 3.01/0.94  --bmc1_ucm_cone_mode                    none
% 3.01/0.94  --bmc1_ucm_reduced_relation_type        0
% 3.01/0.94  --bmc1_ucm_relax_model                  4
% 3.01/0.94  --bmc1_ucm_full_tr_after_sat            true
% 3.01/0.94  --bmc1_ucm_expand_neg_assumptions       false
% 3.01/0.94  --bmc1_ucm_layered_model                none
% 3.01/0.94  --bmc1_ucm_max_lemma_size               10
% 3.01/0.94  
% 3.01/0.94  ------ AIG Options
% 3.01/0.94  
% 3.01/0.94  --aig_mode                              false
% 3.01/0.94  
% 3.01/0.94  ------ Instantiation Options
% 3.01/0.94  
% 3.01/0.94  --instantiation_flag                    true
% 3.01/0.94  --inst_sos_flag                         false
% 3.01/0.94  --inst_sos_phase                        true
% 3.01/0.94  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.01/0.94  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.01/0.94  --inst_lit_sel_side                     num_symb
% 3.01/0.94  --inst_solver_per_active                1400
% 3.01/0.94  --inst_solver_calls_frac                1.
% 3.01/0.94  --inst_passive_queue_type               priority_queues
% 3.01/0.94  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.01/0.94  --inst_passive_queues_freq              [25;2]
% 3.01/0.94  --inst_dismatching                      true
% 3.01/0.94  --inst_eager_unprocessed_to_passive     true
% 3.01/0.94  --inst_prop_sim_given                   true
% 3.01/0.94  --inst_prop_sim_new                     false
% 3.01/0.94  --inst_subs_new                         false
% 3.01/0.94  --inst_eq_res_simp                      false
% 3.01/0.94  --inst_subs_given                       false
% 3.01/0.94  --inst_orphan_elimination               true
% 3.01/0.94  --inst_learning_loop_flag               true
% 3.01/0.94  --inst_learning_start                   3000
% 3.01/0.94  --inst_learning_factor                  2
% 3.01/0.94  --inst_start_prop_sim_after_learn       3
% 3.01/0.94  --inst_sel_renew                        solver
% 3.01/0.94  --inst_lit_activity_flag                true
% 3.01/0.94  --inst_restr_to_given                   false
% 3.01/0.94  --inst_activity_threshold               500
% 3.01/0.94  --inst_out_proof                        true
% 3.01/0.94  
% 3.01/0.94  ------ Resolution Options
% 3.01/0.94  
% 3.01/0.94  --resolution_flag                       true
% 3.01/0.94  --res_lit_sel                           adaptive
% 3.01/0.94  --res_lit_sel_side                      none
% 3.01/0.94  --res_ordering                          kbo
% 3.01/0.94  --res_to_prop_solver                    active
% 3.01/0.94  --res_prop_simpl_new                    false
% 3.01/0.94  --res_prop_simpl_given                  true
% 3.01/0.94  --res_passive_queue_type                priority_queues
% 3.01/0.94  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.01/0.94  --res_passive_queues_freq               [15;5]
% 3.01/0.94  --res_forward_subs                      full
% 3.01/0.94  --res_backward_subs                     full
% 3.01/0.94  --res_forward_subs_resolution           true
% 3.01/0.94  --res_backward_subs_resolution          true
% 3.01/0.94  --res_orphan_elimination                true
% 3.01/0.94  --res_time_limit                        2.
% 3.01/0.94  --res_out_proof                         true
% 3.01/0.94  
% 3.01/0.94  ------ Superposition Options
% 3.01/0.94  
% 3.01/0.94  --superposition_flag                    true
% 3.01/0.94  --sup_passive_queue_type                priority_queues
% 3.01/0.94  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.01/0.94  --sup_passive_queues_freq               [8;1;4]
% 3.01/0.94  --demod_completeness_check              fast
% 3.01/0.94  --demod_use_ground                      true
% 3.01/0.94  --sup_to_prop_solver                    passive
% 3.01/0.94  --sup_prop_simpl_new                    true
% 3.01/0.94  --sup_prop_simpl_given                  true
% 3.01/0.94  --sup_fun_splitting                     false
% 3.01/0.94  --sup_smt_interval                      50000
% 3.01/0.94  
% 3.01/0.94  ------ Superposition Simplification Setup
% 3.01/0.94  
% 3.01/0.94  --sup_indices_passive                   []
% 3.01/0.94  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/0.94  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/0.94  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/0.94  --sup_full_triv                         [TrivRules;PropSubs]
% 3.01/0.94  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/0.94  --sup_full_bw                           [BwDemod]
% 3.01/0.94  --sup_immed_triv                        [TrivRules]
% 3.01/0.94  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.01/0.94  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/0.94  --sup_immed_bw_main                     []
% 3.01/0.94  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.01/0.94  --sup_input_triv                        [Unflattening;TrivRules]
% 3.01/0.94  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/0.94  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.01/0.94  
% 3.01/0.94  ------ Combination Options
% 3.01/0.94  
% 3.01/0.94  --comb_res_mult                         3
% 3.01/0.94  --comb_sup_mult                         2
% 3.01/0.94  --comb_inst_mult                        10
% 3.01/0.94  
% 3.01/0.94  ------ Debug Options
% 3.01/0.94  
% 3.01/0.94  --dbg_backtrace                         false
% 3.01/0.94  --dbg_dump_prop_clauses                 false
% 3.01/0.94  --dbg_dump_prop_clauses_file            -
% 3.01/0.94  --dbg_out_stat                          false
% 3.01/0.94  ------ Parsing...
% 3.01/0.94  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.01/0.94  
% 3.01/0.94  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.01/0.94  
% 3.01/0.94  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.01/0.94  
% 3.01/0.94  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.01/0.94  ------ Proving...
% 3.01/0.94  ------ Problem Properties 
% 3.01/0.94  
% 3.01/0.94  
% 3.01/0.94  clauses                                 19
% 3.01/0.94  conjectures                             3
% 3.01/0.94  EPR                                     1
% 3.01/0.94  Horn                                    19
% 3.01/0.94  unary                                   7
% 3.01/0.94  binary                                  9
% 3.01/0.94  lits                                    34
% 3.01/0.94  lits eq                                 12
% 3.01/0.94  fd_pure                                 0
% 3.01/0.94  fd_pseudo                               0
% 3.01/0.94  fd_cond                                 0
% 3.01/0.94  fd_pseudo_cond                          0
% 3.01/0.94  AC symbols                              0
% 3.01/0.94  
% 3.01/0.94  ------ Schedule dynamic 5 is on 
% 3.01/0.94  
% 3.01/0.94  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.01/0.94  
% 3.01/0.94  
% 3.01/0.94  ------ 
% 3.01/0.94  Current options:
% 3.01/0.94  ------ 
% 3.01/0.94  
% 3.01/0.94  ------ Input Options
% 3.01/0.94  
% 3.01/0.94  --out_options                           all
% 3.01/0.94  --tptp_safe_out                         true
% 3.01/0.94  --problem_path                          ""
% 3.01/0.94  --include_path                          ""
% 3.01/0.94  --clausifier                            res/vclausify_rel
% 3.01/0.94  --clausifier_options                    --mode clausify
% 3.01/0.94  --stdin                                 false
% 3.01/0.94  --stats_out                             all
% 3.01/0.94  
% 3.01/0.94  ------ General Options
% 3.01/0.94  
% 3.01/0.94  --fof                                   false
% 3.01/0.94  --time_out_real                         305.
% 3.01/0.94  --time_out_virtual                      -1.
% 3.01/0.94  --symbol_type_check                     false
% 3.01/0.94  --clausify_out                          false
% 3.01/0.94  --sig_cnt_out                           false
% 3.01/0.94  --trig_cnt_out                          false
% 3.01/0.94  --trig_cnt_out_tolerance                1.
% 3.01/0.94  --trig_cnt_out_sk_spl                   false
% 3.01/0.94  --abstr_cl_out                          false
% 3.01/0.94  
% 3.01/0.94  ------ Global Options
% 3.01/0.94  
% 3.01/0.94  --schedule                              default
% 3.01/0.94  --add_important_lit                     false
% 3.01/0.94  --prop_solver_per_cl                    1000
% 3.01/0.94  --min_unsat_core                        false
% 3.01/0.94  --soft_assumptions                      false
% 3.01/0.94  --soft_lemma_size                       3
% 3.01/0.94  --prop_impl_unit_size                   0
% 3.01/0.94  --prop_impl_unit                        []
% 3.01/0.94  --share_sel_clauses                     true
% 3.01/0.94  --reset_solvers                         false
% 3.01/0.94  --bc_imp_inh                            [conj_cone]
% 3.01/0.94  --conj_cone_tolerance                   3.
% 3.01/0.94  --extra_neg_conj                        none
% 3.01/0.94  --large_theory_mode                     true
% 3.01/0.94  --prolific_symb_bound                   200
% 3.01/0.94  --lt_threshold                          2000
% 3.01/0.94  --clause_weak_htbl                      true
% 3.01/0.94  --gc_record_bc_elim                     false
% 3.01/0.94  
% 3.01/0.94  ------ Preprocessing Options
% 3.01/0.94  
% 3.01/0.94  --preprocessing_flag                    true
% 3.01/0.94  --time_out_prep_mult                    0.1
% 3.01/0.94  --splitting_mode                        input
% 3.01/0.94  --splitting_grd                         true
% 3.01/0.94  --splitting_cvd                         false
% 3.01/0.94  --splitting_cvd_svl                     false
% 3.01/0.94  --splitting_nvd                         32
% 3.01/0.94  --sub_typing                            true
% 3.01/0.94  --prep_gs_sim                           true
% 3.01/0.94  --prep_unflatten                        true
% 3.01/0.94  --prep_res_sim                          true
% 3.01/0.94  --prep_upred                            true
% 3.01/0.94  --prep_sem_filter                       exhaustive
% 3.01/0.94  --prep_sem_filter_out                   false
% 3.01/0.94  --pred_elim                             true
% 3.01/0.94  --res_sim_input                         true
% 3.01/0.94  --eq_ax_congr_red                       true
% 3.01/0.94  --pure_diseq_elim                       true
% 3.01/0.94  --brand_transform                       false
% 3.01/0.94  --non_eq_to_eq                          false
% 3.01/0.94  --prep_def_merge                        true
% 3.01/0.94  --prep_def_merge_prop_impl              false
% 3.01/0.94  --prep_def_merge_mbd                    true
% 3.01/0.94  --prep_def_merge_tr_red                 false
% 3.01/0.94  --prep_def_merge_tr_cl                  false
% 3.01/0.94  --smt_preprocessing                     true
% 3.01/0.94  --smt_ac_axioms                         fast
% 3.01/0.94  --preprocessed_out                      false
% 3.01/0.94  --preprocessed_stats                    false
% 3.01/0.94  
% 3.01/0.94  ------ Abstraction refinement Options
% 3.01/0.94  
% 3.01/0.94  --abstr_ref                             []
% 3.01/0.94  --abstr_ref_prep                        false
% 3.01/0.94  --abstr_ref_until_sat                   false
% 3.01/0.94  --abstr_ref_sig_restrict                funpre
% 3.01/0.94  --abstr_ref_af_restrict_to_split_sk     false
% 3.01/0.94  --abstr_ref_under                       []
% 3.01/0.94  
% 3.01/0.94  ------ SAT Options
% 3.01/0.94  
% 3.01/0.94  --sat_mode                              false
% 3.01/0.94  --sat_fm_restart_options                ""
% 3.01/0.94  --sat_gr_def                            false
% 3.01/0.94  --sat_epr_types                         true
% 3.01/0.94  --sat_non_cyclic_types                  false
% 3.01/0.94  --sat_finite_models                     false
% 3.01/0.94  --sat_fm_lemmas                         false
% 3.01/0.94  --sat_fm_prep                           false
% 3.01/0.94  --sat_fm_uc_incr                        true
% 3.01/0.94  --sat_out_model                         small
% 3.01/0.94  --sat_out_clauses                       false
% 3.01/0.94  
% 3.01/0.94  ------ QBF Options
% 3.01/0.94  
% 3.01/0.94  --qbf_mode                              false
% 3.01/0.94  --qbf_elim_univ                         false
% 3.01/0.94  --qbf_dom_inst                          none
% 3.01/0.94  --qbf_dom_pre_inst                      false
% 3.01/0.94  --qbf_sk_in                             false
% 3.01/0.94  --qbf_pred_elim                         true
% 3.01/0.94  --qbf_split                             512
% 3.01/0.94  
% 3.01/0.94  ------ BMC1 Options
% 3.01/0.94  
% 3.01/0.94  --bmc1_incremental                      false
% 3.01/0.94  --bmc1_axioms                           reachable_all
% 3.01/0.94  --bmc1_min_bound                        0
% 3.01/0.94  --bmc1_max_bound                        -1
% 3.01/0.94  --bmc1_max_bound_default                -1
% 3.01/0.94  --bmc1_symbol_reachability              true
% 3.01/0.94  --bmc1_property_lemmas                  false
% 3.01/0.94  --bmc1_k_induction                      false
% 3.01/0.94  --bmc1_non_equiv_states                 false
% 3.01/0.94  --bmc1_deadlock                         false
% 3.01/0.94  --bmc1_ucm                              false
% 3.01/0.94  --bmc1_add_unsat_core                   none
% 3.01/0.94  --bmc1_unsat_core_children              false
% 3.01/0.94  --bmc1_unsat_core_extrapolate_axioms    false
% 3.01/0.94  --bmc1_out_stat                         full
% 3.01/0.94  --bmc1_ground_init                      false
% 3.01/0.94  --bmc1_pre_inst_next_state              false
% 3.01/0.94  --bmc1_pre_inst_state                   false
% 3.01/0.94  --bmc1_pre_inst_reach_state             false
% 3.01/0.94  --bmc1_out_unsat_core                   false
% 3.01/0.94  --bmc1_aig_witness_out                  false
% 3.01/0.94  --bmc1_verbose                          false
% 3.01/0.94  --bmc1_dump_clauses_tptp                false
% 3.01/0.94  --bmc1_dump_unsat_core_tptp             false
% 3.01/0.94  --bmc1_dump_file                        -
% 3.01/0.94  --bmc1_ucm_expand_uc_limit              128
% 3.01/0.94  --bmc1_ucm_n_expand_iterations          6
% 3.01/0.94  --bmc1_ucm_extend_mode                  1
% 3.01/0.94  --bmc1_ucm_init_mode                    2
% 3.01/0.94  --bmc1_ucm_cone_mode                    none
% 3.01/0.94  --bmc1_ucm_reduced_relation_type        0
% 3.01/0.94  --bmc1_ucm_relax_model                  4
% 3.01/0.94  --bmc1_ucm_full_tr_after_sat            true
% 3.01/0.94  --bmc1_ucm_expand_neg_assumptions       false
% 3.01/0.94  --bmc1_ucm_layered_model                none
% 3.01/0.94  --bmc1_ucm_max_lemma_size               10
% 3.01/0.94  
% 3.01/0.94  ------ AIG Options
% 3.01/0.94  
% 3.01/0.94  --aig_mode                              false
% 3.01/0.94  
% 3.01/0.94  ------ Instantiation Options
% 3.01/0.94  
% 3.01/0.94  --instantiation_flag                    true
% 3.01/0.94  --inst_sos_flag                         false
% 3.01/0.94  --inst_sos_phase                        true
% 3.01/0.94  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.01/0.94  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.01/0.94  --inst_lit_sel_side                     none
% 3.01/0.94  --inst_solver_per_active                1400
% 3.01/0.94  --inst_solver_calls_frac                1.
% 3.01/0.94  --inst_passive_queue_type               priority_queues
% 3.01/0.94  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.01/0.94  --inst_passive_queues_freq              [25;2]
% 3.01/0.94  --inst_dismatching                      true
% 3.01/0.94  --inst_eager_unprocessed_to_passive     true
% 3.01/0.94  --inst_prop_sim_given                   true
% 3.01/0.94  --inst_prop_sim_new                     false
% 3.01/0.94  --inst_subs_new                         false
% 3.01/0.94  --inst_eq_res_simp                      false
% 3.01/0.94  --inst_subs_given                       false
% 3.01/0.94  --inst_orphan_elimination               true
% 3.01/0.94  --inst_learning_loop_flag               true
% 3.01/0.94  --inst_learning_start                   3000
% 3.01/0.94  --inst_learning_factor                  2
% 3.01/0.94  --inst_start_prop_sim_after_learn       3
% 3.01/0.94  --inst_sel_renew                        solver
% 3.01/0.94  --inst_lit_activity_flag                true
% 3.01/0.94  --inst_restr_to_given                   false
% 3.01/0.94  --inst_activity_threshold               500
% 3.01/0.94  --inst_out_proof                        true
% 3.01/0.94  
% 3.01/0.94  ------ Resolution Options
% 3.01/0.94  
% 3.01/0.94  --resolution_flag                       false
% 3.01/0.94  --res_lit_sel                           adaptive
% 3.01/0.94  --res_lit_sel_side                      none
% 3.01/0.94  --res_ordering                          kbo
% 3.01/0.94  --res_to_prop_solver                    active
% 3.01/0.94  --res_prop_simpl_new                    false
% 3.01/0.94  --res_prop_simpl_given                  true
% 3.01/0.94  --res_passive_queue_type                priority_queues
% 3.01/0.94  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.01/0.94  --res_passive_queues_freq               [15;5]
% 3.01/0.94  --res_forward_subs                      full
% 3.01/0.94  --res_backward_subs                     full
% 3.01/0.94  --res_forward_subs_resolution           true
% 3.01/0.94  --res_backward_subs_resolution          true
% 3.01/0.94  --res_orphan_elimination                true
% 3.01/0.94  --res_time_limit                        2.
% 3.01/0.94  --res_out_proof                         true
% 3.01/0.94  
% 3.01/0.94  ------ Superposition Options
% 3.01/0.94  
% 3.01/0.94  --superposition_flag                    true
% 3.01/0.94  --sup_passive_queue_type                priority_queues
% 3.01/0.94  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.01/0.94  --sup_passive_queues_freq               [8;1;4]
% 3.01/0.94  --demod_completeness_check              fast
% 3.01/0.94  --demod_use_ground                      true
% 3.01/0.94  --sup_to_prop_solver                    passive
% 3.01/0.94  --sup_prop_simpl_new                    true
% 3.01/0.94  --sup_prop_simpl_given                  true
% 3.01/0.94  --sup_fun_splitting                     false
% 3.01/0.94  --sup_smt_interval                      50000
% 3.01/0.94  
% 3.01/0.94  ------ Superposition Simplification Setup
% 3.01/0.94  
% 3.01/0.94  --sup_indices_passive                   []
% 3.01/0.94  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/0.94  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/0.94  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/0.94  --sup_full_triv                         [TrivRules;PropSubs]
% 3.01/0.94  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/0.94  --sup_full_bw                           [BwDemod]
% 3.01/0.94  --sup_immed_triv                        [TrivRules]
% 3.01/0.94  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.01/0.94  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/0.94  --sup_immed_bw_main                     []
% 3.01/0.94  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.01/0.94  --sup_input_triv                        [Unflattening;TrivRules]
% 3.01/0.94  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/0.94  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.01/0.94  
% 3.01/0.94  ------ Combination Options
% 3.01/0.94  
% 3.01/0.94  --comb_res_mult                         3
% 3.01/0.94  --comb_sup_mult                         2
% 3.01/0.94  --comb_inst_mult                        10
% 3.01/0.94  
% 3.01/0.94  ------ Debug Options
% 3.01/0.94  
% 3.01/0.94  --dbg_backtrace                         false
% 3.01/0.94  --dbg_dump_prop_clauses                 false
% 3.01/0.94  --dbg_dump_prop_clauses_file            -
% 3.01/0.94  --dbg_out_stat                          false
% 3.01/0.94  
% 3.01/0.94  
% 3.01/0.94  
% 3.01/0.94  
% 3.01/0.94  ------ Proving...
% 3.01/0.94  
% 3.01/0.94  
% 3.01/0.94  % SZS status Theorem for theBenchmark.p
% 3.01/0.94  
% 3.01/0.94  % SZS output start CNFRefutation for theBenchmark.p
% 3.01/0.94  
% 3.01/0.94  fof(f15,conjecture,(
% 3.01/0.94    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 3.01/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.94  
% 3.01/0.94  fof(f16,negated_conjecture,(
% 3.01/0.94    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 3.01/0.94    inference(negated_conjecture,[],[f15])).
% 3.01/0.94  
% 3.01/0.94  fof(f30,plain,(
% 3.01/0.94    ? [X0,X1] : ((~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 3.01/0.94    inference(ennf_transformation,[],[f16])).
% 3.01/0.94  
% 3.01/0.94  fof(f31,plain,(
% 3.01/0.94    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 3.01/0.94    inference(flattening,[],[f30])).
% 3.01/0.94  
% 3.01/0.94  fof(f32,plain,(
% 3.01/0.94    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 3.01/0.94    introduced(choice_axiom,[])).
% 3.01/0.94  
% 3.01/0.94  fof(f33,plain,(
% 3.01/0.94    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1)),
% 3.01/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f32])).
% 3.01/0.94  
% 3.01/0.94  fof(f50,plain,(
% 3.01/0.94    v1_relat_1(sK1)),
% 3.01/0.94    inference(cnf_transformation,[],[f33])).
% 3.01/0.94  
% 3.01/0.94  fof(f1,axiom,(
% 3.01/0.94    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 3.01/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.94  
% 3.01/0.94  fof(f18,plain,(
% 3.01/0.94    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.01/0.94    inference(ennf_transformation,[],[f1])).
% 3.01/0.94  
% 3.01/0.94  fof(f34,plain,(
% 3.01/0.94    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 3.01/0.94    inference(cnf_transformation,[],[f18])).
% 3.01/0.94  
% 3.01/0.94  fof(f4,axiom,(
% 3.01/0.94    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 3.01/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.94  
% 3.01/0.94  fof(f21,plain,(
% 3.01/0.94    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.01/0.94    inference(ennf_transformation,[],[f4])).
% 3.01/0.94  
% 3.01/0.94  fof(f37,plain,(
% 3.01/0.94    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.01/0.94    inference(cnf_transformation,[],[f21])).
% 3.01/0.95  
% 3.01/0.95  fof(f13,axiom,(
% 3.01/0.95    ! [X0,X1] : (v1_relat_1(X1) => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0))),
% 3.01/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.95  
% 3.01/0.95  fof(f29,plain,(
% 3.01/0.95    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.01/0.95    inference(ennf_transformation,[],[f13])).
% 3.01/0.95  
% 3.01/0.95  fof(f48,plain,(
% 3.01/0.95    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.01/0.95    inference(cnf_transformation,[],[f29])).
% 3.01/0.95  
% 3.01/0.95  fof(f14,axiom,(
% 3.01/0.95    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.01/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.95  
% 3.01/0.95  fof(f17,plain,(
% 3.01/0.95    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 3.01/0.95    inference(pure_predicate_removal,[],[f14])).
% 3.01/0.95  
% 3.01/0.95  fof(f49,plain,(
% 3.01/0.95    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 3.01/0.95    inference(cnf_transformation,[],[f17])).
% 3.01/0.95  
% 3.01/0.95  fof(f8,axiom,(
% 3.01/0.95    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 3.01/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.95  
% 3.01/0.95  fof(f25,plain,(
% 3.01/0.95    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.01/0.95    inference(ennf_transformation,[],[f8])).
% 3.01/0.95  
% 3.01/0.95  fof(f42,plain,(
% 3.01/0.95    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.01/0.95    inference(cnf_transformation,[],[f25])).
% 3.01/0.95  
% 3.01/0.95  fof(f10,axiom,(
% 3.01/0.95    ! [X0] : k4_relat_1(k6_relat_1(X0)) = k6_relat_1(X0)),
% 3.01/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.95  
% 3.01/0.95  fof(f45,plain,(
% 3.01/0.95    ( ! [X0] : (k4_relat_1(k6_relat_1(X0)) = k6_relat_1(X0)) )),
% 3.01/0.95    inference(cnf_transformation,[],[f10])).
% 3.01/0.95  
% 3.01/0.95  fof(f3,axiom,(
% 3.01/0.95    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 3.01/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.95  
% 3.01/0.95  fof(f20,plain,(
% 3.01/0.95    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 3.01/0.95    inference(ennf_transformation,[],[f3])).
% 3.01/0.95  
% 3.01/0.95  fof(f36,plain,(
% 3.01/0.95    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 3.01/0.95    inference(cnf_transformation,[],[f20])).
% 3.01/0.95  
% 3.01/0.95  fof(f2,axiom,(
% 3.01/0.95    ! [X0,X1] : (v1_relat_1(X1) => v1_relat_1(k8_relat_1(X0,X1)))),
% 3.01/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.95  
% 3.01/0.95  fof(f19,plain,(
% 3.01/0.95    ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 3.01/0.95    inference(ennf_transformation,[],[f2])).
% 3.01/0.95  
% 3.01/0.95  fof(f35,plain,(
% 3.01/0.95    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 3.01/0.95    inference(cnf_transformation,[],[f19])).
% 3.01/0.95  
% 3.01/0.95  fof(f7,axiom,(
% 3.01/0.95    ! [X0] : (v1_relat_1(X0) => (k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 3.01/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.95  
% 3.01/0.95  fof(f24,plain,(
% 3.01/0.95    ! [X0] : ((k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.01/0.95    inference(ennf_transformation,[],[f7])).
% 3.01/0.95  
% 3.01/0.95  fof(f41,plain,(
% 3.01/0.95    ( ! [X0] : (k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.01/0.95    inference(cnf_transformation,[],[f24])).
% 3.01/0.95  
% 3.01/0.95  fof(f6,axiom,(
% 3.01/0.95    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 3.01/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.95  
% 3.01/0.95  fof(f23,plain,(
% 3.01/0.95    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.01/0.95    inference(ennf_transformation,[],[f6])).
% 3.01/0.95  
% 3.01/0.95  fof(f39,plain,(
% 3.01/0.95    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.01/0.95    inference(cnf_transformation,[],[f23])).
% 3.01/0.95  
% 3.01/0.95  fof(f9,axiom,(
% 3.01/0.95    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.01/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.95  
% 3.01/0.95  fof(f43,plain,(
% 3.01/0.95    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 3.01/0.95    inference(cnf_transformation,[],[f9])).
% 3.01/0.95  
% 3.01/0.95  fof(f51,plain,(
% 3.01/0.95    r1_tarski(sK0,k1_relat_1(sK1))),
% 3.01/0.95    inference(cnf_transformation,[],[f33])).
% 3.01/0.95  
% 3.01/0.95  fof(f12,axiom,(
% 3.01/0.95    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 3.01/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.95  
% 3.01/0.95  fof(f27,plain,(
% 3.01/0.95    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 3.01/0.95    inference(ennf_transformation,[],[f12])).
% 3.01/0.95  
% 3.01/0.95  fof(f28,plain,(
% 3.01/0.95    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.01/0.95    inference(flattening,[],[f27])).
% 3.01/0.95  
% 3.01/0.95  fof(f47,plain,(
% 3.01/0.95    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.01/0.95    inference(cnf_transformation,[],[f28])).
% 3.01/0.95  
% 3.01/0.95  fof(f11,axiom,(
% 3.01/0.95    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 3.01/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.95  
% 3.01/0.95  fof(f26,plain,(
% 3.01/0.95    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.01/0.95    inference(ennf_transformation,[],[f11])).
% 3.01/0.95  
% 3.01/0.95  fof(f46,plain,(
% 3.01/0.95    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.01/0.95    inference(cnf_transformation,[],[f26])).
% 3.01/0.95  
% 3.01/0.95  fof(f5,axiom,(
% 3.01/0.95    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k3_xboole_0(k1_relat_1(X1),X0),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0))))),
% 3.01/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.95  
% 3.01/0.95  fof(f22,plain,(
% 3.01/0.95    ! [X0,X1] : (r1_tarski(k3_xboole_0(k1_relat_1(X1),X0),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.01/0.95    inference(ennf_transformation,[],[f5])).
% 3.01/0.95  
% 3.01/0.95  fof(f38,plain,(
% 3.01/0.95    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(k1_relat_1(X1),X0),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0))) | ~v1_relat_1(X1)) )),
% 3.01/0.95    inference(cnf_transformation,[],[f22])).
% 3.01/0.95  
% 3.01/0.95  fof(f52,plain,(
% 3.01/0.95    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 3.01/0.95    inference(cnf_transformation,[],[f33])).
% 3.01/0.95  
% 3.01/0.95  cnf(c_18,negated_conjecture,
% 3.01/0.95      ( v1_relat_1(sK1) ),
% 3.01/0.95      inference(cnf_transformation,[],[f50]) ).
% 3.01/0.95  
% 3.01/0.95  cnf(c_554,plain,
% 3.01/0.95      ( v1_relat_1(sK1) = iProver_top ),
% 3.01/0.95      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.01/0.95  
% 3.01/0.95  cnf(c_0,plain,
% 3.01/0.95      ( ~ v1_relat_1(X0) | v1_relat_1(k4_relat_1(X0)) ),
% 3.01/0.95      inference(cnf_transformation,[],[f34]) ).
% 3.01/0.95  
% 3.01/0.95  cnf(c_569,plain,
% 3.01/0.95      ( v1_relat_1(X0) != iProver_top
% 3.01/0.95      | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
% 3.01/0.95      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.01/0.95  
% 3.01/0.95  cnf(c_3,plain,
% 3.01/0.95      ( ~ v1_relat_1(X0)
% 3.01/0.95      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 3.01/0.95      inference(cnf_transformation,[],[f37]) ).
% 3.01/0.95  
% 3.01/0.95  cnf(c_566,plain,
% 3.01/0.95      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 3.01/0.95      | v1_relat_1(X0) != iProver_top ),
% 3.01/0.95      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.01/0.95  
% 3.01/0.95  cnf(c_1126,plain,
% 3.01/0.95      ( k2_relat_1(k7_relat_1(k4_relat_1(X0),X1)) = k9_relat_1(k4_relat_1(X0),X1)
% 3.01/0.95      | v1_relat_1(X0) != iProver_top ),
% 3.01/0.95      inference(superposition,[status(thm)],[c_569,c_566]) ).
% 3.01/0.95  
% 3.01/0.95  cnf(c_6177,plain,
% 3.01/0.95      ( k2_relat_1(k7_relat_1(k4_relat_1(sK1),X0)) = k9_relat_1(k4_relat_1(sK1),X0) ),
% 3.01/0.95      inference(superposition,[status(thm)],[c_554,c_1126]) ).
% 3.01/0.95  
% 3.01/0.95  cnf(c_14,plain,
% 3.01/0.95      ( ~ v1_relat_1(X0)
% 3.01/0.95      | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
% 3.01/0.95      inference(cnf_transformation,[],[f48]) ).
% 3.01/0.95  
% 3.01/0.95  cnf(c_558,plain,
% 3.01/0.95      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
% 3.01/0.95      | v1_relat_1(X1) != iProver_top ),
% 3.01/0.95      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.01/0.95  
% 3.01/0.95  cnf(c_882,plain,
% 3.01/0.95      ( k5_relat_1(k6_relat_1(X0),k4_relat_1(X1)) = k7_relat_1(k4_relat_1(X1),X0)
% 3.01/0.95      | v1_relat_1(X1) != iProver_top ),
% 3.01/0.95      inference(superposition,[status(thm)],[c_569,c_558]) ).
% 3.01/0.95  
% 3.01/0.95  cnf(c_4504,plain,
% 3.01/0.95      ( k5_relat_1(k6_relat_1(X0),k4_relat_1(sK1)) = k7_relat_1(k4_relat_1(sK1),X0) ),
% 3.01/0.95      inference(superposition,[status(thm)],[c_554,c_882]) ).
% 3.01/0.95  
% 3.01/0.95  cnf(c_15,plain,
% 3.01/0.95      ( v1_relat_1(k6_relat_1(X0)) ),
% 3.01/0.95      inference(cnf_transformation,[],[f49]) ).
% 3.01/0.95  
% 3.01/0.95  cnf(c_557,plain,
% 3.01/0.95      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 3.01/0.95      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.01/0.95  
% 3.01/0.95  cnf(c_8,plain,
% 3.01/0.95      ( ~ v1_relat_1(X0)
% 3.01/0.95      | ~ v1_relat_1(X1)
% 3.01/0.95      | k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1)) ),
% 3.01/0.95      inference(cnf_transformation,[],[f42]) ).
% 3.01/0.95  
% 3.01/0.95  cnf(c_561,plain,
% 3.01/0.95      ( k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,X0))
% 3.01/0.95      | v1_relat_1(X1) != iProver_top
% 3.01/0.95      | v1_relat_1(X0) != iProver_top ),
% 3.01/0.95      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.01/0.95  
% 3.01/0.95  cnf(c_3096,plain,
% 3.01/0.95      ( k5_relat_1(k4_relat_1(k6_relat_1(X0)),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,k6_relat_1(X0)))
% 3.01/0.95      | v1_relat_1(X1) != iProver_top ),
% 3.01/0.95      inference(superposition,[status(thm)],[c_557,c_561]) ).
% 3.01/0.95  
% 3.01/0.95  cnf(c_11,plain,
% 3.01/0.95      ( k4_relat_1(k6_relat_1(X0)) = k6_relat_1(X0) ),
% 3.01/0.95      inference(cnf_transformation,[],[f45]) ).
% 3.01/0.95  
% 3.01/0.95  cnf(c_3104,plain,
% 3.01/0.95      ( k5_relat_1(k6_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,k6_relat_1(X0)))
% 3.01/0.95      | v1_relat_1(X1) != iProver_top ),
% 3.01/0.95      inference(light_normalisation,[status(thm)],[c_3096,c_11]) ).
% 3.01/0.95  
% 3.01/0.95  cnf(c_3135,plain,
% 3.01/0.95      ( k5_relat_1(k6_relat_1(X0),k4_relat_1(sK1)) = k4_relat_1(k5_relat_1(sK1,k6_relat_1(X0))) ),
% 3.01/0.95      inference(superposition,[status(thm)],[c_554,c_3104]) ).
% 3.01/0.95  
% 3.01/0.95  cnf(c_2,plain,
% 3.01/0.95      ( ~ v1_relat_1(X0)
% 3.01/0.95      | k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0) ),
% 3.01/0.95      inference(cnf_transformation,[],[f36]) ).
% 3.01/0.95  
% 3.01/0.95  cnf(c_567,plain,
% 3.01/0.95      ( k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0)
% 3.01/0.95      | v1_relat_1(X0) != iProver_top ),
% 3.01/0.95      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.01/0.95  
% 3.01/0.95  cnf(c_1546,plain,
% 3.01/0.95      ( k5_relat_1(sK1,k6_relat_1(X0)) = k8_relat_1(X0,sK1) ),
% 3.01/0.95      inference(superposition,[status(thm)],[c_554,c_567]) ).
% 3.01/0.95  
% 3.01/0.95  cnf(c_3137,plain,
% 3.01/0.95      ( k5_relat_1(k6_relat_1(X0),k4_relat_1(sK1)) = k4_relat_1(k8_relat_1(X0,sK1)) ),
% 3.01/0.95      inference(light_normalisation,[status(thm)],[c_3135,c_1546]) ).
% 3.01/0.95  
% 3.01/0.95  cnf(c_4506,plain,
% 3.01/0.95      ( k7_relat_1(k4_relat_1(sK1),X0) = k4_relat_1(k8_relat_1(X0,sK1)) ),
% 3.01/0.95      inference(light_normalisation,[status(thm)],[c_4504,c_3137]) ).
% 3.01/0.95  
% 3.01/0.95  cnf(c_1,plain,
% 3.01/0.95      ( ~ v1_relat_1(X0) | v1_relat_1(k8_relat_1(X1,X0)) ),
% 3.01/0.95      inference(cnf_transformation,[],[f35]) ).
% 3.01/0.95  
% 3.01/0.95  cnf(c_568,plain,
% 3.01/0.95      ( v1_relat_1(X0) != iProver_top
% 3.01/0.95      | v1_relat_1(k8_relat_1(X1,X0)) = iProver_top ),
% 3.01/0.95      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.01/0.95  
% 3.01/0.95  cnf(c_6,plain,
% 3.01/0.95      ( ~ v1_relat_1(X0) | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
% 3.01/0.95      inference(cnf_transformation,[],[f41]) ).
% 3.01/0.95  
% 3.01/0.95  cnf(c_563,plain,
% 3.01/0.95      ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
% 3.01/0.95      | v1_relat_1(X0) != iProver_top ),
% 3.01/0.95      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.01/0.95  
% 3.01/0.95  cnf(c_1002,plain,
% 3.01/0.95      ( k2_relat_1(k4_relat_1(k8_relat_1(X0,X1))) = k1_relat_1(k8_relat_1(X0,X1))
% 3.01/0.95      | v1_relat_1(X1) != iProver_top ),
% 3.01/0.95      inference(superposition,[status(thm)],[c_568,c_563]) ).
% 3.01/0.95  
% 3.01/0.95  cnf(c_4776,plain,
% 3.01/0.95      ( k2_relat_1(k4_relat_1(k8_relat_1(X0,sK1))) = k1_relat_1(k8_relat_1(X0,sK1)) ),
% 3.01/0.95      inference(superposition,[status(thm)],[c_554,c_1002]) ).
% 3.01/0.95  
% 3.01/0.95  cnf(c_5,plain,
% 3.01/0.95      ( ~ v1_relat_1(X0)
% 3.01/0.95      | ~ v1_relat_1(X1)
% 3.01/0.95      | k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1)) ),
% 3.01/0.95      inference(cnf_transformation,[],[f39]) ).
% 3.01/0.95  
% 3.01/0.95  cnf(c_564,plain,
% 3.01/0.95      ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
% 3.01/0.95      | v1_relat_1(X0) != iProver_top
% 3.01/0.95      | v1_relat_1(X1) != iProver_top ),
% 3.01/0.95      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.01/0.95  
% 3.01/0.95  cnf(c_3367,plain,
% 3.01/0.95      ( k10_relat_1(sK1,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(sK1,X0))
% 3.01/0.95      | v1_relat_1(X0) != iProver_top ),
% 3.01/0.95      inference(superposition,[status(thm)],[c_554,c_564]) ).
% 3.01/0.95  
% 3.01/0.95  cnf(c_3764,plain,
% 3.01/0.95      ( k10_relat_1(sK1,k1_relat_1(k6_relat_1(X0))) = k1_relat_1(k5_relat_1(sK1,k6_relat_1(X0))) ),
% 3.01/0.95      inference(superposition,[status(thm)],[c_557,c_3367]) ).
% 3.01/0.95  
% 3.01/0.95  cnf(c_10,plain,
% 3.01/0.95      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 3.01/0.95      inference(cnf_transformation,[],[f43]) ).
% 3.01/0.95  
% 3.01/0.95  cnf(c_3769,plain,
% 3.01/0.95      ( k1_relat_1(k8_relat_1(X0,sK1)) = k10_relat_1(sK1,X0) ),
% 3.01/0.95      inference(light_normalisation,[status(thm)],[c_3764,c_10,c_1546]) ).
% 3.01/0.95  
% 3.01/0.95  cnf(c_4778,plain,
% 3.01/0.95      ( k2_relat_1(k4_relat_1(k8_relat_1(X0,sK1))) = k10_relat_1(sK1,X0) ),
% 3.01/0.95      inference(light_normalisation,[status(thm)],[c_4776,c_3769]) ).
% 3.01/0.95  
% 3.01/0.95  cnf(c_6179,plain,
% 3.01/0.95      ( k9_relat_1(k4_relat_1(sK1),X0) = k10_relat_1(sK1,X0) ),
% 3.01/0.95      inference(light_normalisation,[status(thm)],[c_6177,c_4506,c_4778]) ).
% 3.01/0.95  
% 3.01/0.95  cnf(c_17,negated_conjecture,
% 3.01/0.95      ( r1_tarski(sK0,k1_relat_1(sK1)) ),
% 3.01/0.95      inference(cnf_transformation,[],[f51]) ).
% 3.01/0.95  
% 3.01/0.95  cnf(c_555,plain,
% 3.01/0.95      ( r1_tarski(sK0,k1_relat_1(sK1)) = iProver_top ),
% 3.01/0.95      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.01/0.95  
% 3.01/0.95  cnf(c_13,plain,
% 3.01/0.95      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 3.01/0.95      | ~ v1_relat_1(X1)
% 3.01/0.95      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 3.01/0.95      inference(cnf_transformation,[],[f47]) ).
% 3.01/0.95  
% 3.01/0.95  cnf(c_559,plain,
% 3.01/0.95      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 3.01/0.95      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 3.01/0.95      | v1_relat_1(X0) != iProver_top ),
% 3.01/0.95      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.01/0.95  
% 3.01/0.95  cnf(c_1764,plain,
% 3.01/0.95      ( k1_relat_1(k7_relat_1(sK1,sK0)) = sK0
% 3.01/0.95      | v1_relat_1(sK1) != iProver_top ),
% 3.01/0.95      inference(superposition,[status(thm)],[c_555,c_559]) ).
% 3.01/0.95  
% 3.01/0.95  cnf(c_229,plain,
% 3.01/0.95      ( ~ v1_relat_1(X0)
% 3.01/0.95      | k1_relat_1(X0) != k1_relat_1(sK1)
% 3.01/0.95      | k1_relat_1(k7_relat_1(X0,X1)) = X1
% 3.01/0.95      | sK0 != X1 ),
% 3.01/0.95      inference(resolution_lifted,[status(thm)],[c_13,c_17]) ).
% 3.01/0.95  
% 3.01/0.95  cnf(c_230,plain,
% 3.01/0.95      ( ~ v1_relat_1(X0)
% 3.01/0.95      | k1_relat_1(X0) != k1_relat_1(sK1)
% 3.01/0.95      | k1_relat_1(k7_relat_1(X0,sK0)) = sK0 ),
% 3.01/0.95      inference(unflattening,[status(thm)],[c_229]) ).
% 3.01/0.95  
% 3.01/0.95  cnf(c_232,plain,
% 3.01/0.95      ( ~ v1_relat_1(sK1)
% 3.01/0.95      | k1_relat_1(k7_relat_1(sK1,sK0)) = sK0
% 3.01/0.95      | k1_relat_1(sK1) != k1_relat_1(sK1) ),
% 3.01/0.95      inference(instantiation,[status(thm)],[c_230]) ).
% 3.01/0.95  
% 3.01/0.95  cnf(c_271,plain,
% 3.01/0.95      ( X0 != X1 | k1_relat_1(X0) = k1_relat_1(X1) ),
% 3.01/0.95      theory(equality) ).
% 3.01/0.95  
% 3.01/0.95  cnf(c_280,plain,
% 3.01/0.95      ( k1_relat_1(sK1) = k1_relat_1(sK1) | sK1 != sK1 ),
% 3.01/0.95      inference(instantiation,[status(thm)],[c_271]) ).
% 3.01/0.95  
% 3.01/0.95  cnf(c_264,plain,( X0 = X0 ),theory(equality) ).
% 3.01/0.95  
% 3.01/0.95  cnf(c_285,plain,
% 3.01/0.95      ( sK1 = sK1 ),
% 3.01/0.95      inference(instantiation,[status(thm)],[c_264]) ).
% 3.01/0.95  
% 3.01/0.95  cnf(c_2378,plain,
% 3.01/0.95      ( k1_relat_1(k7_relat_1(sK1,sK0)) = sK0 ),
% 3.01/0.95      inference(global_propositional_subsumption,
% 3.01/0.95                [status(thm)],
% 3.01/0.95                [c_1764,c_18,c_232,c_280,c_285]) ).
% 3.01/0.95  
% 3.01/0.95  cnf(c_12,plain,
% 3.01/0.95      ( ~ v1_relat_1(X0)
% 3.01/0.95      | k3_xboole_0(k1_relat_1(X0),X1) = k1_relat_1(k7_relat_1(X0,X1)) ),
% 3.01/0.95      inference(cnf_transformation,[],[f46]) ).
% 3.01/0.95  
% 3.01/0.95  cnf(c_560,plain,
% 3.01/0.95      ( k3_xboole_0(k1_relat_1(X0),X1) = k1_relat_1(k7_relat_1(X0,X1))
% 3.01/0.95      | v1_relat_1(X0) != iProver_top ),
% 3.01/0.95      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.01/0.95  
% 3.01/0.95  cnf(c_1904,plain,
% 3.01/0.95      ( k3_xboole_0(k1_relat_1(sK1),X0) = k1_relat_1(k7_relat_1(sK1,X0)) ),
% 3.01/0.95      inference(superposition,[status(thm)],[c_554,c_560]) ).
% 3.01/0.95  
% 3.01/0.95  cnf(c_4,plain,
% 3.01/0.95      ( r1_tarski(k3_xboole_0(k1_relat_1(X0),X1),k9_relat_1(k4_relat_1(X0),k9_relat_1(X0,X1)))
% 3.01/0.95      | ~ v1_relat_1(X0) ),
% 3.01/0.95      inference(cnf_transformation,[],[f38]) ).
% 3.01/0.95  
% 3.01/0.95  cnf(c_565,plain,
% 3.01/0.95      ( r1_tarski(k3_xboole_0(k1_relat_1(X0),X1),k9_relat_1(k4_relat_1(X0),k9_relat_1(X0,X1))) = iProver_top
% 3.01/0.95      | v1_relat_1(X0) != iProver_top ),
% 3.01/0.95      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.01/0.95  
% 3.01/0.95  cnf(c_2363,plain,
% 3.01/0.95      ( r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,X0))) = iProver_top
% 3.01/0.95      | v1_relat_1(sK1) != iProver_top ),
% 3.01/0.95      inference(superposition,[status(thm)],[c_1904,c_565]) ).
% 3.01/0.95  
% 3.01/0.95  cnf(c_19,plain,
% 3.01/0.95      ( v1_relat_1(sK1) = iProver_top ),
% 3.01/0.95      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.01/0.95  
% 3.01/0.95  cnf(c_2782,plain,
% 3.01/0.95      ( r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,X0))) = iProver_top ),
% 3.01/0.95      inference(global_propositional_subsumption,
% 3.01/0.95                [status(thm)],
% 3.01/0.95                [c_2363,c_19]) ).
% 3.01/0.95  
% 3.01/0.95  cnf(c_2789,plain,
% 3.01/0.95      ( r1_tarski(sK0,k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,sK0))) = iProver_top ),
% 3.01/0.95      inference(superposition,[status(thm)],[c_2378,c_2782]) ).
% 3.01/0.95  
% 3.01/0.95  cnf(c_6201,plain,
% 3.01/0.95      ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) = iProver_top ),
% 3.01/0.95      inference(demodulation,[status(thm)],[c_6179,c_2789]) ).
% 3.01/0.95  
% 3.01/0.95  cnf(c_16,negated_conjecture,
% 3.01/0.95      ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
% 3.01/0.95      inference(cnf_transformation,[],[f52]) ).
% 3.01/0.95  
% 3.01/0.95  cnf(c_21,plain,
% 3.01/0.95      ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) != iProver_top ),
% 3.01/0.95      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.01/0.95  
% 3.01/0.95  cnf(contradiction,plain,
% 3.01/0.95      ( $false ),
% 3.01/0.95      inference(minisat,[status(thm)],[c_6201,c_21]) ).
% 3.01/0.95  
% 3.01/0.95  
% 3.01/0.95  % SZS output end CNFRefutation for theBenchmark.p
% 3.01/0.95  
% 3.01/0.95  ------                               Statistics
% 3.01/0.95  
% 3.01/0.95  ------ General
% 3.01/0.95  
% 3.01/0.95  abstr_ref_over_cycles:                  0
% 3.01/0.95  abstr_ref_under_cycles:                 0
% 3.01/0.95  gc_basic_clause_elim:                   0
% 3.01/0.95  forced_gc_time:                         0
% 3.01/0.95  parsing_time:                           0.011
% 3.01/0.95  unif_index_cands_time:                  0.
% 3.01/0.95  unif_index_add_time:                    0.
% 3.01/0.95  orderings_time:                         0.
% 3.01/0.95  out_proof_time:                         0.009
% 3.01/0.95  total_time:                             0.201
% 3.01/0.95  num_of_symbols:                         45
% 3.01/0.95  num_of_terms:                           4942
% 3.01/0.95  
% 3.01/0.95  ------ Preprocessing
% 3.01/0.95  
% 3.01/0.95  num_of_splits:                          0
% 3.01/0.95  num_of_split_atoms:                     0
% 3.01/0.95  num_of_reused_defs:                     0
% 3.01/0.95  num_eq_ax_congr_red:                    12
% 3.01/0.95  num_of_sem_filtered_clauses:            1
% 3.01/0.95  num_of_subtypes:                        0
% 3.01/0.95  monotx_restored_types:                  0
% 3.01/0.95  sat_num_of_epr_types:                   0
% 3.01/0.95  sat_num_of_non_cyclic_types:            0
% 3.01/0.95  sat_guarded_non_collapsed_types:        0
% 3.01/0.95  num_pure_diseq_elim:                    0
% 3.01/0.95  simp_replaced_by:                       0
% 3.01/0.95  res_preprocessed:                       80
% 3.01/0.95  prep_upred:                             0
% 3.01/0.95  prep_unflattend:                        2
% 3.01/0.95  smt_new_axioms:                         0
% 3.01/0.95  pred_elim_cands:                        2
% 3.01/0.95  pred_elim:                              0
% 3.01/0.95  pred_elim_cl:                           0
% 3.01/0.95  pred_elim_cycles:                       1
% 3.01/0.95  merged_defs:                            0
% 3.01/0.95  merged_defs_ncl:                        0
% 3.01/0.95  bin_hyper_res:                          0
% 3.01/0.95  prep_cycles:                            3
% 3.01/0.95  pred_elim_time:                         0.001
% 3.01/0.95  splitting_time:                         0.
% 3.01/0.95  sem_filter_time:                        0.
% 3.01/0.95  monotx_time:                            0.
% 3.01/0.95  subtype_inf_time:                       0.
% 3.01/0.95  
% 3.01/0.95  ------ Problem properties
% 3.01/0.95  
% 3.01/0.95  clauses:                                19
% 3.01/0.95  conjectures:                            3
% 3.01/0.95  epr:                                    1
% 3.01/0.95  horn:                                   19
% 3.01/0.95  ground:                                 3
% 3.01/0.95  unary:                                  7
% 3.01/0.95  binary:                                 9
% 3.01/0.95  lits:                                   34
% 3.01/0.95  lits_eq:                                12
% 3.01/0.95  fd_pure:                                0
% 3.01/0.95  fd_pseudo:                              0
% 3.01/0.95  fd_cond:                                0
% 3.01/0.95  fd_pseudo_cond:                         0
% 3.01/0.95  ac_symbols:                             0
% 3.01/0.95  
% 3.01/0.95  ------ Propositional Solver
% 3.01/0.95  
% 3.01/0.95  prop_solver_calls:                      24
% 3.01/0.95  prop_fast_solver_calls:                 440
% 3.01/0.95  smt_solver_calls:                       0
% 3.01/0.95  smt_fast_solver_calls:                  0
% 3.01/0.95  prop_num_of_clauses:                    2380
% 3.01/0.95  prop_preprocess_simplified:             5772
% 3.01/0.95  prop_fo_subsumed:                       6
% 3.01/0.95  prop_solver_time:                       0.
% 3.01/0.95  smt_solver_time:                        0.
% 3.01/0.95  smt_fast_solver_time:                   0.
% 3.01/0.95  prop_fast_solver_time:                  0.
% 3.01/0.95  prop_unsat_core_time:                   0.
% 3.01/0.95  
% 3.01/0.95  ------ QBF
% 3.01/0.95  
% 3.01/0.95  qbf_q_res:                              0
% 3.01/0.95  qbf_num_tautologies:                    0
% 3.01/0.95  qbf_prep_cycles:                        0
% 3.01/0.95  
% 3.01/0.95  ------ BMC1
% 3.01/0.95  
% 3.01/0.95  bmc1_current_bound:                     -1
% 3.01/0.95  bmc1_last_solved_bound:                 -1
% 3.01/0.95  bmc1_unsat_core_size:                   -1
% 3.01/0.95  bmc1_unsat_core_parents_size:           -1
% 3.01/0.95  bmc1_merge_next_fun:                    0
% 3.01/0.95  bmc1_unsat_core_clauses_time:           0.
% 3.01/0.95  
% 3.01/0.95  ------ Instantiation
% 3.01/0.95  
% 3.01/0.95  inst_num_of_clauses:                    874
% 3.01/0.95  inst_num_in_passive:                    204
% 3.01/0.95  inst_num_in_active:                     323
% 3.01/0.95  inst_num_in_unprocessed:                347
% 3.01/0.95  inst_num_of_loops:                      330
% 3.01/0.95  inst_num_of_learning_restarts:          0
% 3.01/0.95  inst_num_moves_active_passive:          4
% 3.01/0.95  inst_lit_activity:                      0
% 3.01/0.95  inst_lit_activity_moves:                0
% 3.01/0.95  inst_num_tautologies:                   0
% 3.01/0.95  inst_num_prop_implied:                  0
% 3.01/0.95  inst_num_existing_simplified:           0
% 3.01/0.95  inst_num_eq_res_simplified:             0
% 3.01/0.95  inst_num_child_elim:                    0
% 3.01/0.95  inst_num_of_dismatching_blockings:      458
% 3.01/0.95  inst_num_of_non_proper_insts:           788
% 3.01/0.95  inst_num_of_duplicates:                 0
% 3.01/0.95  inst_inst_num_from_inst_to_res:         0
% 3.01/0.95  inst_dismatching_checking_time:         0.
% 3.01/0.95  
% 3.01/0.95  ------ Resolution
% 3.01/0.95  
% 3.01/0.95  res_num_of_clauses:                     0
% 3.01/0.95  res_num_in_passive:                     0
% 3.01/0.95  res_num_in_active:                      0
% 3.01/0.95  res_num_of_loops:                       83
% 3.01/0.95  res_forward_subset_subsumed:            67
% 3.01/0.95  res_backward_subset_subsumed:           2
% 3.01/0.95  res_forward_subsumed:                   0
% 3.01/0.95  res_backward_subsumed:                  0
% 3.01/0.95  res_forward_subsumption_resolution:     0
% 3.01/0.95  res_backward_subsumption_resolution:    0
% 3.01/0.95  res_clause_to_clause_subsumption:       266
% 3.01/0.95  res_orphan_elimination:                 0
% 3.01/0.95  res_tautology_del:                      46
% 3.01/0.95  res_num_eq_res_simplified:              0
% 3.01/0.95  res_num_sel_changes:                    0
% 3.01/0.95  res_moves_from_active_to_pass:          0
% 3.01/0.95  
% 3.01/0.95  ------ Superposition
% 3.01/0.95  
% 3.01/0.95  sup_time_total:                         0.
% 3.01/0.95  sup_time_generating:                    0.
% 3.01/0.95  sup_time_sim_full:                      0.
% 3.01/0.95  sup_time_sim_immed:                     0.
% 3.01/0.95  
% 3.01/0.95  sup_num_of_clauses:                     120
% 3.01/0.95  sup_num_in_active:                      60
% 3.01/0.95  sup_num_in_passive:                     60
% 3.01/0.95  sup_num_of_loops:                       65
% 3.01/0.95  sup_fw_superposition:                   92
% 3.01/0.95  sup_bw_superposition:                   23
% 3.01/0.95  sup_immediate_simplified:               26
% 3.01/0.95  sup_given_eliminated:                   0
% 3.01/0.95  comparisons_done:                       0
% 3.01/0.95  comparisons_avoided:                    0
% 3.01/0.95  
% 3.01/0.95  ------ Simplifications
% 3.01/0.95  
% 3.01/0.95  
% 3.01/0.95  sim_fw_subset_subsumed:                 2
% 3.01/0.95  sim_bw_subset_subsumed:                 0
% 3.01/0.95  sim_fw_subsumed:                        0
% 3.01/0.95  sim_bw_subsumed:                        0
% 3.01/0.95  sim_fw_subsumption_res:                 0
% 3.01/0.95  sim_bw_subsumption_res:                 0
% 3.01/0.95  sim_tautology_del:                      0
% 3.01/0.95  sim_eq_tautology_del:                   8
% 3.01/0.95  sim_eq_res_simp:                        0
% 3.01/0.95  sim_fw_demodulated:                     3
% 3.01/0.95  sim_bw_demodulated:                     5
% 3.01/0.95  sim_light_normalised:                   22
% 3.01/0.95  sim_joinable_taut:                      0
% 3.01/0.95  sim_joinable_simp:                      0
% 3.01/0.95  sim_ac_normalised:                      0
% 3.01/0.95  sim_smt_subsumption:                    0
% 3.01/0.95  
%------------------------------------------------------------------------------
