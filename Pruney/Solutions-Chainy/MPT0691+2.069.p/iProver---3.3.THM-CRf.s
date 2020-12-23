%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:51:50 EST 2020

% Result     : Theorem 27.38s
% Output     : CNFRefutation 27.38s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 233 expanded)
%              Number of clauses        :   58 (  93 expanded)
%              Number of leaves         :   13 (  43 expanded)
%              Depth                    :   19
%              Number of atoms          :  196 ( 529 expanded)
%              Number of equality atoms :   93 ( 138 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f37,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f38,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f41,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f38,f41])).

fof(f61,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f55,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0))
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f62,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f42])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f63,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_20,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_701,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_712,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_709,plain,
    ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1370,plain,
    ( k10_relat_1(k7_relat_1(X0,X1),k2_relat_1(k7_relat_1(X0,X1))) = k1_relat_1(k7_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_712,c_709])).

cnf(c_9338,plain,
    ( k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0))) = k1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_701,c_1370])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_711,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2303,plain,
    ( k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
    inference(superposition,[status(thm)],[c_701,c_711])).

cnf(c_9339,plain,
    ( k10_relat_1(k7_relat_1(sK1,X0),k9_relat_1(sK1,X0)) = k1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_9338,c_2303])).

cnf(c_17,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(k7_relat_1(X0,X1),X2) = k3_xboole_0(X1,k10_relat_1(X0,X2)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_704,plain,
    ( k10_relat_1(k7_relat_1(X0,X1),X2) = k3_xboole_0(X1,k10_relat_1(X0,X2))
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1269,plain,
    ( k10_relat_1(k7_relat_1(sK1,X0),X1) = k3_xboole_0(X0,k10_relat_1(sK1,X1)) ),
    inference(superposition,[status(thm)],[c_701,c_704])).

cnf(c_9966,plain,
    ( k3_xboole_0(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0))) = k1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_9339,c_1269])).

cnf(c_15,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_706,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_716,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1361,plain,
    ( k2_xboole_0(k7_relat_1(X0,X1),X0) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_706,c_716])).

cnf(c_6039,plain,
    ( k2_xboole_0(k7_relat_1(sK1,X0),sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_701,c_1361])).

cnf(c_7,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_714,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_6047,plain,
    ( r1_tarski(k7_relat_1(sK1,X0),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_6039,c_714])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k10_relat_1(X0,X2),k10_relat_1(X1,X2))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_707,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k10_relat_1(X0,X2),k10_relat_1(X1,X2)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3278,plain,
    ( k2_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X2,X1)) = k10_relat_1(X2,X1)
    | r1_tarski(X0,X2) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_707,c_716])).

cnf(c_50521,plain,
    ( k2_xboole_0(k10_relat_1(k7_relat_1(sK1,X0),X1),k10_relat_1(sK1,X1)) = k10_relat_1(sK1,X1)
    | v1_relat_1(k7_relat_1(sK1,X0)) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_6047,c_3278])).

cnf(c_50598,plain,
    ( k2_xboole_0(k3_xboole_0(X0,k10_relat_1(sK1,X1)),k10_relat_1(sK1,X1)) = k10_relat_1(sK1,X1)
    | v1_relat_1(k7_relat_1(sK1,X0)) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_50521,c_1269])).

cnf(c_21,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_51805,plain,
    ( v1_relat_1(k7_relat_1(sK1,X0)) != iProver_top
    | k2_xboole_0(k3_xboole_0(X0,k10_relat_1(sK1,X1)),k10_relat_1(sK1,X1)) = k10_relat_1(sK1,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_50598,c_21])).

cnf(c_51806,plain,
    ( k2_xboole_0(k3_xboole_0(X0,k10_relat_1(sK1,X1)),k10_relat_1(sK1,X1)) = k10_relat_1(sK1,X1)
    | v1_relat_1(k7_relat_1(sK1,X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_51805])).

cnf(c_51811,plain,
    ( k2_xboole_0(k3_xboole_0(X0,k10_relat_1(sK1,X1)),k10_relat_1(sK1,X1)) = k10_relat_1(sK1,X1)
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_712,c_51806])).

cnf(c_118002,plain,
    ( k2_xboole_0(k3_xboole_0(X0,k10_relat_1(sK1,X1)),k10_relat_1(sK1,X1)) = k10_relat_1(sK1,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_51811,c_21])).

cnf(c_118049,plain,
    ( r1_tarski(k3_xboole_0(X0,k10_relat_1(sK1,X1)),k10_relat_1(sK1,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_118002,c_714])).

cnf(c_118197,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k10_relat_1(sK1,k9_relat_1(sK1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_9966,c_118049])).

cnf(c_19,negated_conjecture,
    ( r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_702,plain,
    ( r1_tarski(sK0,k1_relat_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_715,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1176,plain,
    ( k3_xboole_0(sK0,k1_relat_1(sK1)) = sK0 ),
    inference(superposition,[status(thm)],[c_702,c_715])).

cnf(c_1371,plain,
    ( k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_701,c_709])).

cnf(c_11,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_710,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1639,plain,
    ( r1_tarski(k3_xboole_0(X0,k10_relat_1(sK1,X1)),k1_relat_1(k7_relat_1(sK1,X0))) = iProver_top
    | v1_relat_1(k7_relat_1(sK1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1269,c_710])).

cnf(c_1744,plain,
    ( r1_tarski(k3_xboole_0(X0,k1_relat_1(sK1)),k1_relat_1(k7_relat_1(sK1,X0))) = iProver_top
    | v1_relat_1(k7_relat_1(sK1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1371,c_1639])).

cnf(c_1757,plain,
    ( r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0))) = iProver_top
    | v1_relat_1(k7_relat_1(sK1,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1176,c_1744])).

cnf(c_1935,plain,
    ( k2_xboole_0(sK0,k1_relat_1(k7_relat_1(sK1,sK0))) = k1_relat_1(k7_relat_1(sK1,sK0))
    | v1_relat_1(k7_relat_1(sK1,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1757,c_716])).

cnf(c_2143,plain,
    ( k2_xboole_0(sK0,k1_relat_1(k7_relat_1(sK1,sK0))) = k1_relat_1(k7_relat_1(sK1,sK0))
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_712,c_1935])).

cnf(c_16515,plain,
    ( k2_xboole_0(sK0,k1_relat_1(k7_relat_1(sK1,sK0))) = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2143,c_21])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_717,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_16529,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),X0) != iProver_top
    | r1_tarski(sK0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_16515,c_717])).

cnf(c_118783,plain,
    ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_118197,c_16529])).

cnf(c_18,negated_conjecture,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_23,plain,
    ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_118783,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:21:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 27.38/4.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.38/4.02  
% 27.38/4.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.38/4.02  
% 27.38/4.02  ------  iProver source info
% 27.38/4.02  
% 27.38/4.02  git: date: 2020-06-30 10:37:57 +0100
% 27.38/4.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.38/4.02  git: non_committed_changes: false
% 27.38/4.02  git: last_make_outside_of_git: false
% 27.38/4.02  
% 27.38/4.02  ------ 
% 27.38/4.02  
% 27.38/4.02  ------ Input Options
% 27.38/4.02  
% 27.38/4.02  --out_options                           all
% 27.38/4.02  --tptp_safe_out                         true
% 27.38/4.02  --problem_path                          ""
% 27.38/4.02  --include_path                          ""
% 27.38/4.02  --clausifier                            res/vclausify_rel
% 27.38/4.02  --clausifier_options                    ""
% 27.38/4.02  --stdin                                 false
% 27.38/4.02  --stats_out                             all
% 27.38/4.02  
% 27.38/4.02  ------ General Options
% 27.38/4.02  
% 27.38/4.02  --fof                                   false
% 27.38/4.02  --time_out_real                         305.
% 27.38/4.02  --time_out_virtual                      -1.
% 27.38/4.02  --symbol_type_check                     false
% 27.38/4.02  --clausify_out                          false
% 27.38/4.02  --sig_cnt_out                           false
% 27.38/4.02  --trig_cnt_out                          false
% 27.38/4.02  --trig_cnt_out_tolerance                1.
% 27.38/4.02  --trig_cnt_out_sk_spl                   false
% 27.38/4.02  --abstr_cl_out                          false
% 27.38/4.02  
% 27.38/4.02  ------ Global Options
% 27.38/4.02  
% 27.38/4.02  --schedule                              default
% 27.38/4.02  --add_important_lit                     false
% 27.38/4.02  --prop_solver_per_cl                    1000
% 27.38/4.02  --min_unsat_core                        false
% 27.38/4.02  --soft_assumptions                      false
% 27.38/4.02  --soft_lemma_size                       3
% 27.38/4.02  --prop_impl_unit_size                   0
% 27.38/4.02  --prop_impl_unit                        []
% 27.38/4.02  --share_sel_clauses                     true
% 27.38/4.02  --reset_solvers                         false
% 27.38/4.02  --bc_imp_inh                            [conj_cone]
% 27.38/4.02  --conj_cone_tolerance                   3.
% 27.38/4.02  --extra_neg_conj                        none
% 27.38/4.02  --large_theory_mode                     true
% 27.38/4.02  --prolific_symb_bound                   200
% 27.38/4.02  --lt_threshold                          2000
% 27.38/4.02  --clause_weak_htbl                      true
% 27.38/4.02  --gc_record_bc_elim                     false
% 27.38/4.02  
% 27.38/4.02  ------ Preprocessing Options
% 27.38/4.02  
% 27.38/4.02  --preprocessing_flag                    true
% 27.38/4.02  --time_out_prep_mult                    0.1
% 27.38/4.02  --splitting_mode                        input
% 27.38/4.02  --splitting_grd                         true
% 27.38/4.02  --splitting_cvd                         false
% 27.38/4.02  --splitting_cvd_svl                     false
% 27.38/4.02  --splitting_nvd                         32
% 27.38/4.02  --sub_typing                            true
% 27.38/4.02  --prep_gs_sim                           true
% 27.38/4.02  --prep_unflatten                        true
% 27.38/4.02  --prep_res_sim                          true
% 27.38/4.02  --prep_upred                            true
% 27.38/4.02  --prep_sem_filter                       exhaustive
% 27.38/4.02  --prep_sem_filter_out                   false
% 27.38/4.02  --pred_elim                             true
% 27.38/4.02  --res_sim_input                         true
% 27.38/4.02  --eq_ax_congr_red                       true
% 27.38/4.02  --pure_diseq_elim                       true
% 27.38/4.02  --brand_transform                       false
% 27.38/4.02  --non_eq_to_eq                          false
% 27.38/4.02  --prep_def_merge                        true
% 27.38/4.02  --prep_def_merge_prop_impl              false
% 27.38/4.02  --prep_def_merge_mbd                    true
% 27.38/4.02  --prep_def_merge_tr_red                 false
% 27.38/4.02  --prep_def_merge_tr_cl                  false
% 27.38/4.02  --smt_preprocessing                     true
% 27.38/4.02  --smt_ac_axioms                         fast
% 27.38/4.02  --preprocessed_out                      false
% 27.38/4.02  --preprocessed_stats                    false
% 27.38/4.02  
% 27.38/4.02  ------ Abstraction refinement Options
% 27.38/4.02  
% 27.38/4.02  --abstr_ref                             []
% 27.38/4.02  --abstr_ref_prep                        false
% 27.38/4.02  --abstr_ref_until_sat                   false
% 27.38/4.02  --abstr_ref_sig_restrict                funpre
% 27.38/4.02  --abstr_ref_af_restrict_to_split_sk     false
% 27.38/4.02  --abstr_ref_under                       []
% 27.38/4.02  
% 27.38/4.02  ------ SAT Options
% 27.38/4.02  
% 27.38/4.02  --sat_mode                              false
% 27.38/4.02  --sat_fm_restart_options                ""
% 27.38/4.02  --sat_gr_def                            false
% 27.38/4.02  --sat_epr_types                         true
% 27.38/4.02  --sat_non_cyclic_types                  false
% 27.38/4.02  --sat_finite_models                     false
% 27.38/4.02  --sat_fm_lemmas                         false
% 27.38/4.02  --sat_fm_prep                           false
% 27.38/4.02  --sat_fm_uc_incr                        true
% 27.38/4.02  --sat_out_model                         small
% 27.38/4.02  --sat_out_clauses                       false
% 27.38/4.02  
% 27.38/4.02  ------ QBF Options
% 27.38/4.02  
% 27.38/4.02  --qbf_mode                              false
% 27.38/4.02  --qbf_elim_univ                         false
% 27.38/4.02  --qbf_dom_inst                          none
% 27.38/4.02  --qbf_dom_pre_inst                      false
% 27.38/4.02  --qbf_sk_in                             false
% 27.38/4.02  --qbf_pred_elim                         true
% 27.38/4.02  --qbf_split                             512
% 27.38/4.02  
% 27.38/4.02  ------ BMC1 Options
% 27.38/4.02  
% 27.38/4.02  --bmc1_incremental                      false
% 27.38/4.02  --bmc1_axioms                           reachable_all
% 27.38/4.02  --bmc1_min_bound                        0
% 27.38/4.02  --bmc1_max_bound                        -1
% 27.38/4.02  --bmc1_max_bound_default                -1
% 27.38/4.02  --bmc1_symbol_reachability              true
% 27.38/4.02  --bmc1_property_lemmas                  false
% 27.38/4.02  --bmc1_k_induction                      false
% 27.38/4.02  --bmc1_non_equiv_states                 false
% 27.38/4.02  --bmc1_deadlock                         false
% 27.38/4.02  --bmc1_ucm                              false
% 27.38/4.02  --bmc1_add_unsat_core                   none
% 27.38/4.02  --bmc1_unsat_core_children              false
% 27.38/4.02  --bmc1_unsat_core_extrapolate_axioms    false
% 27.38/4.02  --bmc1_out_stat                         full
% 27.38/4.02  --bmc1_ground_init                      false
% 27.38/4.02  --bmc1_pre_inst_next_state              false
% 27.38/4.02  --bmc1_pre_inst_state                   false
% 27.38/4.02  --bmc1_pre_inst_reach_state             false
% 27.38/4.02  --bmc1_out_unsat_core                   false
% 27.38/4.02  --bmc1_aig_witness_out                  false
% 27.38/4.02  --bmc1_verbose                          false
% 27.38/4.02  --bmc1_dump_clauses_tptp                false
% 27.38/4.02  --bmc1_dump_unsat_core_tptp             false
% 27.38/4.02  --bmc1_dump_file                        -
% 27.38/4.02  --bmc1_ucm_expand_uc_limit              128
% 27.38/4.02  --bmc1_ucm_n_expand_iterations          6
% 27.38/4.02  --bmc1_ucm_extend_mode                  1
% 27.38/4.02  --bmc1_ucm_init_mode                    2
% 27.38/4.02  --bmc1_ucm_cone_mode                    none
% 27.38/4.02  --bmc1_ucm_reduced_relation_type        0
% 27.38/4.02  --bmc1_ucm_relax_model                  4
% 27.38/4.02  --bmc1_ucm_full_tr_after_sat            true
% 27.38/4.02  --bmc1_ucm_expand_neg_assumptions       false
% 27.38/4.02  --bmc1_ucm_layered_model                none
% 27.38/4.02  --bmc1_ucm_max_lemma_size               10
% 27.38/4.02  
% 27.38/4.02  ------ AIG Options
% 27.38/4.02  
% 27.38/4.02  --aig_mode                              false
% 27.38/4.02  
% 27.38/4.02  ------ Instantiation Options
% 27.38/4.02  
% 27.38/4.02  --instantiation_flag                    true
% 27.38/4.02  --inst_sos_flag                         true
% 27.38/4.02  --inst_sos_phase                        true
% 27.38/4.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.38/4.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.38/4.02  --inst_lit_sel_side                     num_symb
% 27.38/4.02  --inst_solver_per_active                1400
% 27.38/4.02  --inst_solver_calls_frac                1.
% 27.38/4.02  --inst_passive_queue_type               priority_queues
% 27.38/4.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.38/4.02  --inst_passive_queues_freq              [25;2]
% 27.38/4.02  --inst_dismatching                      true
% 27.38/4.02  --inst_eager_unprocessed_to_passive     true
% 27.38/4.02  --inst_prop_sim_given                   true
% 27.38/4.02  --inst_prop_sim_new                     false
% 27.38/4.02  --inst_subs_new                         false
% 27.38/4.02  --inst_eq_res_simp                      false
% 27.38/4.02  --inst_subs_given                       false
% 27.38/4.02  --inst_orphan_elimination               true
% 27.38/4.02  --inst_learning_loop_flag               true
% 27.38/4.02  --inst_learning_start                   3000
% 27.38/4.02  --inst_learning_factor                  2
% 27.38/4.02  --inst_start_prop_sim_after_learn       3
% 27.38/4.02  --inst_sel_renew                        solver
% 27.38/4.02  --inst_lit_activity_flag                true
% 27.38/4.02  --inst_restr_to_given                   false
% 27.38/4.02  --inst_activity_threshold               500
% 27.38/4.02  --inst_out_proof                        true
% 27.38/4.02  
% 27.38/4.02  ------ Resolution Options
% 27.38/4.02  
% 27.38/4.02  --resolution_flag                       true
% 27.38/4.02  --res_lit_sel                           adaptive
% 27.38/4.02  --res_lit_sel_side                      none
% 27.38/4.02  --res_ordering                          kbo
% 27.38/4.02  --res_to_prop_solver                    active
% 27.38/4.02  --res_prop_simpl_new                    false
% 27.38/4.02  --res_prop_simpl_given                  true
% 27.38/4.02  --res_passive_queue_type                priority_queues
% 27.38/4.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.38/4.02  --res_passive_queues_freq               [15;5]
% 27.38/4.02  --res_forward_subs                      full
% 27.38/4.02  --res_backward_subs                     full
% 27.38/4.02  --res_forward_subs_resolution           true
% 27.38/4.02  --res_backward_subs_resolution          true
% 27.38/4.02  --res_orphan_elimination                true
% 27.38/4.02  --res_time_limit                        2.
% 27.38/4.02  --res_out_proof                         true
% 27.38/4.02  
% 27.38/4.02  ------ Superposition Options
% 27.38/4.02  
% 27.38/4.02  --superposition_flag                    true
% 27.38/4.02  --sup_passive_queue_type                priority_queues
% 27.38/4.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.38/4.02  --sup_passive_queues_freq               [8;1;4]
% 27.38/4.02  --demod_completeness_check              fast
% 27.38/4.02  --demod_use_ground                      true
% 27.38/4.02  --sup_to_prop_solver                    passive
% 27.38/4.02  --sup_prop_simpl_new                    true
% 27.38/4.02  --sup_prop_simpl_given                  true
% 27.38/4.02  --sup_fun_splitting                     true
% 27.38/4.02  --sup_smt_interval                      50000
% 27.38/4.02  
% 27.38/4.02  ------ Superposition Simplification Setup
% 27.38/4.02  
% 27.38/4.02  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 27.38/4.02  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 27.38/4.02  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 27.38/4.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 27.38/4.02  --sup_full_triv                         [TrivRules;PropSubs]
% 27.38/4.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 27.38/4.02  --sup_full_bw                           [BwDemod;BwSubsumption]
% 27.38/4.02  --sup_immed_triv                        [TrivRules]
% 27.38/4.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.38/4.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.38/4.02  --sup_immed_bw_main                     []
% 27.38/4.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 27.38/4.02  --sup_input_triv                        [Unflattening;TrivRules]
% 27.38/4.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.38/4.02  --sup_input_bw                          []
% 27.38/4.02  
% 27.38/4.02  ------ Combination Options
% 27.38/4.02  
% 27.38/4.02  --comb_res_mult                         3
% 27.38/4.02  --comb_sup_mult                         2
% 27.38/4.02  --comb_inst_mult                        10
% 27.38/4.02  
% 27.38/4.02  ------ Debug Options
% 27.38/4.02  
% 27.38/4.02  --dbg_backtrace                         false
% 27.38/4.02  --dbg_dump_prop_clauses                 false
% 27.38/4.02  --dbg_dump_prop_clauses_file            -
% 27.38/4.02  --dbg_out_stat                          false
% 27.38/4.02  ------ Parsing...
% 27.38/4.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.38/4.02  
% 27.38/4.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 27.38/4.02  
% 27.38/4.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.38/4.02  
% 27.38/4.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.38/4.02  ------ Proving...
% 27.38/4.02  ------ Problem Properties 
% 27.38/4.02  
% 27.38/4.02  
% 27.38/4.02  clauses                                 20
% 27.38/4.02  conjectures                             3
% 27.38/4.02  EPR                                     3
% 27.38/4.02  Horn                                    20
% 27.38/4.02  unary                                   5
% 27.38/4.02  binary                                  10
% 27.38/4.02  lits                                    41
% 27.38/4.02  lits eq                                 7
% 27.38/4.02  fd_pure                                 0
% 27.38/4.02  fd_pseudo                               0
% 27.38/4.02  fd_cond                                 0
% 27.38/4.02  fd_pseudo_cond                          1
% 27.38/4.02  AC symbols                              0
% 27.38/4.02  
% 27.38/4.02  ------ Schedule dynamic 5 is on 
% 27.38/4.02  
% 27.38/4.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 27.38/4.02  
% 27.38/4.02  
% 27.38/4.02  ------ 
% 27.38/4.02  Current options:
% 27.38/4.02  ------ 
% 27.38/4.02  
% 27.38/4.02  ------ Input Options
% 27.38/4.02  
% 27.38/4.02  --out_options                           all
% 27.38/4.02  --tptp_safe_out                         true
% 27.38/4.02  --problem_path                          ""
% 27.38/4.02  --include_path                          ""
% 27.38/4.02  --clausifier                            res/vclausify_rel
% 27.38/4.02  --clausifier_options                    ""
% 27.38/4.02  --stdin                                 false
% 27.38/4.02  --stats_out                             all
% 27.38/4.02  
% 27.38/4.02  ------ General Options
% 27.38/4.02  
% 27.38/4.02  --fof                                   false
% 27.38/4.02  --time_out_real                         305.
% 27.38/4.02  --time_out_virtual                      -1.
% 27.38/4.02  --symbol_type_check                     false
% 27.38/4.02  --clausify_out                          false
% 27.38/4.02  --sig_cnt_out                           false
% 27.38/4.02  --trig_cnt_out                          false
% 27.38/4.02  --trig_cnt_out_tolerance                1.
% 27.38/4.02  --trig_cnt_out_sk_spl                   false
% 27.38/4.02  --abstr_cl_out                          false
% 27.38/4.02  
% 27.38/4.02  ------ Global Options
% 27.38/4.02  
% 27.38/4.02  --schedule                              default
% 27.38/4.02  --add_important_lit                     false
% 27.38/4.02  --prop_solver_per_cl                    1000
% 27.38/4.02  --min_unsat_core                        false
% 27.38/4.02  --soft_assumptions                      false
% 27.38/4.02  --soft_lemma_size                       3
% 27.38/4.02  --prop_impl_unit_size                   0
% 27.38/4.02  --prop_impl_unit                        []
% 27.38/4.02  --share_sel_clauses                     true
% 27.38/4.02  --reset_solvers                         false
% 27.38/4.02  --bc_imp_inh                            [conj_cone]
% 27.38/4.02  --conj_cone_tolerance                   3.
% 27.38/4.02  --extra_neg_conj                        none
% 27.38/4.02  --large_theory_mode                     true
% 27.38/4.02  --prolific_symb_bound                   200
% 27.38/4.02  --lt_threshold                          2000
% 27.38/4.02  --clause_weak_htbl                      true
% 27.38/4.02  --gc_record_bc_elim                     false
% 27.38/4.02  
% 27.38/4.02  ------ Preprocessing Options
% 27.38/4.02  
% 27.38/4.02  --preprocessing_flag                    true
% 27.38/4.02  --time_out_prep_mult                    0.1
% 27.38/4.02  --splitting_mode                        input
% 27.38/4.02  --splitting_grd                         true
% 27.38/4.02  --splitting_cvd                         false
% 27.38/4.02  --splitting_cvd_svl                     false
% 27.38/4.02  --splitting_nvd                         32
% 27.38/4.02  --sub_typing                            true
% 27.38/4.02  --prep_gs_sim                           true
% 27.38/4.02  --prep_unflatten                        true
% 27.38/4.02  --prep_res_sim                          true
% 27.38/4.02  --prep_upred                            true
% 27.38/4.02  --prep_sem_filter                       exhaustive
% 27.38/4.02  --prep_sem_filter_out                   false
% 27.38/4.02  --pred_elim                             true
% 27.38/4.02  --res_sim_input                         true
% 27.38/4.02  --eq_ax_congr_red                       true
% 27.38/4.02  --pure_diseq_elim                       true
% 27.38/4.02  --brand_transform                       false
% 27.38/4.02  --non_eq_to_eq                          false
% 27.38/4.02  --prep_def_merge                        true
% 27.38/4.02  --prep_def_merge_prop_impl              false
% 27.38/4.02  --prep_def_merge_mbd                    true
% 27.38/4.02  --prep_def_merge_tr_red                 false
% 27.38/4.02  --prep_def_merge_tr_cl                  false
% 27.38/4.02  --smt_preprocessing                     true
% 27.38/4.02  --smt_ac_axioms                         fast
% 27.38/4.02  --preprocessed_out                      false
% 27.38/4.02  --preprocessed_stats                    false
% 27.38/4.02  
% 27.38/4.02  ------ Abstraction refinement Options
% 27.38/4.02  
% 27.38/4.02  --abstr_ref                             []
% 27.38/4.02  --abstr_ref_prep                        false
% 27.38/4.02  --abstr_ref_until_sat                   false
% 27.38/4.02  --abstr_ref_sig_restrict                funpre
% 27.38/4.02  --abstr_ref_af_restrict_to_split_sk     false
% 27.38/4.02  --abstr_ref_under                       []
% 27.38/4.02  
% 27.38/4.02  ------ SAT Options
% 27.38/4.02  
% 27.38/4.02  --sat_mode                              false
% 27.38/4.02  --sat_fm_restart_options                ""
% 27.38/4.02  --sat_gr_def                            false
% 27.38/4.02  --sat_epr_types                         true
% 27.38/4.02  --sat_non_cyclic_types                  false
% 27.38/4.02  --sat_finite_models                     false
% 27.38/4.02  --sat_fm_lemmas                         false
% 27.38/4.02  --sat_fm_prep                           false
% 27.38/4.02  --sat_fm_uc_incr                        true
% 27.38/4.02  --sat_out_model                         small
% 27.38/4.02  --sat_out_clauses                       false
% 27.38/4.02  
% 27.38/4.02  ------ QBF Options
% 27.38/4.02  
% 27.38/4.02  --qbf_mode                              false
% 27.38/4.02  --qbf_elim_univ                         false
% 27.38/4.02  --qbf_dom_inst                          none
% 27.38/4.02  --qbf_dom_pre_inst                      false
% 27.38/4.02  --qbf_sk_in                             false
% 27.38/4.02  --qbf_pred_elim                         true
% 27.38/4.02  --qbf_split                             512
% 27.38/4.02  
% 27.38/4.02  ------ BMC1 Options
% 27.38/4.02  
% 27.38/4.02  --bmc1_incremental                      false
% 27.38/4.02  --bmc1_axioms                           reachable_all
% 27.38/4.02  --bmc1_min_bound                        0
% 27.38/4.02  --bmc1_max_bound                        -1
% 27.38/4.02  --bmc1_max_bound_default                -1
% 27.38/4.02  --bmc1_symbol_reachability              true
% 27.38/4.02  --bmc1_property_lemmas                  false
% 27.38/4.02  --bmc1_k_induction                      false
% 27.38/4.02  --bmc1_non_equiv_states                 false
% 27.38/4.02  --bmc1_deadlock                         false
% 27.38/4.02  --bmc1_ucm                              false
% 27.38/4.02  --bmc1_add_unsat_core                   none
% 27.38/4.02  --bmc1_unsat_core_children              false
% 27.38/4.02  --bmc1_unsat_core_extrapolate_axioms    false
% 27.38/4.02  --bmc1_out_stat                         full
% 27.38/4.02  --bmc1_ground_init                      false
% 27.38/4.02  --bmc1_pre_inst_next_state              false
% 27.38/4.02  --bmc1_pre_inst_state                   false
% 27.38/4.02  --bmc1_pre_inst_reach_state             false
% 27.38/4.02  --bmc1_out_unsat_core                   false
% 27.38/4.02  --bmc1_aig_witness_out                  false
% 27.38/4.02  --bmc1_verbose                          false
% 27.38/4.02  --bmc1_dump_clauses_tptp                false
% 27.38/4.02  --bmc1_dump_unsat_core_tptp             false
% 27.38/4.02  --bmc1_dump_file                        -
% 27.38/4.02  --bmc1_ucm_expand_uc_limit              128
% 27.38/4.02  --bmc1_ucm_n_expand_iterations          6
% 27.38/4.02  --bmc1_ucm_extend_mode                  1
% 27.38/4.02  --bmc1_ucm_init_mode                    2
% 27.38/4.02  --bmc1_ucm_cone_mode                    none
% 27.38/4.02  --bmc1_ucm_reduced_relation_type        0
% 27.38/4.02  --bmc1_ucm_relax_model                  4
% 27.38/4.02  --bmc1_ucm_full_tr_after_sat            true
% 27.38/4.02  --bmc1_ucm_expand_neg_assumptions       false
% 27.38/4.02  --bmc1_ucm_layered_model                none
% 27.38/4.02  --bmc1_ucm_max_lemma_size               10
% 27.38/4.02  
% 27.38/4.02  ------ AIG Options
% 27.38/4.02  
% 27.38/4.02  --aig_mode                              false
% 27.38/4.02  
% 27.38/4.02  ------ Instantiation Options
% 27.38/4.02  
% 27.38/4.02  --instantiation_flag                    true
% 27.38/4.02  --inst_sos_flag                         true
% 27.38/4.02  --inst_sos_phase                        true
% 27.38/4.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.38/4.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.38/4.02  --inst_lit_sel_side                     none
% 27.38/4.02  --inst_solver_per_active                1400
% 27.38/4.02  --inst_solver_calls_frac                1.
% 27.38/4.02  --inst_passive_queue_type               priority_queues
% 27.38/4.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.38/4.02  --inst_passive_queues_freq              [25;2]
% 27.38/4.02  --inst_dismatching                      true
% 27.38/4.02  --inst_eager_unprocessed_to_passive     true
% 27.38/4.02  --inst_prop_sim_given                   true
% 27.38/4.02  --inst_prop_sim_new                     false
% 27.38/4.02  --inst_subs_new                         false
% 27.38/4.02  --inst_eq_res_simp                      false
% 27.38/4.02  --inst_subs_given                       false
% 27.38/4.02  --inst_orphan_elimination               true
% 27.38/4.02  --inst_learning_loop_flag               true
% 27.38/4.02  --inst_learning_start                   3000
% 27.38/4.02  --inst_learning_factor                  2
% 27.38/4.02  --inst_start_prop_sim_after_learn       3
% 27.38/4.02  --inst_sel_renew                        solver
% 27.38/4.02  --inst_lit_activity_flag                true
% 27.38/4.02  --inst_restr_to_given                   false
% 27.38/4.02  --inst_activity_threshold               500
% 27.38/4.02  --inst_out_proof                        true
% 27.38/4.02  
% 27.38/4.02  ------ Resolution Options
% 27.38/4.02  
% 27.38/4.02  --resolution_flag                       false
% 27.38/4.02  --res_lit_sel                           adaptive
% 27.38/4.02  --res_lit_sel_side                      none
% 27.38/4.02  --res_ordering                          kbo
% 27.38/4.02  --res_to_prop_solver                    active
% 27.38/4.02  --res_prop_simpl_new                    false
% 27.38/4.02  --res_prop_simpl_given                  true
% 27.38/4.02  --res_passive_queue_type                priority_queues
% 27.38/4.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.38/4.02  --res_passive_queues_freq               [15;5]
% 27.38/4.02  --res_forward_subs                      full
% 27.38/4.02  --res_backward_subs                     full
% 27.38/4.02  --res_forward_subs_resolution           true
% 27.38/4.02  --res_backward_subs_resolution          true
% 27.38/4.02  --res_orphan_elimination                true
% 27.38/4.02  --res_time_limit                        2.
% 27.38/4.02  --res_out_proof                         true
% 27.38/4.02  
% 27.38/4.02  ------ Superposition Options
% 27.38/4.02  
% 27.38/4.02  --superposition_flag                    true
% 27.38/4.02  --sup_passive_queue_type                priority_queues
% 27.38/4.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.38/4.02  --sup_passive_queues_freq               [8;1;4]
% 27.38/4.02  --demod_completeness_check              fast
% 27.38/4.02  --demod_use_ground                      true
% 27.38/4.02  --sup_to_prop_solver                    passive
% 27.38/4.02  --sup_prop_simpl_new                    true
% 27.38/4.02  --sup_prop_simpl_given                  true
% 27.38/4.02  --sup_fun_splitting                     true
% 27.38/4.02  --sup_smt_interval                      50000
% 27.38/4.02  
% 27.38/4.02  ------ Superposition Simplification Setup
% 27.38/4.02  
% 27.38/4.02  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 27.38/4.02  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 27.38/4.02  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 27.38/4.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 27.38/4.02  --sup_full_triv                         [TrivRules;PropSubs]
% 27.38/4.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 27.38/4.02  --sup_full_bw                           [BwDemod;BwSubsumption]
% 27.38/4.02  --sup_immed_triv                        [TrivRules]
% 27.38/4.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.38/4.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.38/4.02  --sup_immed_bw_main                     []
% 27.38/4.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 27.38/4.02  --sup_input_triv                        [Unflattening;TrivRules]
% 27.38/4.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.38/4.02  --sup_input_bw                          []
% 27.38/4.02  
% 27.38/4.02  ------ Combination Options
% 27.38/4.02  
% 27.38/4.02  --comb_res_mult                         3
% 27.38/4.02  --comb_sup_mult                         2
% 27.38/4.02  --comb_inst_mult                        10
% 27.38/4.02  
% 27.38/4.02  ------ Debug Options
% 27.38/4.02  
% 27.38/4.02  --dbg_backtrace                         false
% 27.38/4.02  --dbg_dump_prop_clauses                 false
% 27.38/4.02  --dbg_dump_prop_clauses_file            -
% 27.38/4.02  --dbg_out_stat                          false
% 27.38/4.02  
% 27.38/4.02  
% 27.38/4.02  
% 27.38/4.02  
% 27.38/4.02  ------ Proving...
% 27.38/4.02  
% 27.38/4.02  
% 27.38/4.02  % SZS status Theorem for theBenchmark.p
% 27.38/4.02  
% 27.38/4.02  % SZS output start CNFRefutation for theBenchmark.p
% 27.38/4.02  
% 27.38/4.02  fof(f17,conjecture,(
% 27.38/4.02    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 27.38/4.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.38/4.02  
% 27.38/4.02  fof(f18,negated_conjecture,(
% 27.38/4.02    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 27.38/4.02    inference(negated_conjecture,[],[f17])).
% 27.38/4.02  
% 27.38/4.02  fof(f37,plain,(
% 27.38/4.02    ? [X0,X1] : ((~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 27.38/4.02    inference(ennf_transformation,[],[f18])).
% 27.38/4.02  
% 27.38/4.02  fof(f38,plain,(
% 27.38/4.02    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 27.38/4.02    inference(flattening,[],[f37])).
% 27.38/4.02  
% 27.38/4.02  fof(f41,plain,(
% 27.38/4.02    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 27.38/4.02    introduced(choice_axiom,[])).
% 27.38/4.02  
% 27.38/4.02  fof(f42,plain,(
% 27.38/4.02    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1)),
% 27.38/4.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f38,f41])).
% 27.38/4.02  
% 27.38/4.02  fof(f61,plain,(
% 27.38/4.02    v1_relat_1(sK1)),
% 27.38/4.02    inference(cnf_transformation,[],[f42])).
% 27.38/4.02  
% 27.38/4.02  fof(f8,axiom,(
% 27.38/4.02    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 27.38/4.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.38/4.02  
% 27.38/4.02  fof(f25,plain,(
% 27.38/4.02    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 27.38/4.02    inference(ennf_transformation,[],[f8])).
% 27.38/4.02  
% 27.38/4.02  fof(f52,plain,(
% 27.38/4.02    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 27.38/4.02    inference(cnf_transformation,[],[f25])).
% 27.38/4.02  
% 27.38/4.02  fof(f11,axiom,(
% 27.38/4.02    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 27.38/4.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.38/4.02  
% 27.38/4.02  fof(f28,plain,(
% 27.38/4.02    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 27.38/4.02    inference(ennf_transformation,[],[f11])).
% 27.38/4.02  
% 27.38/4.02  fof(f55,plain,(
% 27.38/4.02    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 27.38/4.02    inference(cnf_transformation,[],[f28])).
% 27.38/4.02  
% 27.38/4.02  fof(f9,axiom,(
% 27.38/4.02    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 27.38/4.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.38/4.02  
% 27.38/4.02  fof(f26,plain,(
% 27.38/4.02    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 27.38/4.02    inference(ennf_transformation,[],[f9])).
% 27.38/4.02  
% 27.38/4.02  fof(f53,plain,(
% 27.38/4.02    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 27.38/4.02    inference(cnf_transformation,[],[f26])).
% 27.38/4.02  
% 27.38/4.02  fof(f16,axiom,(
% 27.38/4.02    ! [X0,X1,X2] : (v1_relat_1(X2) => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1))),
% 27.38/4.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.38/4.02  
% 27.38/4.02  fof(f36,plain,(
% 27.38/4.02    ! [X0,X1,X2] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 27.38/4.02    inference(ennf_transformation,[],[f16])).
% 27.38/4.02  
% 27.38/4.02  fof(f60,plain,(
% 27.38/4.02    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 27.38/4.02    inference(cnf_transformation,[],[f36])).
% 27.38/4.02  
% 27.38/4.02  fof(f14,axiom,(
% 27.38/4.02    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 27.38/4.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.38/4.02  
% 27.38/4.02  fof(f33,plain,(
% 27.38/4.02    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 27.38/4.02    inference(ennf_transformation,[],[f14])).
% 27.38/4.02  
% 27.38/4.02  fof(f58,plain,(
% 27.38/4.02    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 27.38/4.02    inference(cnf_transformation,[],[f33])).
% 27.38/4.02  
% 27.38/4.02  fof(f4,axiom,(
% 27.38/4.02    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 27.38/4.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.38/4.02  
% 27.38/4.02  fof(f21,plain,(
% 27.38/4.02    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 27.38/4.02    inference(ennf_transformation,[],[f4])).
% 27.38/4.02  
% 27.38/4.02  fof(f48,plain,(
% 27.38/4.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 27.38/4.02    inference(cnf_transformation,[],[f21])).
% 27.38/4.02  
% 27.38/4.02  fof(f6,axiom,(
% 27.38/4.02    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 27.38/4.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.38/4.02  
% 27.38/4.02  fof(f50,plain,(
% 27.38/4.02    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 27.38/4.02    inference(cnf_transformation,[],[f6])).
% 27.38/4.02  
% 27.38/4.02  fof(f13,axiom,(
% 27.38/4.02    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)))))),
% 27.38/4.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.38/4.02  
% 27.38/4.02  fof(f31,plain,(
% 27.38/4.02    ! [X0,X1] : (! [X2] : ((r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 27.38/4.02    inference(ennf_transformation,[],[f13])).
% 27.38/4.02  
% 27.38/4.02  fof(f32,plain,(
% 27.38/4.02    ! [X0,X1] : (! [X2] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 27.38/4.02    inference(flattening,[],[f31])).
% 27.38/4.02  
% 27.38/4.02  fof(f57,plain,(
% 27.38/4.02    ( ! [X2,X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 27.38/4.02    inference(cnf_transformation,[],[f32])).
% 27.38/4.02  
% 27.38/4.02  fof(f62,plain,(
% 27.38/4.02    r1_tarski(sK0,k1_relat_1(sK1))),
% 27.38/4.02    inference(cnf_transformation,[],[f42])).
% 27.38/4.02  
% 27.38/4.02  fof(f5,axiom,(
% 27.38/4.02    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 27.38/4.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.38/4.02  
% 27.38/4.02  fof(f22,plain,(
% 27.38/4.02    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 27.38/4.02    inference(ennf_transformation,[],[f5])).
% 27.38/4.02  
% 27.38/4.02  fof(f49,plain,(
% 27.38/4.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 27.38/4.02    inference(cnf_transformation,[],[f22])).
% 27.38/4.02  
% 27.38/4.02  fof(f10,axiom,(
% 27.38/4.02    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 27.38/4.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.38/4.02  
% 27.38/4.02  fof(f27,plain,(
% 27.38/4.02    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 27.38/4.02    inference(ennf_transformation,[],[f10])).
% 27.38/4.02  
% 27.38/4.02  fof(f54,plain,(
% 27.38/4.02    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 27.38/4.02    inference(cnf_transformation,[],[f27])).
% 27.38/4.02  
% 27.38/4.02  fof(f3,axiom,(
% 27.38/4.02    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 27.38/4.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.38/4.02  
% 27.38/4.02  fof(f20,plain,(
% 27.38/4.02    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 27.38/4.02    inference(ennf_transformation,[],[f3])).
% 27.38/4.02  
% 27.38/4.02  fof(f47,plain,(
% 27.38/4.02    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 27.38/4.02    inference(cnf_transformation,[],[f20])).
% 27.38/4.02  
% 27.38/4.02  fof(f63,plain,(
% 27.38/4.02    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 27.38/4.02    inference(cnf_transformation,[],[f42])).
% 27.38/4.02  
% 27.38/4.02  cnf(c_20,negated_conjecture,
% 27.38/4.02      ( v1_relat_1(sK1) ),
% 27.38/4.02      inference(cnf_transformation,[],[f61]) ).
% 27.38/4.02  
% 27.38/4.02  cnf(c_701,plain,
% 27.38/4.02      ( v1_relat_1(sK1) = iProver_top ),
% 27.38/4.02      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 27.38/4.02  
% 27.38/4.02  cnf(c_9,plain,
% 27.38/4.02      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 27.38/4.02      inference(cnf_transformation,[],[f52]) ).
% 27.38/4.02  
% 27.38/4.02  cnf(c_712,plain,
% 27.38/4.02      ( v1_relat_1(X0) != iProver_top
% 27.38/4.02      | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
% 27.38/4.02      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 27.38/4.02  
% 27.38/4.02  cnf(c_12,plain,
% 27.38/4.02      ( ~ v1_relat_1(X0)
% 27.38/4.02      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 27.38/4.02      inference(cnf_transformation,[],[f55]) ).
% 27.38/4.02  
% 27.38/4.02  cnf(c_709,plain,
% 27.38/4.02      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
% 27.38/4.02      | v1_relat_1(X0) != iProver_top ),
% 27.38/4.02      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 27.38/4.02  
% 27.38/4.02  cnf(c_1370,plain,
% 27.38/4.02      ( k10_relat_1(k7_relat_1(X0,X1),k2_relat_1(k7_relat_1(X0,X1))) = k1_relat_1(k7_relat_1(X0,X1))
% 27.38/4.02      | v1_relat_1(X0) != iProver_top ),
% 27.38/4.02      inference(superposition,[status(thm)],[c_712,c_709]) ).
% 27.38/4.02  
% 27.38/4.02  cnf(c_9338,plain,
% 27.38/4.02      ( k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0))) = k1_relat_1(k7_relat_1(sK1,X0)) ),
% 27.38/4.02      inference(superposition,[status(thm)],[c_701,c_1370]) ).
% 27.38/4.02  
% 27.38/4.02  cnf(c_10,plain,
% 27.38/4.02      ( ~ v1_relat_1(X0)
% 27.38/4.02      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 27.38/4.02      inference(cnf_transformation,[],[f53]) ).
% 27.38/4.02  
% 27.38/4.02  cnf(c_711,plain,
% 27.38/4.02      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 27.38/4.02      | v1_relat_1(X0) != iProver_top ),
% 27.38/4.02      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 27.38/4.02  
% 27.38/4.02  cnf(c_2303,plain,
% 27.38/4.02      ( k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
% 27.38/4.02      inference(superposition,[status(thm)],[c_701,c_711]) ).
% 27.38/4.02  
% 27.38/4.02  cnf(c_9339,plain,
% 27.38/4.02      ( k10_relat_1(k7_relat_1(sK1,X0),k9_relat_1(sK1,X0)) = k1_relat_1(k7_relat_1(sK1,X0)) ),
% 27.38/4.02      inference(light_normalisation,[status(thm)],[c_9338,c_2303]) ).
% 27.38/4.02  
% 27.38/4.02  cnf(c_17,plain,
% 27.38/4.02      ( ~ v1_relat_1(X0)
% 27.38/4.02      | k10_relat_1(k7_relat_1(X0,X1),X2) = k3_xboole_0(X1,k10_relat_1(X0,X2)) ),
% 27.38/4.02      inference(cnf_transformation,[],[f60]) ).
% 27.38/4.02  
% 27.38/4.02  cnf(c_704,plain,
% 27.38/4.02      ( k10_relat_1(k7_relat_1(X0,X1),X2) = k3_xboole_0(X1,k10_relat_1(X0,X2))
% 27.38/4.02      | v1_relat_1(X0) != iProver_top ),
% 27.38/4.02      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 27.38/4.02  
% 27.38/4.02  cnf(c_1269,plain,
% 27.38/4.02      ( k10_relat_1(k7_relat_1(sK1,X0),X1) = k3_xboole_0(X0,k10_relat_1(sK1,X1)) ),
% 27.38/4.02      inference(superposition,[status(thm)],[c_701,c_704]) ).
% 27.38/4.02  
% 27.38/4.02  cnf(c_9966,plain,
% 27.38/4.02      ( k3_xboole_0(X0,k10_relat_1(sK1,k9_relat_1(sK1,X0))) = k1_relat_1(k7_relat_1(sK1,X0)) ),
% 27.38/4.02      inference(superposition,[status(thm)],[c_9339,c_1269]) ).
% 27.38/4.02  
% 27.38/4.02  cnf(c_15,plain,
% 27.38/4.02      ( r1_tarski(k7_relat_1(X0,X1),X0) | ~ v1_relat_1(X0) ),
% 27.38/4.02      inference(cnf_transformation,[],[f58]) ).
% 27.38/4.02  
% 27.38/4.02  cnf(c_706,plain,
% 27.38/4.02      ( r1_tarski(k7_relat_1(X0,X1),X0) = iProver_top
% 27.38/4.02      | v1_relat_1(X0) != iProver_top ),
% 27.38/4.02      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 27.38/4.02  
% 27.38/4.02  cnf(c_5,plain,
% 27.38/4.02      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 27.38/4.02      inference(cnf_transformation,[],[f48]) ).
% 27.38/4.02  
% 27.38/4.02  cnf(c_716,plain,
% 27.38/4.02      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 27.38/4.02      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 27.38/4.02  
% 27.38/4.02  cnf(c_1361,plain,
% 27.38/4.02      ( k2_xboole_0(k7_relat_1(X0,X1),X0) = X0
% 27.38/4.02      | v1_relat_1(X0) != iProver_top ),
% 27.38/4.02      inference(superposition,[status(thm)],[c_706,c_716]) ).
% 27.38/4.02  
% 27.38/4.02  cnf(c_6039,plain,
% 27.38/4.02      ( k2_xboole_0(k7_relat_1(sK1,X0),sK1) = sK1 ),
% 27.38/4.02      inference(superposition,[status(thm)],[c_701,c_1361]) ).
% 27.38/4.02  
% 27.38/4.02  cnf(c_7,plain,
% 27.38/4.02      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 27.38/4.02      inference(cnf_transformation,[],[f50]) ).
% 27.38/4.02  
% 27.38/4.02  cnf(c_714,plain,
% 27.38/4.02      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 27.38/4.02      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 27.38/4.02  
% 27.38/4.02  cnf(c_6047,plain,
% 27.38/4.02      ( r1_tarski(k7_relat_1(sK1,X0),sK1) = iProver_top ),
% 27.38/4.02      inference(superposition,[status(thm)],[c_6039,c_714]) ).
% 27.38/4.02  
% 27.38/4.02  cnf(c_14,plain,
% 27.38/4.02      ( ~ r1_tarski(X0,X1)
% 27.38/4.02      | r1_tarski(k10_relat_1(X0,X2),k10_relat_1(X1,X2))
% 27.38/4.02      | ~ v1_relat_1(X0)
% 27.38/4.02      | ~ v1_relat_1(X1) ),
% 27.38/4.02      inference(cnf_transformation,[],[f57]) ).
% 27.38/4.02  
% 27.38/4.02  cnf(c_707,plain,
% 27.38/4.02      ( r1_tarski(X0,X1) != iProver_top
% 27.38/4.02      | r1_tarski(k10_relat_1(X0,X2),k10_relat_1(X1,X2)) = iProver_top
% 27.38/4.02      | v1_relat_1(X0) != iProver_top
% 27.38/4.02      | v1_relat_1(X1) != iProver_top ),
% 27.38/4.02      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 27.38/4.02  
% 27.38/4.02  cnf(c_3278,plain,
% 27.38/4.02      ( k2_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X2,X1)) = k10_relat_1(X2,X1)
% 27.38/4.02      | r1_tarski(X0,X2) != iProver_top
% 27.38/4.02      | v1_relat_1(X0) != iProver_top
% 27.38/4.02      | v1_relat_1(X2) != iProver_top ),
% 27.38/4.02      inference(superposition,[status(thm)],[c_707,c_716]) ).
% 27.38/4.02  
% 27.38/4.02  cnf(c_50521,plain,
% 27.38/4.02      ( k2_xboole_0(k10_relat_1(k7_relat_1(sK1,X0),X1),k10_relat_1(sK1,X1)) = k10_relat_1(sK1,X1)
% 27.38/4.02      | v1_relat_1(k7_relat_1(sK1,X0)) != iProver_top
% 27.38/4.02      | v1_relat_1(sK1) != iProver_top ),
% 27.38/4.02      inference(superposition,[status(thm)],[c_6047,c_3278]) ).
% 27.38/4.02  
% 27.38/4.02  cnf(c_50598,plain,
% 27.38/4.02      ( k2_xboole_0(k3_xboole_0(X0,k10_relat_1(sK1,X1)),k10_relat_1(sK1,X1)) = k10_relat_1(sK1,X1)
% 27.38/4.02      | v1_relat_1(k7_relat_1(sK1,X0)) != iProver_top
% 27.38/4.02      | v1_relat_1(sK1) != iProver_top ),
% 27.38/4.02      inference(light_normalisation,[status(thm)],[c_50521,c_1269]) ).
% 27.38/4.02  
% 27.38/4.02  cnf(c_21,plain,
% 27.38/4.02      ( v1_relat_1(sK1) = iProver_top ),
% 27.38/4.02      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 27.38/4.02  
% 27.38/4.02  cnf(c_51805,plain,
% 27.38/4.02      ( v1_relat_1(k7_relat_1(sK1,X0)) != iProver_top
% 27.38/4.02      | k2_xboole_0(k3_xboole_0(X0,k10_relat_1(sK1,X1)),k10_relat_1(sK1,X1)) = k10_relat_1(sK1,X1) ),
% 27.38/4.02      inference(global_propositional_subsumption,
% 27.38/4.02                [status(thm)],
% 27.38/4.02                [c_50598,c_21]) ).
% 27.38/4.02  
% 27.38/4.02  cnf(c_51806,plain,
% 27.38/4.02      ( k2_xboole_0(k3_xboole_0(X0,k10_relat_1(sK1,X1)),k10_relat_1(sK1,X1)) = k10_relat_1(sK1,X1)
% 27.38/4.02      | v1_relat_1(k7_relat_1(sK1,X0)) != iProver_top ),
% 27.38/4.02      inference(renaming,[status(thm)],[c_51805]) ).
% 27.38/4.02  
% 27.38/4.02  cnf(c_51811,plain,
% 27.38/4.02      ( k2_xboole_0(k3_xboole_0(X0,k10_relat_1(sK1,X1)),k10_relat_1(sK1,X1)) = k10_relat_1(sK1,X1)
% 27.38/4.02      | v1_relat_1(sK1) != iProver_top ),
% 27.38/4.02      inference(superposition,[status(thm)],[c_712,c_51806]) ).
% 27.38/4.02  
% 27.38/4.02  cnf(c_118002,plain,
% 27.38/4.02      ( k2_xboole_0(k3_xboole_0(X0,k10_relat_1(sK1,X1)),k10_relat_1(sK1,X1)) = k10_relat_1(sK1,X1) ),
% 27.38/4.02      inference(global_propositional_subsumption,
% 27.38/4.02                [status(thm)],
% 27.38/4.02                [c_51811,c_21]) ).
% 27.38/4.02  
% 27.38/4.02  cnf(c_118049,plain,
% 27.38/4.02      ( r1_tarski(k3_xboole_0(X0,k10_relat_1(sK1,X1)),k10_relat_1(sK1,X1)) = iProver_top ),
% 27.38/4.02      inference(superposition,[status(thm)],[c_118002,c_714]) ).
% 27.38/4.02  
% 27.38/4.02  cnf(c_118197,plain,
% 27.38/4.02      ( r1_tarski(k1_relat_1(k7_relat_1(sK1,X0)),k10_relat_1(sK1,k9_relat_1(sK1,X0))) = iProver_top ),
% 27.38/4.02      inference(superposition,[status(thm)],[c_9966,c_118049]) ).
% 27.38/4.02  
% 27.38/4.02  cnf(c_19,negated_conjecture,
% 27.38/4.02      ( r1_tarski(sK0,k1_relat_1(sK1)) ),
% 27.38/4.02      inference(cnf_transformation,[],[f62]) ).
% 27.38/4.02  
% 27.38/4.02  cnf(c_702,plain,
% 27.38/4.02      ( r1_tarski(sK0,k1_relat_1(sK1)) = iProver_top ),
% 27.38/4.02      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 27.38/4.02  
% 27.38/4.02  cnf(c_6,plain,
% 27.38/4.02      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 27.38/4.02      inference(cnf_transformation,[],[f49]) ).
% 27.38/4.02  
% 27.38/4.02  cnf(c_715,plain,
% 27.38/4.02      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 27.38/4.02      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 27.38/4.02  
% 27.38/4.02  cnf(c_1176,plain,
% 27.38/4.02      ( k3_xboole_0(sK0,k1_relat_1(sK1)) = sK0 ),
% 27.38/4.02      inference(superposition,[status(thm)],[c_702,c_715]) ).
% 27.38/4.02  
% 27.38/4.02  cnf(c_1371,plain,
% 27.38/4.02      ( k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(sK1) ),
% 27.38/4.02      inference(superposition,[status(thm)],[c_701,c_709]) ).
% 27.38/4.02  
% 27.38/4.02  cnf(c_11,plain,
% 27.38/4.02      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 27.38/4.02      inference(cnf_transformation,[],[f54]) ).
% 27.38/4.02  
% 27.38/4.02  cnf(c_710,plain,
% 27.38/4.02      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) = iProver_top
% 27.38/4.02      | v1_relat_1(X0) != iProver_top ),
% 27.38/4.02      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 27.38/4.02  
% 27.38/4.02  cnf(c_1639,plain,
% 27.38/4.02      ( r1_tarski(k3_xboole_0(X0,k10_relat_1(sK1,X1)),k1_relat_1(k7_relat_1(sK1,X0))) = iProver_top
% 27.38/4.02      | v1_relat_1(k7_relat_1(sK1,X0)) != iProver_top ),
% 27.38/4.02      inference(superposition,[status(thm)],[c_1269,c_710]) ).
% 27.38/4.02  
% 27.38/4.02  cnf(c_1744,plain,
% 27.38/4.02      ( r1_tarski(k3_xboole_0(X0,k1_relat_1(sK1)),k1_relat_1(k7_relat_1(sK1,X0))) = iProver_top
% 27.38/4.02      | v1_relat_1(k7_relat_1(sK1,X0)) != iProver_top ),
% 27.38/4.02      inference(superposition,[status(thm)],[c_1371,c_1639]) ).
% 27.38/4.02  
% 27.38/4.02  cnf(c_1757,plain,
% 27.38/4.02      ( r1_tarski(sK0,k1_relat_1(k7_relat_1(sK1,sK0))) = iProver_top
% 27.38/4.02      | v1_relat_1(k7_relat_1(sK1,sK0)) != iProver_top ),
% 27.38/4.02      inference(superposition,[status(thm)],[c_1176,c_1744]) ).
% 27.38/4.02  
% 27.38/4.02  cnf(c_1935,plain,
% 27.38/4.02      ( k2_xboole_0(sK0,k1_relat_1(k7_relat_1(sK1,sK0))) = k1_relat_1(k7_relat_1(sK1,sK0))
% 27.38/4.02      | v1_relat_1(k7_relat_1(sK1,sK0)) != iProver_top ),
% 27.38/4.02      inference(superposition,[status(thm)],[c_1757,c_716]) ).
% 27.38/4.02  
% 27.38/4.02  cnf(c_2143,plain,
% 27.38/4.02      ( k2_xboole_0(sK0,k1_relat_1(k7_relat_1(sK1,sK0))) = k1_relat_1(k7_relat_1(sK1,sK0))
% 27.38/4.02      | v1_relat_1(sK1) != iProver_top ),
% 27.38/4.02      inference(superposition,[status(thm)],[c_712,c_1935]) ).
% 27.38/4.02  
% 27.38/4.02  cnf(c_16515,plain,
% 27.38/4.02      ( k2_xboole_0(sK0,k1_relat_1(k7_relat_1(sK1,sK0))) = k1_relat_1(k7_relat_1(sK1,sK0)) ),
% 27.38/4.02      inference(global_propositional_subsumption,
% 27.38/4.02                [status(thm)],
% 27.38/4.02                [c_2143,c_21]) ).
% 27.38/4.02  
% 27.38/4.02  cnf(c_4,plain,
% 27.38/4.02      ( r1_tarski(X0,X1) | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 27.38/4.02      inference(cnf_transformation,[],[f47]) ).
% 27.38/4.02  
% 27.38/4.02  cnf(c_717,plain,
% 27.38/4.02      ( r1_tarski(X0,X1) = iProver_top
% 27.38/4.02      | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
% 27.38/4.02      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 27.38/4.02  
% 27.38/4.02  cnf(c_16529,plain,
% 27.38/4.02      ( r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),X0) != iProver_top
% 27.38/4.02      | r1_tarski(sK0,X0) = iProver_top ),
% 27.38/4.02      inference(superposition,[status(thm)],[c_16515,c_717]) ).
% 27.38/4.02  
% 27.38/4.02  cnf(c_118783,plain,
% 27.38/4.02      ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) = iProver_top ),
% 27.38/4.02      inference(superposition,[status(thm)],[c_118197,c_16529]) ).
% 27.38/4.02  
% 27.38/4.02  cnf(c_18,negated_conjecture,
% 27.38/4.02      ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
% 27.38/4.02      inference(cnf_transformation,[],[f63]) ).
% 27.38/4.02  
% 27.38/4.02  cnf(c_23,plain,
% 27.38/4.02      ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) != iProver_top ),
% 27.38/4.02      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 27.38/4.02  
% 27.38/4.02  cnf(contradiction,plain,
% 27.38/4.02      ( $false ),
% 27.38/4.02      inference(minisat,[status(thm)],[c_118783,c_23]) ).
% 27.38/4.02  
% 27.38/4.02  
% 27.38/4.02  % SZS output end CNFRefutation for theBenchmark.p
% 27.38/4.02  
% 27.38/4.02  ------                               Statistics
% 27.38/4.02  
% 27.38/4.02  ------ General
% 27.38/4.02  
% 27.38/4.02  abstr_ref_over_cycles:                  0
% 27.38/4.02  abstr_ref_under_cycles:                 0
% 27.38/4.02  gc_basic_clause_elim:                   0
% 27.38/4.02  forced_gc_time:                         0
% 27.38/4.02  parsing_time:                           0.008
% 27.38/4.02  unif_index_cands_time:                  0.
% 27.38/4.02  unif_index_add_time:                    0.
% 27.38/4.02  orderings_time:                         0.
% 27.38/4.02  out_proof_time:                         0.038
% 27.38/4.02  total_time:                             3.25
% 27.38/4.02  num_of_symbols:                         42
% 27.38/4.02  num_of_terms:                           122062
% 27.38/4.02  
% 27.38/4.02  ------ Preprocessing
% 27.38/4.02  
% 27.38/4.02  num_of_splits:                          0
% 27.38/4.02  num_of_split_atoms:                     0
% 27.38/4.02  num_of_reused_defs:                     0
% 27.38/4.02  num_eq_ax_congr_red:                    15
% 27.38/4.02  num_of_sem_filtered_clauses:            1
% 27.38/4.02  num_of_subtypes:                        0
% 27.38/4.02  monotx_restored_types:                  0
% 27.38/4.02  sat_num_of_epr_types:                   0
% 27.38/4.02  sat_num_of_non_cyclic_types:            0
% 27.38/4.02  sat_guarded_non_collapsed_types:        0
% 27.38/4.02  num_pure_diseq_elim:                    0
% 27.38/4.02  simp_replaced_by:                       0
% 27.38/4.02  res_preprocessed:                       99
% 27.38/4.02  prep_upred:                             0
% 27.38/4.02  prep_unflattend:                        0
% 27.38/4.02  smt_new_axioms:                         0
% 27.38/4.02  pred_elim_cands:                        2
% 27.38/4.02  pred_elim:                              0
% 27.38/4.02  pred_elim_cl:                           0
% 27.38/4.02  pred_elim_cycles:                       2
% 27.38/4.02  merged_defs:                            0
% 27.38/4.02  merged_defs_ncl:                        0
% 27.38/4.02  bin_hyper_res:                          0
% 27.38/4.02  prep_cycles:                            4
% 27.38/4.02  pred_elim_time:                         0.
% 27.38/4.02  splitting_time:                         0.
% 27.38/4.02  sem_filter_time:                        0.
% 27.38/4.02  monotx_time:                            0.001
% 27.38/4.02  subtype_inf_time:                       0.
% 27.38/4.02  
% 27.38/4.02  ------ Problem properties
% 27.38/4.02  
% 27.38/4.02  clauses:                                20
% 27.38/4.02  conjectures:                            3
% 27.38/4.02  epr:                                    3
% 27.38/4.02  horn:                                   20
% 27.38/4.02  ground:                                 3
% 27.38/4.02  unary:                                  5
% 27.38/4.02  binary:                                 10
% 27.38/4.02  lits:                                   41
% 27.38/4.02  lits_eq:                                7
% 27.38/4.02  fd_pure:                                0
% 27.38/4.02  fd_pseudo:                              0
% 27.38/4.02  fd_cond:                                0
% 27.38/4.02  fd_pseudo_cond:                         1
% 27.38/4.02  ac_symbols:                             0
% 27.38/4.02  
% 27.38/4.02  ------ Propositional Solver
% 27.38/4.02  
% 27.38/4.02  prop_solver_calls:                      51
% 27.38/4.02  prop_fast_solver_calls:                 1644
% 27.38/4.02  smt_solver_calls:                       0
% 27.38/4.02  smt_fast_solver_calls:                  0
% 27.38/4.02  prop_num_of_clauses:                    45826
% 27.38/4.02  prop_preprocess_simplified:             61339
% 27.38/4.02  prop_fo_subsumed:                       34
% 27.38/4.02  prop_solver_time:                       0.
% 27.38/4.02  smt_solver_time:                        0.
% 27.38/4.02  smt_fast_solver_time:                   0.
% 27.38/4.02  prop_fast_solver_time:                  0.
% 27.38/4.02  prop_unsat_core_time:                   0.007
% 27.38/4.02  
% 27.38/4.02  ------ QBF
% 27.38/4.02  
% 27.38/4.02  qbf_q_res:                              0
% 27.38/4.02  qbf_num_tautologies:                    0
% 27.38/4.02  qbf_prep_cycles:                        0
% 27.38/4.02  
% 27.38/4.02  ------ BMC1
% 27.38/4.02  
% 27.38/4.02  bmc1_current_bound:                     -1
% 27.38/4.02  bmc1_last_solved_bound:                 -1
% 27.38/4.02  bmc1_unsat_core_size:                   -1
% 27.38/4.02  bmc1_unsat_core_parents_size:           -1
% 27.38/4.02  bmc1_merge_next_fun:                    0
% 27.38/4.02  bmc1_unsat_core_clauses_time:           0.
% 27.38/4.02  
% 27.38/4.02  ------ Instantiation
% 27.38/4.02  
% 27.38/4.02  inst_num_of_clauses:                    193
% 27.38/4.02  inst_num_in_passive:                    11
% 27.38/4.02  inst_num_in_active:                     2418
% 27.38/4.02  inst_num_in_unprocessed:                94
% 27.38/4.02  inst_num_of_loops:                      3089
% 27.38/4.02  inst_num_of_learning_restarts:          1
% 27.38/4.02  inst_num_moves_active_passive:          663
% 27.38/4.02  inst_lit_activity:                      0
% 27.38/4.02  inst_lit_activity_moves:                4
% 27.38/4.02  inst_num_tautologies:                   0
% 27.38/4.02  inst_num_prop_implied:                  0
% 27.38/4.02  inst_num_existing_simplified:           0
% 27.38/4.02  inst_num_eq_res_simplified:             0
% 27.38/4.02  inst_num_child_elim:                    0
% 27.38/4.02  inst_num_of_dismatching_blockings:      18888
% 27.38/4.02  inst_num_of_non_proper_insts:           12935
% 27.38/4.02  inst_num_of_duplicates:                 0
% 27.38/4.02  inst_inst_num_from_inst_to_res:         0
% 27.38/4.02  inst_dismatching_checking_time:         0.
% 27.38/4.02  
% 27.38/4.02  ------ Resolution
% 27.38/4.02  
% 27.38/4.02  res_num_of_clauses:                     29
% 27.38/4.02  res_num_in_passive:                     29
% 27.38/4.02  res_num_in_active:                      0
% 27.38/4.02  res_num_of_loops:                       103
% 27.38/4.02  res_forward_subset_subsumed:            1563
% 27.38/4.02  res_backward_subset_subsumed:           42
% 27.38/4.02  res_forward_subsumed:                   0
% 27.38/4.02  res_backward_subsumed:                  0
% 27.38/4.02  res_forward_subsumption_resolution:     0
% 27.38/4.02  res_backward_subsumption_resolution:    0
% 27.38/4.02  res_clause_to_clause_subsumption:       69914
% 27.38/4.02  res_orphan_elimination:                 0
% 27.38/4.02  res_tautology_del:                      453
% 27.38/4.02  res_num_eq_res_simplified:              0
% 27.38/4.02  res_num_sel_changes:                    0
% 27.38/4.02  res_moves_from_active_to_pass:          0
% 27.38/4.02  
% 27.38/4.02  ------ Superposition
% 27.38/4.02  
% 27.38/4.02  sup_time_total:                         0.
% 27.38/4.02  sup_time_generating:                    0.
% 27.38/4.02  sup_time_sim_full:                      0.
% 27.38/4.02  sup_time_sim_immed:                     0.
% 27.38/4.02  
% 27.38/4.02  sup_num_of_clauses:                     5630
% 27.38/4.02  sup_num_in_active:                      591
% 27.38/4.02  sup_num_in_passive:                     5039
% 27.38/4.02  sup_num_of_loops:                       617
% 27.38/4.02  sup_fw_superposition:                   10809
% 27.38/4.02  sup_bw_superposition:                   9019
% 27.38/4.02  sup_immediate_simplified:               7330
% 27.38/4.02  sup_given_eliminated:                   2
% 27.38/4.02  comparisons_done:                       0
% 27.38/4.02  comparisons_avoided:                    0
% 27.38/4.02  
% 27.38/4.02  ------ Simplifications
% 27.38/4.02  
% 27.38/4.02  
% 27.38/4.02  sim_fw_subset_subsumed:                 293
% 27.38/4.02  sim_bw_subset_subsumed:                 56
% 27.38/4.02  sim_fw_subsumed:                        3094
% 27.38/4.02  sim_bw_subsumed:                        126
% 27.38/4.02  sim_fw_subsumption_res:                 0
% 27.38/4.02  sim_bw_subsumption_res:                 0
% 27.38/4.02  sim_tautology_del:                      206
% 27.38/4.02  sim_eq_tautology_del:                   870
% 27.38/4.02  sim_eq_res_simp:                        0
% 27.38/4.02  sim_fw_demodulated:                     3082
% 27.38/4.02  sim_bw_demodulated:                     6
% 27.38/4.02  sim_light_normalised:                   1516
% 27.38/4.02  sim_joinable_taut:                      0
% 27.38/4.02  sim_joinable_simp:                      0
% 27.38/4.02  sim_ac_normalised:                      0
% 27.38/4.02  sim_smt_subsumption:                    0
% 27.38/4.02  
%------------------------------------------------------------------------------
