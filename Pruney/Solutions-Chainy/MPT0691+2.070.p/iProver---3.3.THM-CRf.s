%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:51:50 EST 2020

% Result     : Theorem 3.77s
% Output     : CNFRefutation 3.77s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 687 expanded)
%              Number of clauses        :   61 ( 235 expanded)
%              Number of leaves         :   11 ( 129 expanded)
%              Depth                    :   22
%              Number of atoms          :  197 (1727 expanded)
%              Number of equality atoms :  100 ( 376 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f38])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f62,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f43])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f36,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f37,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f40,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f37,f40])).

fof(f60,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f41])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f59,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f52,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f61,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_719,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_18,negated_conjecture,
    ( r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_703,plain,
    ( r1_tarski(sK0,k1_relat_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_707,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3417,plain,
    ( k1_relat_1(k7_relat_1(sK1,sK0)) = sK0
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_703,c_707])).

cnf(c_19,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_899,plain,
    ( ~ r1_tarski(sK0,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | k1_relat_1(k7_relat_1(sK1,sK0)) = sK0 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_3751,plain,
    ( k1_relat_1(k7_relat_1(sK1,sK0)) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3417,c_19,c_18,c_899])).

cnf(c_15,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_706,plain,
    ( k7_relat_1(X0,X1) = X0
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3755,plain,
    ( k7_relat_1(k7_relat_1(sK1,sK0),X0) = k7_relat_1(sK1,sK0)
    | r1_tarski(sK0,X0) != iProver_top
    | v1_relat_1(k7_relat_1(sK1,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3751,c_706])).

cnf(c_20,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_3912,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,sK0)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_3913,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k7_relat_1(X0,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3912])).

cnf(c_3915,plain,
    ( v1_relat_1(k7_relat_1(sK1,sK0)) = iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3913])).

cnf(c_9656,plain,
    ( r1_tarski(sK0,X0) != iProver_top
    | k7_relat_1(k7_relat_1(sK1,sK0),X0) = k7_relat_1(sK1,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3755,c_20,c_3915])).

cnf(c_9657,plain,
    ( k7_relat_1(k7_relat_1(sK1,sK0),X0) = k7_relat_1(sK1,sK0)
    | r1_tarski(sK0,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_9656])).

cnf(c_9664,plain,
    ( k7_relat_1(k7_relat_1(sK1,sK0),sK0) = k7_relat_1(sK1,sK0) ),
    inference(superposition,[status(thm)],[c_719,c_9657])).

cnf(c_702,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_714,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_711,plain,
    ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1151,plain,
    ( k10_relat_1(k7_relat_1(X0,X1),k2_relat_1(k7_relat_1(X0,X1))) = k1_relat_1(k7_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_714,c_711])).

cnf(c_7862,plain,
    ( k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0))) = k1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_702,c_1151])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_713,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1476,plain,
    ( k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
    inference(superposition,[status(thm)],[c_702,c_713])).

cnf(c_7864,plain,
    ( k10_relat_1(k7_relat_1(sK1,X0),k9_relat_1(sK1,X0)) = k1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_7862,c_1476])).

cnf(c_16,plain,
    ( ~ v1_relat_1(X0)
    | k3_xboole_0(X1,k10_relat_1(X0,X2)) = k10_relat_1(k7_relat_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_705,plain,
    ( k3_xboole_0(X0,k10_relat_1(X1,X2)) = k10_relat_1(k7_relat_1(X1,X0),X2)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1300,plain,
    ( k3_xboole_0(X0,k10_relat_1(k7_relat_1(X1,X2),X3)) = k10_relat_1(k7_relat_1(k7_relat_1(X1,X2),X0),X3)
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_714,c_705])).

cnf(c_10094,plain,
    ( k3_xboole_0(X0,k10_relat_1(k7_relat_1(sK1,X1),X2)) = k10_relat_1(k7_relat_1(k7_relat_1(sK1,X1),X0),X2) ),
    inference(superposition,[status(thm)],[c_702,c_1300])).

cnf(c_10547,plain,
    ( k10_relat_1(k7_relat_1(k7_relat_1(sK1,X0),X1),k9_relat_1(sK1,X0)) = k3_xboole_0(X1,k1_relat_1(k7_relat_1(sK1,X0))) ),
    inference(superposition,[status(thm)],[c_7864,c_10094])).

cnf(c_10989,plain,
    ( k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)) = k3_xboole_0(sK0,k1_relat_1(k7_relat_1(sK1,sK0))) ),
    inference(superposition,[status(thm)],[c_9664,c_10547])).

cnf(c_11037,plain,
    ( k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)) = k3_xboole_0(sK0,sK0) ),
    inference(light_normalisation,[status(thm)],[c_10989,c_3751])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | k3_xboole_0(k1_relat_1(X0),X1) = k1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_708,plain,
    ( k3_xboole_0(k1_relat_1(X0),X1) = k1_relat_1(k7_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2013,plain,
    ( k3_xboole_0(k1_relat_1(sK1),X0) = k1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_702,c_708])).

cnf(c_9667,plain,
    ( k7_relat_1(k7_relat_1(sK1,sK0),k1_relat_1(sK1)) = k7_relat_1(sK1,sK0) ),
    inference(superposition,[status(thm)],[c_703,c_9657])).

cnf(c_10988,plain,
    ( k3_xboole_0(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_9667,c_10547])).

cnf(c_11039,plain,
    ( k3_xboole_0(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) = k3_xboole_0(sK0,sK0) ),
    inference(light_normalisation,[status(thm)],[c_10988,c_11037])).

cnf(c_11041,plain,
    ( k3_xboole_0(k1_relat_1(sK1),sK0) = k3_xboole_0(sK0,sK0) ),
    inference(light_normalisation,[status(thm)],[c_11039,c_3751])).

cnf(c_11217,plain,
    ( k1_relat_1(k7_relat_1(sK1,sK0)) = k3_xboole_0(sK0,sK0) ),
    inference(superposition,[status(thm)],[c_2013,c_11041])).

cnf(c_11219,plain,
    ( k3_xboole_0(sK0,sK0) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_11217,c_3751])).

cnf(c_12012,plain,
    ( k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_11037,c_11219])).

cnf(c_1301,plain,
    ( k3_xboole_0(X0,k10_relat_1(sK1,X1)) = k10_relat_1(k7_relat_1(sK1,X0),X1) ),
    inference(superposition,[status(thm)],[c_702,c_705])).

cnf(c_2012,plain,
    ( k3_xboole_0(k1_relat_1(k7_relat_1(X0,X1)),X2) = k1_relat_1(k7_relat_1(k7_relat_1(X0,X1),X2))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_714,c_708])).

cnf(c_12824,plain,
    ( k3_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)),X1) = k1_relat_1(k7_relat_1(k7_relat_1(sK1,X0),X1)) ),
    inference(superposition,[status(thm)],[c_702,c_2012])).

cnf(c_12838,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1(sK1,sK0),X0)) = k3_xboole_0(sK0,X0) ),
    inference(superposition,[status(thm)],[c_3751,c_12824])).

cnf(c_12,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_709,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_13520,plain,
    ( r1_tarski(k3_xboole_0(sK0,X0),X0) = iProver_top
    | v1_relat_1(k7_relat_1(sK1,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12838,c_709])).

cnf(c_14585,plain,
    ( r1_tarski(k3_xboole_0(sK0,X0),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13520,c_20,c_3915])).

cnf(c_14592,plain,
    ( r1_tarski(k10_relat_1(k7_relat_1(sK1,sK0),X0),k10_relat_1(sK1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1301,c_14585])).

cnf(c_14952,plain,
    ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_12012,c_14592])).

cnf(c_17,negated_conjecture,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_22,plain,
    ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14952,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:55:59 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.77/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.77/0.99  
% 3.77/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.77/0.99  
% 3.77/0.99  ------  iProver source info
% 3.77/0.99  
% 3.77/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.77/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.77/0.99  git: non_committed_changes: false
% 3.77/0.99  git: last_make_outside_of_git: false
% 3.77/0.99  
% 3.77/0.99  ------ 
% 3.77/0.99  ------ Parsing...
% 3.77/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.77/0.99  
% 3.77/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.77/0.99  
% 3.77/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.77/0.99  
% 3.77/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.77/0.99  ------ Proving...
% 3.77/0.99  ------ Problem Properties 
% 3.77/0.99  
% 3.77/0.99  
% 3.77/0.99  clauses                                 19
% 3.77/0.99  conjectures                             3
% 3.77/0.99  EPR                                     4
% 3.77/0.99  Horn                                    19
% 3.77/0.99  unary                                   5
% 3.77/0.99  binary                                  8
% 3.77/0.99  lits                                    39
% 3.77/0.99  lits eq                                 7
% 3.77/0.99  fd_pure                                 0
% 3.77/0.99  fd_pseudo                               0
% 3.77/0.99  fd_cond                                 0
% 3.77/0.99  fd_pseudo_cond                          1
% 3.77/0.99  AC symbols                              0
% 3.77/0.99  
% 3.77/0.99  ------ Input Options Time Limit: Unbounded
% 3.77/0.99  
% 3.77/0.99  
% 3.77/0.99  ------ 
% 3.77/0.99  Current options:
% 3.77/0.99  ------ 
% 3.77/0.99  
% 3.77/0.99  
% 3.77/0.99  
% 3.77/0.99  
% 3.77/0.99  ------ Proving...
% 3.77/0.99  
% 3.77/0.99  
% 3.77/0.99  % SZS status Theorem for theBenchmark.p
% 3.77/0.99  
% 3.77/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.77/0.99  
% 3.77/0.99  fof(f1,axiom,(
% 3.77/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.77/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f38,plain,(
% 3.77/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.77/0.99    inference(nnf_transformation,[],[f1])).
% 3.77/0.99  
% 3.77/0.99  fof(f39,plain,(
% 3.77/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.77/0.99    inference(flattening,[],[f38])).
% 3.77/0.99  
% 3.77/0.99  fof(f43,plain,(
% 3.77/0.99    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.77/0.99    inference(cnf_transformation,[],[f39])).
% 3.77/0.99  
% 3.77/0.99  fof(f62,plain,(
% 3.77/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.77/0.99    inference(equality_resolution,[],[f43])).
% 3.77/0.99  
% 3.77/0.99  fof(f16,conjecture,(
% 3.77/0.99    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 3.77/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f17,negated_conjecture,(
% 3.77/0.99    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 3.77/0.99    inference(negated_conjecture,[],[f16])).
% 3.77/0.99  
% 3.77/0.99  fof(f36,plain,(
% 3.77/0.99    ? [X0,X1] : ((~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 3.77/0.99    inference(ennf_transformation,[],[f17])).
% 3.77/0.99  
% 3.77/0.99  fof(f37,plain,(
% 3.77/0.99    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 3.77/0.99    inference(flattening,[],[f36])).
% 3.77/0.99  
% 3.77/0.99  fof(f40,plain,(
% 3.77/0.99    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 3.77/0.99    introduced(choice_axiom,[])).
% 3.77/0.99  
% 3.77/0.99  fof(f41,plain,(
% 3.77/0.99    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1)),
% 3.77/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f37,f40])).
% 3.77/0.99  
% 3.77/0.99  fof(f60,plain,(
% 3.77/0.99    r1_tarski(sK0,k1_relat_1(sK1))),
% 3.77/0.99    inference(cnf_transformation,[],[f41])).
% 3.77/0.99  
% 3.77/0.99  fof(f13,axiom,(
% 3.77/0.99    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 3.77/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f31,plain,(
% 3.77/0.99    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 3.77/0.99    inference(ennf_transformation,[],[f13])).
% 3.77/0.99  
% 3.77/0.99  fof(f32,plain,(
% 3.77/0.99    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.77/0.99    inference(flattening,[],[f31])).
% 3.77/0.99  
% 3.77/0.99  fof(f56,plain,(
% 3.77/0.99    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.77/0.99    inference(cnf_transformation,[],[f32])).
% 3.77/0.99  
% 3.77/0.99  fof(f59,plain,(
% 3.77/0.99    v1_relat_1(sK1)),
% 3.77/0.99    inference(cnf_transformation,[],[f41])).
% 3.77/0.99  
% 3.77/0.99  fof(f14,axiom,(
% 3.77/0.99    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 3.77/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f33,plain,(
% 3.77/0.99    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.77/0.99    inference(ennf_transformation,[],[f14])).
% 3.77/0.99  
% 3.77/0.99  fof(f34,plain,(
% 3.77/0.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.77/0.99    inference(flattening,[],[f33])).
% 3.77/0.99  
% 3.77/0.99  fof(f57,plain,(
% 3.77/0.99    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.77/0.99    inference(cnf_transformation,[],[f34])).
% 3.77/0.99  
% 3.77/0.99  fof(f6,axiom,(
% 3.77/0.99    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 3.77/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f23,plain,(
% 3.77/0.99    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 3.77/0.99    inference(ennf_transformation,[],[f6])).
% 3.77/0.99  
% 3.77/0.99  fof(f49,plain,(
% 3.77/0.99    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 3.77/0.99    inference(cnf_transformation,[],[f23])).
% 3.77/0.99  
% 3.77/0.99  fof(f9,axiom,(
% 3.77/0.99    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 3.77/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f26,plain,(
% 3.77/0.99    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 3.77/0.99    inference(ennf_transformation,[],[f9])).
% 3.77/0.99  
% 3.77/0.99  fof(f52,plain,(
% 3.77/0.99    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.77/0.99    inference(cnf_transformation,[],[f26])).
% 3.77/0.99  
% 3.77/0.99  fof(f7,axiom,(
% 3.77/0.99    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 3.77/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f24,plain,(
% 3.77/0.99    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.77/0.99    inference(ennf_transformation,[],[f7])).
% 3.77/0.99  
% 3.77/0.99  fof(f50,plain,(
% 3.77/0.99    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.77/0.99    inference(cnf_transformation,[],[f24])).
% 3.77/0.99  
% 3.77/0.99  fof(f15,axiom,(
% 3.77/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 3.77/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f35,plain,(
% 3.77/0.99    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 3.77/0.99    inference(ennf_transformation,[],[f15])).
% 3.77/0.99  
% 3.77/0.99  fof(f58,plain,(
% 3.77/0.99    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.77/0.99    inference(cnf_transformation,[],[f35])).
% 3.77/0.99  
% 3.77/0.99  fof(f12,axiom,(
% 3.77/0.99    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 3.77/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f30,plain,(
% 3.77/0.99    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.77/0.99    inference(ennf_transformation,[],[f12])).
% 3.77/0.99  
% 3.77/0.99  fof(f55,plain,(
% 3.77/0.99    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.77/0.99    inference(cnf_transformation,[],[f30])).
% 3.77/0.99  
% 3.77/0.99  fof(f11,axiom,(
% 3.77/0.99    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 3.77/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/0.99  
% 3.77/0.99  fof(f29,plain,(
% 3.77/0.99    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 3.77/0.99    inference(ennf_transformation,[],[f11])).
% 3.77/0.99  
% 3.77/0.99  fof(f54,plain,(
% 3.77/0.99    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 3.77/0.99    inference(cnf_transformation,[],[f29])).
% 3.77/0.99  
% 3.77/0.99  fof(f61,plain,(
% 3.77/0.99    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 3.77/0.99    inference(cnf_transformation,[],[f41])).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1,plain,
% 3.77/0.99      ( r1_tarski(X0,X0) ),
% 3.77/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_719,plain,
% 3.77/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_18,negated_conjecture,
% 3.77/0.99      ( r1_tarski(sK0,k1_relat_1(sK1)) ),
% 3.77/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_703,plain,
% 3.77/0.99      ( r1_tarski(sK0,k1_relat_1(sK1)) = iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_14,plain,
% 3.77/0.99      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 3.77/0.99      | ~ v1_relat_1(X1)
% 3.77/0.99      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 3.77/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_707,plain,
% 3.77/0.99      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 3.77/0.99      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 3.77/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_3417,plain,
% 3.77/0.99      ( k1_relat_1(k7_relat_1(sK1,sK0)) = sK0
% 3.77/0.99      | v1_relat_1(sK1) != iProver_top ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_703,c_707]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_19,negated_conjecture,
% 3.77/0.99      ( v1_relat_1(sK1) ),
% 3.77/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_899,plain,
% 3.77/0.99      ( ~ r1_tarski(sK0,k1_relat_1(sK1))
% 3.77/0.99      | ~ v1_relat_1(sK1)
% 3.77/0.99      | k1_relat_1(k7_relat_1(sK1,sK0)) = sK0 ),
% 3.77/0.99      inference(instantiation,[status(thm)],[c_14]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_3751,plain,
% 3.77/0.99      ( k1_relat_1(k7_relat_1(sK1,sK0)) = sK0 ),
% 3.77/0.99      inference(global_propositional_subsumption,
% 3.77/0.99                [status(thm)],
% 3.77/0.99                [c_3417,c_19,c_18,c_899]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_15,plain,
% 3.77/0.99      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 3.77/0.99      | ~ v1_relat_1(X0)
% 3.77/0.99      | k7_relat_1(X0,X1) = X0 ),
% 3.77/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_706,plain,
% 3.77/0.99      ( k7_relat_1(X0,X1) = X0
% 3.77/0.99      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 3.77/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_3755,plain,
% 3.77/0.99      ( k7_relat_1(k7_relat_1(sK1,sK0),X0) = k7_relat_1(sK1,sK0)
% 3.77/0.99      | r1_tarski(sK0,X0) != iProver_top
% 3.77/0.99      | v1_relat_1(k7_relat_1(sK1,sK0)) != iProver_top ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_3751,c_706]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_20,plain,
% 3.77/0.99      ( v1_relat_1(sK1) = iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_7,plain,
% 3.77/0.99      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 3.77/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_3912,plain,
% 3.77/0.99      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,sK0)) ),
% 3.77/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_3913,plain,
% 3.77/0.99      ( v1_relat_1(X0) != iProver_top
% 3.77/0.99      | v1_relat_1(k7_relat_1(X0,sK0)) = iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_3912]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_3915,plain,
% 3.77/0.99      ( v1_relat_1(k7_relat_1(sK1,sK0)) = iProver_top
% 3.77/0.99      | v1_relat_1(sK1) != iProver_top ),
% 3.77/0.99      inference(instantiation,[status(thm)],[c_3913]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_9656,plain,
% 3.77/0.99      ( r1_tarski(sK0,X0) != iProver_top
% 3.77/0.99      | k7_relat_1(k7_relat_1(sK1,sK0),X0) = k7_relat_1(sK1,sK0) ),
% 3.77/0.99      inference(global_propositional_subsumption,
% 3.77/0.99                [status(thm)],
% 3.77/0.99                [c_3755,c_20,c_3915]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_9657,plain,
% 3.77/0.99      ( k7_relat_1(k7_relat_1(sK1,sK0),X0) = k7_relat_1(sK1,sK0)
% 3.77/0.99      | r1_tarski(sK0,X0) != iProver_top ),
% 3.77/0.99      inference(renaming,[status(thm)],[c_9656]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_9664,plain,
% 3.77/0.99      ( k7_relat_1(k7_relat_1(sK1,sK0),sK0) = k7_relat_1(sK1,sK0) ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_719,c_9657]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_702,plain,
% 3.77/0.99      ( v1_relat_1(sK1) = iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_714,plain,
% 3.77/0.99      ( v1_relat_1(X0) != iProver_top
% 3.77/0.99      | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_10,plain,
% 3.77/0.99      ( ~ v1_relat_1(X0)
% 3.77/0.99      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 3.77/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_711,plain,
% 3.77/0.99      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
% 3.77/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1151,plain,
% 3.77/0.99      ( k10_relat_1(k7_relat_1(X0,X1),k2_relat_1(k7_relat_1(X0,X1))) = k1_relat_1(k7_relat_1(X0,X1))
% 3.77/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_714,c_711]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_7862,plain,
% 3.77/0.99      ( k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0))) = k1_relat_1(k7_relat_1(sK1,X0)) ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_702,c_1151]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_8,plain,
% 3.77/0.99      ( ~ v1_relat_1(X0)
% 3.77/0.99      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 3.77/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_713,plain,
% 3.77/0.99      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 3.77/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1476,plain,
% 3.77/0.99      ( k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_702,c_713]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_7864,plain,
% 3.77/0.99      ( k10_relat_1(k7_relat_1(sK1,X0),k9_relat_1(sK1,X0)) = k1_relat_1(k7_relat_1(sK1,X0)) ),
% 3.77/0.99      inference(light_normalisation,[status(thm)],[c_7862,c_1476]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_16,plain,
% 3.77/0.99      ( ~ v1_relat_1(X0)
% 3.77/0.99      | k3_xboole_0(X1,k10_relat_1(X0,X2)) = k10_relat_1(k7_relat_1(X0,X1),X2) ),
% 3.77/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_705,plain,
% 3.77/0.99      ( k3_xboole_0(X0,k10_relat_1(X1,X2)) = k10_relat_1(k7_relat_1(X1,X0),X2)
% 3.77/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1300,plain,
% 3.77/0.99      ( k3_xboole_0(X0,k10_relat_1(k7_relat_1(X1,X2),X3)) = k10_relat_1(k7_relat_1(k7_relat_1(X1,X2),X0),X3)
% 3.77/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_714,c_705]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_10094,plain,
% 3.77/0.99      ( k3_xboole_0(X0,k10_relat_1(k7_relat_1(sK1,X1),X2)) = k10_relat_1(k7_relat_1(k7_relat_1(sK1,X1),X0),X2) ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_702,c_1300]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_10547,plain,
% 3.77/0.99      ( k10_relat_1(k7_relat_1(k7_relat_1(sK1,X0),X1),k9_relat_1(sK1,X0)) = k3_xboole_0(X1,k1_relat_1(k7_relat_1(sK1,X0))) ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_7864,c_10094]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_10989,plain,
% 3.77/0.99      ( k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)) = k3_xboole_0(sK0,k1_relat_1(k7_relat_1(sK1,sK0))) ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_9664,c_10547]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_11037,plain,
% 3.77/0.99      ( k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)) = k3_xboole_0(sK0,sK0) ),
% 3.77/0.99      inference(light_normalisation,[status(thm)],[c_10989,c_3751]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_13,plain,
% 3.77/0.99      ( ~ v1_relat_1(X0)
% 3.77/0.99      | k3_xboole_0(k1_relat_1(X0),X1) = k1_relat_1(k7_relat_1(X0,X1)) ),
% 3.77/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_708,plain,
% 3.77/0.99      ( k3_xboole_0(k1_relat_1(X0),X1) = k1_relat_1(k7_relat_1(X0,X1))
% 3.77/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_2013,plain,
% 3.77/0.99      ( k3_xboole_0(k1_relat_1(sK1),X0) = k1_relat_1(k7_relat_1(sK1,X0)) ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_702,c_708]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_9667,plain,
% 3.77/0.99      ( k7_relat_1(k7_relat_1(sK1,sK0),k1_relat_1(sK1)) = k7_relat_1(sK1,sK0) ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_703,c_9657]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_10988,plain,
% 3.77/0.99      ( k3_xboole_0(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) = k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)) ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_9667,c_10547]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_11039,plain,
% 3.77/0.99      ( k3_xboole_0(k1_relat_1(sK1),k1_relat_1(k7_relat_1(sK1,sK0))) = k3_xboole_0(sK0,sK0) ),
% 3.77/0.99      inference(light_normalisation,[status(thm)],[c_10988,c_11037]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_11041,plain,
% 3.77/0.99      ( k3_xboole_0(k1_relat_1(sK1),sK0) = k3_xboole_0(sK0,sK0) ),
% 3.77/0.99      inference(light_normalisation,[status(thm)],[c_11039,c_3751]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_11217,plain,
% 3.77/0.99      ( k1_relat_1(k7_relat_1(sK1,sK0)) = k3_xboole_0(sK0,sK0) ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_2013,c_11041]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_11219,plain,
% 3.77/0.99      ( k3_xboole_0(sK0,sK0) = sK0 ),
% 3.77/0.99      inference(light_normalisation,[status(thm)],[c_11217,c_3751]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_12012,plain,
% 3.77/0.99      ( k10_relat_1(k7_relat_1(sK1,sK0),k9_relat_1(sK1,sK0)) = sK0 ),
% 3.77/0.99      inference(light_normalisation,[status(thm)],[c_11037,c_11219]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_1301,plain,
% 3.77/0.99      ( k3_xboole_0(X0,k10_relat_1(sK1,X1)) = k10_relat_1(k7_relat_1(sK1,X0),X1) ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_702,c_705]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_2012,plain,
% 3.77/0.99      ( k3_xboole_0(k1_relat_1(k7_relat_1(X0,X1)),X2) = k1_relat_1(k7_relat_1(k7_relat_1(X0,X1),X2))
% 3.77/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_714,c_708]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_12824,plain,
% 3.77/0.99      ( k3_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)),X1) = k1_relat_1(k7_relat_1(k7_relat_1(sK1,X0),X1)) ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_702,c_2012]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_12838,plain,
% 3.77/0.99      ( k1_relat_1(k7_relat_1(k7_relat_1(sK1,sK0),X0)) = k3_xboole_0(sK0,X0) ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_3751,c_12824]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_12,plain,
% 3.77/0.99      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 3.77/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_709,plain,
% 3.77/0.99      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
% 3.77/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_13520,plain,
% 3.77/0.99      ( r1_tarski(k3_xboole_0(sK0,X0),X0) = iProver_top
% 3.77/0.99      | v1_relat_1(k7_relat_1(sK1,sK0)) != iProver_top ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_12838,c_709]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_14585,plain,
% 3.77/0.99      ( r1_tarski(k3_xboole_0(sK0,X0),X0) = iProver_top ),
% 3.77/0.99      inference(global_propositional_subsumption,
% 3.77/0.99                [status(thm)],
% 3.77/0.99                [c_13520,c_20,c_3915]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_14592,plain,
% 3.77/0.99      ( r1_tarski(k10_relat_1(k7_relat_1(sK1,sK0),X0),k10_relat_1(sK1,X0)) = iProver_top ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_1301,c_14585]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_14952,plain,
% 3.77/0.99      ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) = iProver_top ),
% 3.77/0.99      inference(superposition,[status(thm)],[c_12012,c_14592]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_17,negated_conjecture,
% 3.77/0.99      ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
% 3.77/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(c_22,plain,
% 3.77/0.99      ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) != iProver_top ),
% 3.77/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.77/0.99  
% 3.77/0.99  cnf(contradiction,plain,
% 3.77/0.99      ( $false ),
% 3.77/0.99      inference(minisat,[status(thm)],[c_14952,c_22]) ).
% 3.77/0.99  
% 3.77/0.99  
% 3.77/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.77/0.99  
% 3.77/0.99  ------                               Statistics
% 3.77/0.99  
% 3.77/0.99  ------ Selected
% 3.77/0.99  
% 3.77/0.99  total_time:                             0.48
% 3.77/0.99  
%------------------------------------------------------------------------------
