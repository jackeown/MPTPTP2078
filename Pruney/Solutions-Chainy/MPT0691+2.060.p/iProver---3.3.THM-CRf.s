%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:51:48 EST 2020

% Result     : Theorem 2.60s
% Output     : CNFRefutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 221 expanded)
%              Number of clauses        :   46 (  73 expanded)
%              Number of leaves         :   14 (  46 expanded)
%              Depth                    :   15
%              Number of atoms          :  179 ( 499 expanded)
%              Number of equality atoms :   89 ( 141 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k1_relat_1(X1))
         => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f28,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f29,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f33,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
      & r1_tarski(sK0,k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    & r1_tarski(sK0,k1_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f33])).

fof(f56,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f34])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f55,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f50,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f66,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f36])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)
          | ~ r1_tarski(X1,X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f52,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,k10_relat_1(X2,X1))) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f54,f44])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f60,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f41,f44])).

fof(f5,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f62,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f42,f44])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f57,plain,(
    ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_17,negated_conjecture,
    ( r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_660,plain,
    ( r1_tarski(sK0,k1_relat_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_663,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1723,plain,
    ( k1_relat_1(k7_relat_1(sK1,sK0)) = sK0
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_660,c_663])).

cnf(c_18,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_783,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | k1_relat_1(k7_relat_1(sK1,X0)) = X0 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_876,plain,
    ( ~ r1_tarski(sK0,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | k1_relat_1(k7_relat_1(sK1,sK0)) = sK0 ),
    inference(instantiation,[status(thm)],[c_783])).

cnf(c_2301,plain,
    ( k1_relat_1(k7_relat_1(sK1,sK0)) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1723,c_18,c_17,c_876])).

cnf(c_659,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_667,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_666,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1821,plain,
    ( k9_relat_1(k7_relat_1(X0,X1),k1_relat_1(k7_relat_1(X0,X1))) = k2_relat_1(k7_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_667,c_666])).

cnf(c_4600,plain,
    ( k9_relat_1(k7_relat_1(sK1,X0),k1_relat_1(k7_relat_1(sK1,X0))) = k2_relat_1(k7_relat_1(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_659,c_1821])).

cnf(c_4983,plain,
    ( k9_relat_1(k7_relat_1(sK1,sK0),sK0) = k2_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_2301,c_4600])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_670,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X2)
    | k9_relat_1(k7_relat_1(X2,X1),X0) = k9_relat_1(X2,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_665,plain,
    ( k9_relat_1(k7_relat_1(X0,X1),X2) = k9_relat_1(X0,X2)
    | r1_tarski(X2,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2050,plain,
    ( k9_relat_1(k7_relat_1(X0,X1),X1) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_670,c_665])).

cnf(c_2824,plain,
    ( k9_relat_1(k7_relat_1(sK1,X0),X0) = k9_relat_1(sK1,X0) ),
    inference(superposition,[status(thm)],[c_659,c_2050])).

cnf(c_4985,plain,
    ( k2_relat_1(k7_relat_1(sK1,sK0)) = k9_relat_1(sK1,sK0) ),
    inference(demodulation,[status(thm)],[c_4983,c_2824])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_664,plain,
    ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1807,plain,
    ( k10_relat_1(k7_relat_1(X0,X1),k2_relat_1(k7_relat_1(X0,X1))) = k1_relat_1(k7_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_667,c_664])).

cnf(c_3772,plain,
    ( k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0))) = k1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_659,c_1807])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | k4_xboole_0(X1,k4_xboole_0(X1,k10_relat_1(X0,X2))) = k10_relat_1(k7_relat_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_662,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k10_relat_1(X1,X2))) = k10_relat_1(k7_relat_1(X1,X0),X2)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1043,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k10_relat_1(sK1,X1))) = k10_relat_1(k7_relat_1(sK1,X0),X1) ),
    inference(superposition,[status(thm)],[c_659,c_662])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1222,plain,
    ( k5_xboole_0(X0,k10_relat_1(k7_relat_1(sK1,X0),X1)) = k4_xboole_0(X0,k10_relat_1(sK1,X1)) ),
    inference(superposition,[status(thm)],[c_1043,c_0])).

cnf(c_4018,plain,
    ( k4_xboole_0(X0,k10_relat_1(sK1,k2_relat_1(k7_relat_1(sK1,X0)))) = k5_xboole_0(X0,k1_relat_1(k7_relat_1(sK1,X0))) ),
    inference(superposition,[status(thm)],[c_3772,c_1222])).

cnf(c_4993,plain,
    ( k4_xboole_0(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) = k5_xboole_0(sK0,k1_relat_1(k7_relat_1(sK1,sK0))) ),
    inference(superposition,[status(thm)],[c_4985,c_4018])).

cnf(c_4999,plain,
    ( k4_xboole_0(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) = k5_xboole_0(sK0,sK0) ),
    inference(light_normalisation,[status(thm)],[c_4993,c_2301])).

cnf(c_7,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_8,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_680,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_7,c_8])).

cnf(c_923,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_680,c_0])).

cnf(c_929,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_923,c_8,c_680])).

cnf(c_5000,plain,
    ( k4_xboole_0(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4999,c_929])).

cnf(c_6,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_765,plain,
    ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
    | k4_xboole_0(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_16,negated_conjecture,
    ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f57])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5000,c_765,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:22:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.60/1.04  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.60/1.04  
% 2.60/1.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.60/1.04  
% 2.60/1.04  ------  iProver source info
% 2.60/1.04  
% 2.60/1.04  git: date: 2020-06-30 10:37:57 +0100
% 2.60/1.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.60/1.04  git: non_committed_changes: false
% 2.60/1.04  git: last_make_outside_of_git: false
% 2.60/1.04  
% 2.60/1.04  ------ 
% 2.60/1.04  
% 2.60/1.04  ------ Input Options
% 2.60/1.04  
% 2.60/1.04  --out_options                           all
% 2.60/1.04  --tptp_safe_out                         true
% 2.60/1.04  --problem_path                          ""
% 2.60/1.04  --include_path                          ""
% 2.60/1.04  --clausifier                            res/vclausify_rel
% 2.60/1.04  --clausifier_options                    --mode clausify
% 2.60/1.04  --stdin                                 false
% 2.60/1.04  --stats_out                             all
% 2.60/1.04  
% 2.60/1.04  ------ General Options
% 2.60/1.04  
% 2.60/1.04  --fof                                   false
% 2.60/1.04  --time_out_real                         305.
% 2.60/1.04  --time_out_virtual                      -1.
% 2.60/1.04  --symbol_type_check                     false
% 2.60/1.04  --clausify_out                          false
% 2.60/1.04  --sig_cnt_out                           false
% 2.60/1.04  --trig_cnt_out                          false
% 2.60/1.04  --trig_cnt_out_tolerance                1.
% 2.60/1.04  --trig_cnt_out_sk_spl                   false
% 2.60/1.04  --abstr_cl_out                          false
% 2.60/1.04  
% 2.60/1.04  ------ Global Options
% 2.60/1.04  
% 2.60/1.04  --schedule                              default
% 2.60/1.04  --add_important_lit                     false
% 2.60/1.04  --prop_solver_per_cl                    1000
% 2.60/1.04  --min_unsat_core                        false
% 2.60/1.04  --soft_assumptions                      false
% 2.60/1.04  --soft_lemma_size                       3
% 2.60/1.04  --prop_impl_unit_size                   0
% 2.60/1.04  --prop_impl_unit                        []
% 2.60/1.04  --share_sel_clauses                     true
% 2.60/1.04  --reset_solvers                         false
% 2.60/1.04  --bc_imp_inh                            [conj_cone]
% 2.60/1.04  --conj_cone_tolerance                   3.
% 2.60/1.04  --extra_neg_conj                        none
% 2.60/1.04  --large_theory_mode                     true
% 2.60/1.04  --prolific_symb_bound                   200
% 2.60/1.04  --lt_threshold                          2000
% 2.60/1.04  --clause_weak_htbl                      true
% 2.60/1.04  --gc_record_bc_elim                     false
% 2.60/1.04  
% 2.60/1.04  ------ Preprocessing Options
% 2.60/1.04  
% 2.60/1.04  --preprocessing_flag                    true
% 2.60/1.04  --time_out_prep_mult                    0.1
% 2.60/1.04  --splitting_mode                        input
% 2.60/1.04  --splitting_grd                         true
% 2.60/1.04  --splitting_cvd                         false
% 2.60/1.04  --splitting_cvd_svl                     false
% 2.60/1.04  --splitting_nvd                         32
% 2.60/1.04  --sub_typing                            true
% 2.60/1.04  --prep_gs_sim                           true
% 2.60/1.04  --prep_unflatten                        true
% 2.60/1.04  --prep_res_sim                          true
% 2.60/1.04  --prep_upred                            true
% 2.60/1.04  --prep_sem_filter                       exhaustive
% 2.60/1.04  --prep_sem_filter_out                   false
% 2.60/1.04  --pred_elim                             true
% 2.60/1.04  --res_sim_input                         true
% 2.60/1.04  --eq_ax_congr_red                       true
% 2.60/1.04  --pure_diseq_elim                       true
% 2.60/1.04  --brand_transform                       false
% 2.60/1.04  --non_eq_to_eq                          false
% 2.60/1.04  --prep_def_merge                        true
% 2.60/1.04  --prep_def_merge_prop_impl              false
% 2.60/1.04  --prep_def_merge_mbd                    true
% 2.60/1.04  --prep_def_merge_tr_red                 false
% 2.60/1.04  --prep_def_merge_tr_cl                  false
% 2.60/1.04  --smt_preprocessing                     true
% 2.60/1.04  --smt_ac_axioms                         fast
% 2.60/1.04  --preprocessed_out                      false
% 2.60/1.04  --preprocessed_stats                    false
% 2.60/1.04  
% 2.60/1.04  ------ Abstraction refinement Options
% 2.60/1.04  
% 2.60/1.04  --abstr_ref                             []
% 2.60/1.04  --abstr_ref_prep                        false
% 2.60/1.04  --abstr_ref_until_sat                   false
% 2.60/1.04  --abstr_ref_sig_restrict                funpre
% 2.60/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 2.60/1.04  --abstr_ref_under                       []
% 2.60/1.04  
% 2.60/1.04  ------ SAT Options
% 2.60/1.04  
% 2.60/1.04  --sat_mode                              false
% 2.60/1.04  --sat_fm_restart_options                ""
% 2.60/1.04  --sat_gr_def                            false
% 2.60/1.04  --sat_epr_types                         true
% 2.60/1.04  --sat_non_cyclic_types                  false
% 2.60/1.04  --sat_finite_models                     false
% 2.60/1.04  --sat_fm_lemmas                         false
% 2.60/1.04  --sat_fm_prep                           false
% 2.60/1.04  --sat_fm_uc_incr                        true
% 2.60/1.04  --sat_out_model                         small
% 2.60/1.04  --sat_out_clauses                       false
% 2.60/1.04  
% 2.60/1.04  ------ QBF Options
% 2.60/1.04  
% 2.60/1.04  --qbf_mode                              false
% 2.60/1.04  --qbf_elim_univ                         false
% 2.60/1.04  --qbf_dom_inst                          none
% 2.60/1.04  --qbf_dom_pre_inst                      false
% 2.60/1.04  --qbf_sk_in                             false
% 2.60/1.04  --qbf_pred_elim                         true
% 2.60/1.04  --qbf_split                             512
% 2.60/1.04  
% 2.60/1.04  ------ BMC1 Options
% 2.60/1.04  
% 2.60/1.04  --bmc1_incremental                      false
% 2.60/1.04  --bmc1_axioms                           reachable_all
% 2.60/1.04  --bmc1_min_bound                        0
% 2.60/1.04  --bmc1_max_bound                        -1
% 2.60/1.04  --bmc1_max_bound_default                -1
% 2.60/1.04  --bmc1_symbol_reachability              true
% 2.60/1.04  --bmc1_property_lemmas                  false
% 2.60/1.04  --bmc1_k_induction                      false
% 2.60/1.04  --bmc1_non_equiv_states                 false
% 2.60/1.04  --bmc1_deadlock                         false
% 2.60/1.04  --bmc1_ucm                              false
% 2.60/1.04  --bmc1_add_unsat_core                   none
% 2.60/1.05  --bmc1_unsat_core_children              false
% 2.60/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 2.60/1.05  --bmc1_out_stat                         full
% 2.60/1.05  --bmc1_ground_init                      false
% 2.60/1.05  --bmc1_pre_inst_next_state              false
% 2.60/1.05  --bmc1_pre_inst_state                   false
% 2.60/1.05  --bmc1_pre_inst_reach_state             false
% 2.60/1.05  --bmc1_out_unsat_core                   false
% 2.60/1.05  --bmc1_aig_witness_out                  false
% 2.60/1.05  --bmc1_verbose                          false
% 2.60/1.05  --bmc1_dump_clauses_tptp                false
% 2.60/1.05  --bmc1_dump_unsat_core_tptp             false
% 2.60/1.05  --bmc1_dump_file                        -
% 2.60/1.05  --bmc1_ucm_expand_uc_limit              128
% 2.60/1.05  --bmc1_ucm_n_expand_iterations          6
% 2.60/1.05  --bmc1_ucm_extend_mode                  1
% 2.60/1.05  --bmc1_ucm_init_mode                    2
% 2.60/1.05  --bmc1_ucm_cone_mode                    none
% 2.60/1.05  --bmc1_ucm_reduced_relation_type        0
% 2.60/1.05  --bmc1_ucm_relax_model                  4
% 2.60/1.05  --bmc1_ucm_full_tr_after_sat            true
% 2.60/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 2.60/1.05  --bmc1_ucm_layered_model                none
% 2.60/1.05  --bmc1_ucm_max_lemma_size               10
% 2.60/1.05  
% 2.60/1.05  ------ AIG Options
% 2.60/1.05  
% 2.60/1.05  --aig_mode                              false
% 2.60/1.05  
% 2.60/1.05  ------ Instantiation Options
% 2.60/1.05  
% 2.60/1.05  --instantiation_flag                    true
% 2.60/1.05  --inst_sos_flag                         false
% 2.60/1.05  --inst_sos_phase                        true
% 2.60/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.60/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.60/1.05  --inst_lit_sel_side                     num_symb
% 2.60/1.05  --inst_solver_per_active                1400
% 2.60/1.05  --inst_solver_calls_frac                1.
% 2.60/1.05  --inst_passive_queue_type               priority_queues
% 2.60/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.60/1.05  --inst_passive_queues_freq              [25;2]
% 2.60/1.05  --inst_dismatching                      true
% 2.60/1.05  --inst_eager_unprocessed_to_passive     true
% 2.60/1.05  --inst_prop_sim_given                   true
% 2.60/1.05  --inst_prop_sim_new                     false
% 2.60/1.05  --inst_subs_new                         false
% 2.60/1.05  --inst_eq_res_simp                      false
% 2.60/1.05  --inst_subs_given                       false
% 2.60/1.05  --inst_orphan_elimination               true
% 2.60/1.05  --inst_learning_loop_flag               true
% 2.60/1.05  --inst_learning_start                   3000
% 2.60/1.05  --inst_learning_factor                  2
% 2.60/1.05  --inst_start_prop_sim_after_learn       3
% 2.60/1.05  --inst_sel_renew                        solver
% 2.60/1.05  --inst_lit_activity_flag                true
% 2.60/1.05  --inst_restr_to_given                   false
% 2.60/1.05  --inst_activity_threshold               500
% 2.60/1.05  --inst_out_proof                        true
% 2.60/1.05  
% 2.60/1.05  ------ Resolution Options
% 2.60/1.05  
% 2.60/1.05  --resolution_flag                       true
% 2.60/1.05  --res_lit_sel                           adaptive
% 2.60/1.05  --res_lit_sel_side                      none
% 2.60/1.05  --res_ordering                          kbo
% 2.60/1.05  --res_to_prop_solver                    active
% 2.60/1.05  --res_prop_simpl_new                    false
% 2.60/1.05  --res_prop_simpl_given                  true
% 2.60/1.05  --res_passive_queue_type                priority_queues
% 2.60/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.60/1.05  --res_passive_queues_freq               [15;5]
% 2.60/1.05  --res_forward_subs                      full
% 2.60/1.05  --res_backward_subs                     full
% 2.60/1.05  --res_forward_subs_resolution           true
% 2.60/1.05  --res_backward_subs_resolution          true
% 2.60/1.05  --res_orphan_elimination                true
% 2.60/1.05  --res_time_limit                        2.
% 2.60/1.05  --res_out_proof                         true
% 2.60/1.05  
% 2.60/1.05  ------ Superposition Options
% 2.60/1.05  
% 2.60/1.05  --superposition_flag                    true
% 2.60/1.05  --sup_passive_queue_type                priority_queues
% 2.60/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.60/1.05  --sup_passive_queues_freq               [8;1;4]
% 2.60/1.05  --demod_completeness_check              fast
% 2.60/1.05  --demod_use_ground                      true
% 2.60/1.05  --sup_to_prop_solver                    passive
% 2.60/1.05  --sup_prop_simpl_new                    true
% 2.60/1.05  --sup_prop_simpl_given                  true
% 2.60/1.05  --sup_fun_splitting                     false
% 2.60/1.05  --sup_smt_interval                      50000
% 2.60/1.05  
% 2.60/1.05  ------ Superposition Simplification Setup
% 2.60/1.05  
% 2.60/1.05  --sup_indices_passive                   []
% 2.60/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.60/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.60/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.60/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 2.60/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.60/1.05  --sup_full_bw                           [BwDemod]
% 2.60/1.05  --sup_immed_triv                        [TrivRules]
% 2.60/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.60/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.60/1.05  --sup_immed_bw_main                     []
% 2.60/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.60/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 2.60/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.60/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.60/1.05  
% 2.60/1.05  ------ Combination Options
% 2.60/1.05  
% 2.60/1.05  --comb_res_mult                         3
% 2.60/1.05  --comb_sup_mult                         2
% 2.60/1.05  --comb_inst_mult                        10
% 2.60/1.05  
% 2.60/1.05  ------ Debug Options
% 2.60/1.05  
% 2.60/1.05  --dbg_backtrace                         false
% 2.60/1.05  --dbg_dump_prop_clauses                 false
% 2.60/1.05  --dbg_dump_prop_clauses_file            -
% 2.60/1.05  --dbg_out_stat                          false
% 2.60/1.05  ------ Parsing...
% 2.60/1.05  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.60/1.05  
% 2.60/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.60/1.05  
% 2.60/1.05  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.60/1.05  
% 2.60/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.60/1.05  ------ Proving...
% 2.60/1.05  ------ Problem Properties 
% 2.60/1.05  
% 2.60/1.05  
% 2.60/1.05  clauses                                 18
% 2.60/1.05  conjectures                             3
% 2.60/1.05  EPR                                     3
% 2.60/1.05  Horn                                    18
% 2.60/1.05  unary                                   9
% 2.60/1.05  binary                                  6
% 2.60/1.05  lits                                    30
% 2.60/1.05  lits eq                                 13
% 2.60/1.05  fd_pure                                 0
% 2.60/1.05  fd_pseudo                               0
% 2.60/1.05  fd_cond                                 0
% 2.60/1.05  fd_pseudo_cond                          1
% 2.60/1.05  AC symbols                              0
% 2.60/1.05  
% 2.60/1.05  ------ Schedule dynamic 5 is on 
% 2.60/1.05  
% 2.60/1.05  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.60/1.05  
% 2.60/1.05  
% 2.60/1.05  ------ 
% 2.60/1.05  Current options:
% 2.60/1.05  ------ 
% 2.60/1.05  
% 2.60/1.05  ------ Input Options
% 2.60/1.05  
% 2.60/1.05  --out_options                           all
% 2.60/1.05  --tptp_safe_out                         true
% 2.60/1.05  --problem_path                          ""
% 2.60/1.05  --include_path                          ""
% 2.60/1.05  --clausifier                            res/vclausify_rel
% 2.60/1.05  --clausifier_options                    --mode clausify
% 2.60/1.05  --stdin                                 false
% 2.60/1.05  --stats_out                             all
% 2.60/1.05  
% 2.60/1.05  ------ General Options
% 2.60/1.05  
% 2.60/1.05  --fof                                   false
% 2.60/1.05  --time_out_real                         305.
% 2.60/1.05  --time_out_virtual                      -1.
% 2.60/1.05  --symbol_type_check                     false
% 2.60/1.05  --clausify_out                          false
% 2.60/1.05  --sig_cnt_out                           false
% 2.60/1.05  --trig_cnt_out                          false
% 2.60/1.05  --trig_cnt_out_tolerance                1.
% 2.60/1.05  --trig_cnt_out_sk_spl                   false
% 2.60/1.05  --abstr_cl_out                          false
% 2.60/1.05  
% 2.60/1.05  ------ Global Options
% 2.60/1.05  
% 2.60/1.05  --schedule                              default
% 2.60/1.05  --add_important_lit                     false
% 2.60/1.05  --prop_solver_per_cl                    1000
% 2.60/1.05  --min_unsat_core                        false
% 2.60/1.05  --soft_assumptions                      false
% 2.60/1.05  --soft_lemma_size                       3
% 2.60/1.05  --prop_impl_unit_size                   0
% 2.60/1.05  --prop_impl_unit                        []
% 2.60/1.05  --share_sel_clauses                     true
% 2.60/1.05  --reset_solvers                         false
% 2.60/1.05  --bc_imp_inh                            [conj_cone]
% 2.60/1.05  --conj_cone_tolerance                   3.
% 2.60/1.05  --extra_neg_conj                        none
% 2.60/1.05  --large_theory_mode                     true
% 2.60/1.05  --prolific_symb_bound                   200
% 2.60/1.05  --lt_threshold                          2000
% 2.60/1.05  --clause_weak_htbl                      true
% 2.60/1.05  --gc_record_bc_elim                     false
% 2.60/1.05  
% 2.60/1.05  ------ Preprocessing Options
% 2.60/1.05  
% 2.60/1.05  --preprocessing_flag                    true
% 2.60/1.05  --time_out_prep_mult                    0.1
% 2.60/1.05  --splitting_mode                        input
% 2.60/1.05  --splitting_grd                         true
% 2.60/1.05  --splitting_cvd                         false
% 2.60/1.05  --splitting_cvd_svl                     false
% 2.60/1.05  --splitting_nvd                         32
% 2.60/1.05  --sub_typing                            true
% 2.60/1.05  --prep_gs_sim                           true
% 2.60/1.05  --prep_unflatten                        true
% 2.60/1.05  --prep_res_sim                          true
% 2.60/1.05  --prep_upred                            true
% 2.60/1.05  --prep_sem_filter                       exhaustive
% 2.60/1.05  --prep_sem_filter_out                   false
% 2.60/1.05  --pred_elim                             true
% 2.60/1.05  --res_sim_input                         true
% 2.60/1.05  --eq_ax_congr_red                       true
% 2.60/1.05  --pure_diseq_elim                       true
% 2.60/1.05  --brand_transform                       false
% 2.60/1.05  --non_eq_to_eq                          false
% 2.60/1.05  --prep_def_merge                        true
% 2.60/1.05  --prep_def_merge_prop_impl              false
% 2.60/1.05  --prep_def_merge_mbd                    true
% 2.60/1.05  --prep_def_merge_tr_red                 false
% 2.60/1.05  --prep_def_merge_tr_cl                  false
% 2.60/1.05  --smt_preprocessing                     true
% 2.60/1.05  --smt_ac_axioms                         fast
% 2.60/1.05  --preprocessed_out                      false
% 2.60/1.05  --preprocessed_stats                    false
% 2.60/1.05  
% 2.60/1.05  ------ Abstraction refinement Options
% 2.60/1.05  
% 2.60/1.05  --abstr_ref                             []
% 2.60/1.05  --abstr_ref_prep                        false
% 2.60/1.05  --abstr_ref_until_sat                   false
% 2.60/1.05  --abstr_ref_sig_restrict                funpre
% 2.60/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 2.60/1.05  --abstr_ref_under                       []
% 2.60/1.05  
% 2.60/1.05  ------ SAT Options
% 2.60/1.05  
% 2.60/1.05  --sat_mode                              false
% 2.60/1.05  --sat_fm_restart_options                ""
% 2.60/1.05  --sat_gr_def                            false
% 2.60/1.05  --sat_epr_types                         true
% 2.60/1.05  --sat_non_cyclic_types                  false
% 2.60/1.05  --sat_finite_models                     false
% 2.60/1.05  --sat_fm_lemmas                         false
% 2.60/1.05  --sat_fm_prep                           false
% 2.60/1.05  --sat_fm_uc_incr                        true
% 2.60/1.05  --sat_out_model                         small
% 2.60/1.05  --sat_out_clauses                       false
% 2.60/1.05  
% 2.60/1.05  ------ QBF Options
% 2.60/1.05  
% 2.60/1.05  --qbf_mode                              false
% 2.60/1.05  --qbf_elim_univ                         false
% 2.60/1.05  --qbf_dom_inst                          none
% 2.60/1.05  --qbf_dom_pre_inst                      false
% 2.60/1.05  --qbf_sk_in                             false
% 2.60/1.05  --qbf_pred_elim                         true
% 2.60/1.05  --qbf_split                             512
% 2.60/1.05  
% 2.60/1.05  ------ BMC1 Options
% 2.60/1.05  
% 2.60/1.05  --bmc1_incremental                      false
% 2.60/1.05  --bmc1_axioms                           reachable_all
% 2.60/1.05  --bmc1_min_bound                        0
% 2.60/1.05  --bmc1_max_bound                        -1
% 2.60/1.05  --bmc1_max_bound_default                -1
% 2.60/1.05  --bmc1_symbol_reachability              true
% 2.60/1.05  --bmc1_property_lemmas                  false
% 2.60/1.05  --bmc1_k_induction                      false
% 2.60/1.05  --bmc1_non_equiv_states                 false
% 2.60/1.05  --bmc1_deadlock                         false
% 2.60/1.05  --bmc1_ucm                              false
% 2.60/1.05  --bmc1_add_unsat_core                   none
% 2.60/1.05  --bmc1_unsat_core_children              false
% 2.60/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 2.60/1.05  --bmc1_out_stat                         full
% 2.60/1.05  --bmc1_ground_init                      false
% 2.60/1.05  --bmc1_pre_inst_next_state              false
% 2.60/1.05  --bmc1_pre_inst_state                   false
% 2.60/1.05  --bmc1_pre_inst_reach_state             false
% 2.60/1.05  --bmc1_out_unsat_core                   false
% 2.60/1.05  --bmc1_aig_witness_out                  false
% 2.60/1.05  --bmc1_verbose                          false
% 2.60/1.05  --bmc1_dump_clauses_tptp                false
% 2.60/1.05  --bmc1_dump_unsat_core_tptp             false
% 2.60/1.05  --bmc1_dump_file                        -
% 2.60/1.05  --bmc1_ucm_expand_uc_limit              128
% 2.60/1.05  --bmc1_ucm_n_expand_iterations          6
% 2.60/1.05  --bmc1_ucm_extend_mode                  1
% 2.60/1.05  --bmc1_ucm_init_mode                    2
% 2.60/1.05  --bmc1_ucm_cone_mode                    none
% 2.60/1.05  --bmc1_ucm_reduced_relation_type        0
% 2.60/1.05  --bmc1_ucm_relax_model                  4
% 2.60/1.05  --bmc1_ucm_full_tr_after_sat            true
% 2.60/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 2.60/1.05  --bmc1_ucm_layered_model                none
% 2.60/1.05  --bmc1_ucm_max_lemma_size               10
% 2.60/1.05  
% 2.60/1.05  ------ AIG Options
% 2.60/1.05  
% 2.60/1.05  --aig_mode                              false
% 2.60/1.05  
% 2.60/1.05  ------ Instantiation Options
% 2.60/1.05  
% 2.60/1.05  --instantiation_flag                    true
% 2.60/1.05  --inst_sos_flag                         false
% 2.60/1.05  --inst_sos_phase                        true
% 2.60/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.60/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.60/1.05  --inst_lit_sel_side                     none
% 2.60/1.05  --inst_solver_per_active                1400
% 2.60/1.05  --inst_solver_calls_frac                1.
% 2.60/1.05  --inst_passive_queue_type               priority_queues
% 2.60/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.60/1.05  --inst_passive_queues_freq              [25;2]
% 2.60/1.05  --inst_dismatching                      true
% 2.60/1.05  --inst_eager_unprocessed_to_passive     true
% 2.60/1.05  --inst_prop_sim_given                   true
% 2.60/1.05  --inst_prop_sim_new                     false
% 2.60/1.05  --inst_subs_new                         false
% 2.60/1.05  --inst_eq_res_simp                      false
% 2.60/1.05  --inst_subs_given                       false
% 2.60/1.05  --inst_orphan_elimination               true
% 2.60/1.05  --inst_learning_loop_flag               true
% 2.60/1.05  --inst_learning_start                   3000
% 2.60/1.05  --inst_learning_factor                  2
% 2.60/1.05  --inst_start_prop_sim_after_learn       3
% 2.60/1.05  --inst_sel_renew                        solver
% 2.60/1.05  --inst_lit_activity_flag                true
% 2.60/1.05  --inst_restr_to_given                   false
% 2.60/1.05  --inst_activity_threshold               500
% 2.60/1.05  --inst_out_proof                        true
% 2.60/1.05  
% 2.60/1.05  ------ Resolution Options
% 2.60/1.05  
% 2.60/1.05  --resolution_flag                       false
% 2.60/1.05  --res_lit_sel                           adaptive
% 2.60/1.05  --res_lit_sel_side                      none
% 2.60/1.05  --res_ordering                          kbo
% 2.60/1.05  --res_to_prop_solver                    active
% 2.60/1.05  --res_prop_simpl_new                    false
% 2.60/1.05  --res_prop_simpl_given                  true
% 2.60/1.05  --res_passive_queue_type                priority_queues
% 2.60/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.60/1.05  --res_passive_queues_freq               [15;5]
% 2.60/1.05  --res_forward_subs                      full
% 2.60/1.05  --res_backward_subs                     full
% 2.60/1.05  --res_forward_subs_resolution           true
% 2.60/1.05  --res_backward_subs_resolution          true
% 2.60/1.05  --res_orphan_elimination                true
% 2.60/1.05  --res_time_limit                        2.
% 2.60/1.05  --res_out_proof                         true
% 2.60/1.05  
% 2.60/1.05  ------ Superposition Options
% 2.60/1.05  
% 2.60/1.05  --superposition_flag                    true
% 2.60/1.05  --sup_passive_queue_type                priority_queues
% 2.60/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.60/1.05  --sup_passive_queues_freq               [8;1;4]
% 2.60/1.05  --demod_completeness_check              fast
% 2.60/1.05  --demod_use_ground                      true
% 2.60/1.05  --sup_to_prop_solver                    passive
% 2.60/1.05  --sup_prop_simpl_new                    true
% 2.60/1.05  --sup_prop_simpl_given                  true
% 2.60/1.05  --sup_fun_splitting                     false
% 2.60/1.05  --sup_smt_interval                      50000
% 2.60/1.05  
% 2.60/1.05  ------ Superposition Simplification Setup
% 2.60/1.05  
% 2.60/1.05  --sup_indices_passive                   []
% 2.60/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.60/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.60/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.60/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 2.60/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.60/1.05  --sup_full_bw                           [BwDemod]
% 2.60/1.05  --sup_immed_triv                        [TrivRules]
% 2.60/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.60/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.60/1.05  --sup_immed_bw_main                     []
% 2.60/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.60/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 2.60/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.60/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.60/1.05  
% 2.60/1.05  ------ Combination Options
% 2.60/1.05  
% 2.60/1.05  --comb_res_mult                         3
% 2.60/1.05  --comb_sup_mult                         2
% 2.60/1.05  --comb_inst_mult                        10
% 2.60/1.05  
% 2.60/1.05  ------ Debug Options
% 2.60/1.05  
% 2.60/1.05  --dbg_backtrace                         false
% 2.60/1.05  --dbg_dump_prop_clauses                 false
% 2.60/1.05  --dbg_dump_prop_clauses_file            -
% 2.60/1.05  --dbg_out_stat                          false
% 2.60/1.05  
% 2.60/1.05  
% 2.60/1.05  
% 2.60/1.05  
% 2.60/1.05  ------ Proving...
% 2.60/1.05  
% 2.60/1.05  
% 2.60/1.05  % SZS status Theorem for theBenchmark.p
% 2.60/1.05  
% 2.60/1.05  % SZS output start CNFRefutation for theBenchmark.p
% 2.60/1.05  
% 2.60/1.05  fof(f18,conjecture,(
% 2.60/1.05    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 2.60/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.60/1.05  
% 2.60/1.05  fof(f19,negated_conjecture,(
% 2.60/1.05    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 2.60/1.05    inference(negated_conjecture,[],[f18])).
% 2.60/1.05  
% 2.60/1.05  fof(f28,plain,(
% 2.60/1.05    ? [X0,X1] : ((~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 2.60/1.05    inference(ennf_transformation,[],[f19])).
% 2.60/1.05  
% 2.60/1.05  fof(f29,plain,(
% 2.60/1.05    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1))),
% 2.60/1.05    inference(flattening,[],[f28])).
% 2.60/1.05  
% 2.60/1.05  fof(f33,plain,(
% 2.60/1.05    ? [X0,X1] : (~r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) & r1_tarski(X0,k1_relat_1(X1)) & v1_relat_1(X1)) => (~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 2.60/1.05    introduced(choice_axiom,[])).
% 2.60/1.05  
% 2.60/1.05  fof(f34,plain,(
% 2.60/1.05    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) & r1_tarski(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1)),
% 2.60/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f33])).
% 2.60/1.05  
% 2.60/1.05  fof(f56,plain,(
% 2.60/1.05    r1_tarski(sK0,k1_relat_1(sK1))),
% 2.60/1.05    inference(cnf_transformation,[],[f34])).
% 2.60/1.05  
% 2.60/1.05  fof(f16,axiom,(
% 2.60/1.05    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 2.60/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.60/1.05  
% 2.60/1.05  fof(f25,plain,(
% 2.60/1.05    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 2.60/1.05    inference(ennf_transformation,[],[f16])).
% 2.60/1.05  
% 2.60/1.05  fof(f26,plain,(
% 2.60/1.05    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.60/1.05    inference(flattening,[],[f25])).
% 2.60/1.05  
% 2.60/1.05  fof(f53,plain,(
% 2.60/1.05    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.60/1.05    inference(cnf_transformation,[],[f26])).
% 2.60/1.05  
% 2.60/1.05  fof(f55,plain,(
% 2.60/1.05    v1_relat_1(sK1)),
% 2.60/1.05    inference(cnf_transformation,[],[f34])).
% 2.60/1.05  
% 2.60/1.05  fof(f12,axiom,(
% 2.60/1.05    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 2.60/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.60/1.05  
% 2.60/1.05  fof(f21,plain,(
% 2.60/1.05    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 2.60/1.05    inference(ennf_transformation,[],[f12])).
% 2.60/1.05  
% 2.60/1.05  fof(f49,plain,(
% 2.60/1.05    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 2.60/1.05    inference(cnf_transformation,[],[f21])).
% 2.60/1.05  
% 2.60/1.05  fof(f13,axiom,(
% 2.60/1.05    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 2.60/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.60/1.05  
% 2.60/1.05  fof(f22,plain,(
% 2.60/1.05    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 2.60/1.05    inference(ennf_transformation,[],[f13])).
% 2.60/1.05  
% 2.60/1.05  fof(f50,plain,(
% 2.60/1.05    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.60/1.05    inference(cnf_transformation,[],[f22])).
% 2.60/1.05  
% 2.60/1.05  fof(f2,axiom,(
% 2.60/1.05    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.60/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.60/1.05  
% 2.60/1.05  fof(f30,plain,(
% 2.60/1.05    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.60/1.05    inference(nnf_transformation,[],[f2])).
% 2.60/1.05  
% 2.60/1.05  fof(f31,plain,(
% 2.60/1.05    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.60/1.05    inference(flattening,[],[f30])).
% 2.60/1.05  
% 2.60/1.05  fof(f36,plain,(
% 2.60/1.05    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.60/1.05    inference(cnf_transformation,[],[f31])).
% 2.60/1.05  
% 2.60/1.05  fof(f66,plain,(
% 2.60/1.05    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.60/1.05    inference(equality_resolution,[],[f36])).
% 2.60/1.05  
% 2.60/1.05  fof(f14,axiom,(
% 2.60/1.05    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)))),
% 2.60/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.60/1.05  
% 2.60/1.05  fof(f23,plain,(
% 2.60/1.05    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X0))),
% 2.60/1.05    inference(ennf_transformation,[],[f14])).
% 2.60/1.05  
% 2.60/1.05  fof(f51,plain,(
% 2.60/1.05    ( ! [X2,X0,X1] : (k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) | ~r1_tarski(X1,X2) | ~v1_relat_1(X0)) )),
% 2.60/1.05    inference(cnf_transformation,[],[f23])).
% 2.60/1.05  
% 2.60/1.05  fof(f15,axiom,(
% 2.60/1.05    ! [X0] : (v1_relat_1(X0) => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)))),
% 2.60/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.60/1.05  
% 2.60/1.05  fof(f24,plain,(
% 2.60/1.05    ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.60/1.05    inference(ennf_transformation,[],[f15])).
% 2.60/1.05  
% 2.60/1.05  fof(f52,plain,(
% 2.60/1.05    ( ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.60/1.05    inference(cnf_transformation,[],[f24])).
% 2.60/1.05  
% 2.60/1.05  fof(f17,axiom,(
% 2.60/1.05    ! [X0,X1,X2] : (v1_relat_1(X2) => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1))),
% 2.60/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.60/1.05  
% 2.60/1.05  fof(f27,plain,(
% 2.60/1.05    ! [X0,X1,X2] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 2.60/1.05    inference(ennf_transformation,[],[f17])).
% 2.60/1.05  
% 2.60/1.05  fof(f54,plain,(
% 2.60/1.05    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 2.60/1.05    inference(cnf_transformation,[],[f27])).
% 2.60/1.05  
% 2.60/1.05  fof(f7,axiom,(
% 2.60/1.05    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.60/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.60/1.05  
% 2.60/1.05  fof(f44,plain,(
% 2.60/1.05    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.60/1.05    inference(cnf_transformation,[],[f7])).
% 2.60/1.05  
% 2.60/1.05  fof(f64,plain,(
% 2.60/1.05    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k10_relat_1(X2,X1))) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 2.60/1.05    inference(definition_unfolding,[],[f54,f44])).
% 2.60/1.05  
% 2.60/1.05  fof(f4,axiom,(
% 2.60/1.05    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.60/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.60/1.05  
% 2.60/1.05  fof(f41,plain,(
% 2.60/1.05    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.60/1.05    inference(cnf_transformation,[],[f4])).
% 2.60/1.05  
% 2.60/1.05  fof(f60,plain,(
% 2.60/1.05    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 2.60/1.05    inference(definition_unfolding,[],[f41,f44])).
% 2.60/1.05  
% 2.60/1.05  fof(f5,axiom,(
% 2.60/1.05    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 2.60/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.60/1.05  
% 2.60/1.05  fof(f42,plain,(
% 2.60/1.05    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 2.60/1.05    inference(cnf_transformation,[],[f5])).
% 2.60/1.05  
% 2.60/1.05  fof(f62,plain,(
% 2.60/1.05    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0) )),
% 2.60/1.05    inference(definition_unfolding,[],[f42,f44])).
% 2.60/1.05  
% 2.60/1.05  fof(f6,axiom,(
% 2.60/1.05    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.60/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.60/1.05  
% 2.60/1.05  fof(f43,plain,(
% 2.60/1.05    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.60/1.05    inference(cnf_transformation,[],[f6])).
% 2.60/1.05  
% 2.60/1.05  fof(f3,axiom,(
% 2.60/1.05    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 2.60/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.60/1.05  
% 2.60/1.05  fof(f32,plain,(
% 2.60/1.05    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 2.60/1.05    inference(nnf_transformation,[],[f3])).
% 2.60/1.05  
% 2.60/1.05  fof(f39,plain,(
% 2.60/1.05    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 2.60/1.05    inference(cnf_transformation,[],[f32])).
% 2.60/1.05  
% 2.60/1.05  fof(f57,plain,(
% 2.60/1.05    ~r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))),
% 2.60/1.05    inference(cnf_transformation,[],[f34])).
% 2.60/1.05  
% 2.60/1.05  cnf(c_17,negated_conjecture,
% 2.60/1.05      ( r1_tarski(sK0,k1_relat_1(sK1)) ),
% 2.60/1.05      inference(cnf_transformation,[],[f56]) ).
% 2.60/1.05  
% 2.60/1.05  cnf(c_660,plain,
% 2.60/1.05      ( r1_tarski(sK0,k1_relat_1(sK1)) = iProver_top ),
% 2.60/1.05      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.60/1.05  
% 2.60/1.05  cnf(c_14,plain,
% 2.60/1.05      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 2.60/1.05      | ~ v1_relat_1(X1)
% 2.60/1.05      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 2.60/1.05      inference(cnf_transformation,[],[f53]) ).
% 2.60/1.05  
% 2.60/1.05  cnf(c_663,plain,
% 2.60/1.05      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 2.60/1.05      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 2.60/1.05      | v1_relat_1(X0) != iProver_top ),
% 2.60/1.05      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.60/1.05  
% 2.60/1.05  cnf(c_1723,plain,
% 2.60/1.05      ( k1_relat_1(k7_relat_1(sK1,sK0)) = sK0
% 2.60/1.05      | v1_relat_1(sK1) != iProver_top ),
% 2.60/1.05      inference(superposition,[status(thm)],[c_660,c_663]) ).
% 2.60/1.05  
% 2.60/1.05  cnf(c_18,negated_conjecture,
% 2.60/1.05      ( v1_relat_1(sK1) ),
% 2.60/1.05      inference(cnf_transformation,[],[f55]) ).
% 2.60/1.05  
% 2.60/1.05  cnf(c_783,plain,
% 2.60/1.05      ( ~ r1_tarski(X0,k1_relat_1(sK1))
% 2.60/1.05      | ~ v1_relat_1(sK1)
% 2.60/1.05      | k1_relat_1(k7_relat_1(sK1,X0)) = X0 ),
% 2.60/1.05      inference(instantiation,[status(thm)],[c_14]) ).
% 2.60/1.05  
% 2.60/1.05  cnf(c_876,plain,
% 2.60/1.05      ( ~ r1_tarski(sK0,k1_relat_1(sK1))
% 2.60/1.05      | ~ v1_relat_1(sK1)
% 2.60/1.05      | k1_relat_1(k7_relat_1(sK1,sK0)) = sK0 ),
% 2.60/1.05      inference(instantiation,[status(thm)],[c_783]) ).
% 2.60/1.05  
% 2.60/1.05  cnf(c_2301,plain,
% 2.60/1.05      ( k1_relat_1(k7_relat_1(sK1,sK0)) = sK0 ),
% 2.60/1.05      inference(global_propositional_subsumption,
% 2.60/1.05                [status(thm)],
% 2.60/1.05                [c_1723,c_18,c_17,c_876]) ).
% 2.60/1.05  
% 2.60/1.05  cnf(c_659,plain,
% 2.60/1.05      ( v1_relat_1(sK1) = iProver_top ),
% 2.60/1.05      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.60/1.05  
% 2.60/1.05  cnf(c_10,plain,
% 2.60/1.05      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 2.60/1.05      inference(cnf_transformation,[],[f49]) ).
% 2.60/1.05  
% 2.60/1.05  cnf(c_667,plain,
% 2.60/1.05      ( v1_relat_1(X0) != iProver_top
% 2.60/1.05      | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
% 2.60/1.05      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.60/1.05  
% 2.60/1.05  cnf(c_11,plain,
% 2.60/1.05      ( ~ v1_relat_1(X0)
% 2.60/1.05      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 2.60/1.05      inference(cnf_transformation,[],[f50]) ).
% 2.60/1.05  
% 2.60/1.05  cnf(c_666,plain,
% 2.60/1.05      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
% 2.60/1.05      | v1_relat_1(X0) != iProver_top ),
% 2.60/1.05      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.60/1.05  
% 2.60/1.05  cnf(c_1821,plain,
% 2.60/1.05      ( k9_relat_1(k7_relat_1(X0,X1),k1_relat_1(k7_relat_1(X0,X1))) = k2_relat_1(k7_relat_1(X0,X1))
% 2.60/1.05      | v1_relat_1(X0) != iProver_top ),
% 2.60/1.05      inference(superposition,[status(thm)],[c_667,c_666]) ).
% 2.60/1.05  
% 2.60/1.05  cnf(c_4600,plain,
% 2.60/1.05      ( k9_relat_1(k7_relat_1(sK1,X0),k1_relat_1(k7_relat_1(sK1,X0))) = k2_relat_1(k7_relat_1(sK1,X0)) ),
% 2.60/1.05      inference(superposition,[status(thm)],[c_659,c_1821]) ).
% 2.60/1.05  
% 2.60/1.05  cnf(c_4983,plain,
% 2.60/1.05      ( k9_relat_1(k7_relat_1(sK1,sK0),sK0) = k2_relat_1(k7_relat_1(sK1,sK0)) ),
% 2.60/1.05      inference(superposition,[status(thm)],[c_2301,c_4600]) ).
% 2.60/1.05  
% 2.60/1.05  cnf(c_4,plain,
% 2.60/1.05      ( r1_tarski(X0,X0) ),
% 2.60/1.05      inference(cnf_transformation,[],[f66]) ).
% 2.60/1.05  
% 2.60/1.05  cnf(c_670,plain,
% 2.60/1.05      ( r1_tarski(X0,X0) = iProver_top ),
% 2.60/1.05      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.60/1.05  
% 2.60/1.05  cnf(c_12,plain,
% 2.60/1.05      ( ~ r1_tarski(X0,X1)
% 2.60/1.05      | ~ v1_relat_1(X2)
% 2.60/1.05      | k9_relat_1(k7_relat_1(X2,X1),X0) = k9_relat_1(X2,X0) ),
% 2.60/1.05      inference(cnf_transformation,[],[f51]) ).
% 2.60/1.05  
% 2.60/1.05  cnf(c_665,plain,
% 2.60/1.05      ( k9_relat_1(k7_relat_1(X0,X1),X2) = k9_relat_1(X0,X2)
% 2.60/1.05      | r1_tarski(X2,X1) != iProver_top
% 2.60/1.05      | v1_relat_1(X0) != iProver_top ),
% 2.60/1.05      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.60/1.05  
% 2.60/1.05  cnf(c_2050,plain,
% 2.60/1.05      ( k9_relat_1(k7_relat_1(X0,X1),X1) = k9_relat_1(X0,X1)
% 2.60/1.05      | v1_relat_1(X0) != iProver_top ),
% 2.60/1.05      inference(superposition,[status(thm)],[c_670,c_665]) ).
% 2.60/1.05  
% 2.60/1.05  cnf(c_2824,plain,
% 2.60/1.05      ( k9_relat_1(k7_relat_1(sK1,X0),X0) = k9_relat_1(sK1,X0) ),
% 2.60/1.05      inference(superposition,[status(thm)],[c_659,c_2050]) ).
% 2.60/1.05  
% 2.60/1.05  cnf(c_4985,plain,
% 2.60/1.05      ( k2_relat_1(k7_relat_1(sK1,sK0)) = k9_relat_1(sK1,sK0) ),
% 2.60/1.05      inference(demodulation,[status(thm)],[c_4983,c_2824]) ).
% 2.60/1.05  
% 2.60/1.05  cnf(c_13,plain,
% 2.60/1.05      ( ~ v1_relat_1(X0)
% 2.60/1.05      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 2.60/1.05      inference(cnf_transformation,[],[f52]) ).
% 2.60/1.05  
% 2.60/1.05  cnf(c_664,plain,
% 2.60/1.05      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
% 2.60/1.05      | v1_relat_1(X0) != iProver_top ),
% 2.60/1.05      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.60/1.05  
% 2.60/1.05  cnf(c_1807,plain,
% 2.60/1.05      ( k10_relat_1(k7_relat_1(X0,X1),k2_relat_1(k7_relat_1(X0,X1))) = k1_relat_1(k7_relat_1(X0,X1))
% 2.60/1.05      | v1_relat_1(X0) != iProver_top ),
% 2.60/1.05      inference(superposition,[status(thm)],[c_667,c_664]) ).
% 2.60/1.05  
% 2.60/1.05  cnf(c_3772,plain,
% 2.60/1.05      ( k10_relat_1(k7_relat_1(sK1,X0),k2_relat_1(k7_relat_1(sK1,X0))) = k1_relat_1(k7_relat_1(sK1,X0)) ),
% 2.60/1.05      inference(superposition,[status(thm)],[c_659,c_1807]) ).
% 2.60/1.05  
% 2.60/1.05  cnf(c_15,plain,
% 2.60/1.05      ( ~ v1_relat_1(X0)
% 2.60/1.05      | k4_xboole_0(X1,k4_xboole_0(X1,k10_relat_1(X0,X2))) = k10_relat_1(k7_relat_1(X0,X1),X2) ),
% 2.60/1.05      inference(cnf_transformation,[],[f64]) ).
% 2.60/1.05  
% 2.60/1.05  cnf(c_662,plain,
% 2.60/1.05      ( k4_xboole_0(X0,k4_xboole_0(X0,k10_relat_1(X1,X2))) = k10_relat_1(k7_relat_1(X1,X0),X2)
% 2.60/1.05      | v1_relat_1(X1) != iProver_top ),
% 2.60/1.05      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.60/1.05  
% 2.60/1.05  cnf(c_1043,plain,
% 2.60/1.05      ( k4_xboole_0(X0,k4_xboole_0(X0,k10_relat_1(sK1,X1))) = k10_relat_1(k7_relat_1(sK1,X0),X1) ),
% 2.60/1.05      inference(superposition,[status(thm)],[c_659,c_662]) ).
% 2.60/1.05  
% 2.60/1.05  cnf(c_0,plain,
% 2.60/1.05      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 2.60/1.05      inference(cnf_transformation,[],[f60]) ).
% 2.60/1.05  
% 2.60/1.05  cnf(c_1222,plain,
% 2.60/1.05      ( k5_xboole_0(X0,k10_relat_1(k7_relat_1(sK1,X0),X1)) = k4_xboole_0(X0,k10_relat_1(sK1,X1)) ),
% 2.60/1.05      inference(superposition,[status(thm)],[c_1043,c_0]) ).
% 2.60/1.05  
% 2.60/1.05  cnf(c_4018,plain,
% 2.60/1.05      ( k4_xboole_0(X0,k10_relat_1(sK1,k2_relat_1(k7_relat_1(sK1,X0)))) = k5_xboole_0(X0,k1_relat_1(k7_relat_1(sK1,X0))) ),
% 2.60/1.05      inference(superposition,[status(thm)],[c_3772,c_1222]) ).
% 2.60/1.05  
% 2.60/1.05  cnf(c_4993,plain,
% 2.60/1.05      ( k4_xboole_0(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) = k5_xboole_0(sK0,k1_relat_1(k7_relat_1(sK1,sK0))) ),
% 2.60/1.05      inference(superposition,[status(thm)],[c_4985,c_4018]) ).
% 2.60/1.05  
% 2.60/1.05  cnf(c_4999,plain,
% 2.60/1.05      ( k4_xboole_0(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) = k5_xboole_0(sK0,sK0) ),
% 2.60/1.05      inference(light_normalisation,[status(thm)],[c_4993,c_2301]) ).
% 2.60/1.05  
% 2.60/1.05  cnf(c_7,plain,
% 2.60/1.05      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 2.60/1.05      inference(cnf_transformation,[],[f62]) ).
% 2.60/1.05  
% 2.60/1.05  cnf(c_8,plain,
% 2.60/1.05      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 2.60/1.05      inference(cnf_transformation,[],[f43]) ).
% 2.60/1.05  
% 2.60/1.05  cnf(c_680,plain,
% 2.60/1.05      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 2.60/1.05      inference(light_normalisation,[status(thm)],[c_7,c_8]) ).
% 2.60/1.05  
% 2.60/1.05  cnf(c_923,plain,
% 2.60/1.05      ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,X0) ),
% 2.60/1.05      inference(superposition,[status(thm)],[c_680,c_0]) ).
% 2.60/1.05  
% 2.60/1.05  cnf(c_929,plain,
% 2.60/1.05      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 2.60/1.05      inference(light_normalisation,[status(thm)],[c_923,c_8,c_680]) ).
% 2.60/1.05  
% 2.60/1.05  cnf(c_5000,plain,
% 2.60/1.05      ( k4_xboole_0(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) = k1_xboole_0 ),
% 2.60/1.05      inference(demodulation,[status(thm)],[c_4999,c_929]) ).
% 2.60/1.05  
% 2.60/1.05  cnf(c_6,plain,
% 2.60/1.05      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 2.60/1.05      inference(cnf_transformation,[],[f39]) ).
% 2.60/1.05  
% 2.60/1.05  cnf(c_765,plain,
% 2.60/1.05      ( r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0)))
% 2.60/1.05      | k4_xboole_0(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) != k1_xboole_0 ),
% 2.60/1.05      inference(instantiation,[status(thm)],[c_6]) ).
% 2.60/1.05  
% 2.60/1.05  cnf(c_16,negated_conjecture,
% 2.60/1.05      ( ~ r1_tarski(sK0,k10_relat_1(sK1,k9_relat_1(sK1,sK0))) ),
% 2.60/1.05      inference(cnf_transformation,[],[f57]) ).
% 2.60/1.05  
% 2.60/1.05  cnf(contradiction,plain,
% 2.60/1.05      ( $false ),
% 2.60/1.05      inference(minisat,[status(thm)],[c_5000,c_765,c_16]) ).
% 2.60/1.05  
% 2.60/1.05  
% 2.60/1.05  % SZS output end CNFRefutation for theBenchmark.p
% 2.60/1.05  
% 2.60/1.05  ------                               Statistics
% 2.60/1.05  
% 2.60/1.05  ------ General
% 2.60/1.05  
% 2.60/1.05  abstr_ref_over_cycles:                  0
% 2.60/1.05  abstr_ref_under_cycles:                 0
% 2.60/1.05  gc_basic_clause_elim:                   0
% 2.60/1.05  forced_gc_time:                         0
% 2.60/1.05  parsing_time:                           0.008
% 2.60/1.05  unif_index_cands_time:                  0.
% 2.60/1.05  unif_index_add_time:                    0.
% 2.60/1.05  orderings_time:                         0.
% 2.60/1.05  out_proof_time:                         0.008
% 2.60/1.05  total_time:                             0.149
% 2.60/1.05  num_of_symbols:                         45
% 2.60/1.05  num_of_terms:                           6311
% 2.60/1.05  
% 2.60/1.05  ------ Preprocessing
% 2.60/1.05  
% 2.60/1.05  num_of_splits:                          0
% 2.60/1.05  num_of_split_atoms:                     0
% 2.60/1.05  num_of_reused_defs:                     0
% 2.60/1.05  num_eq_ax_congr_red:                    30
% 2.60/1.05  num_of_sem_filtered_clauses:            1
% 2.60/1.05  num_of_subtypes:                        0
% 2.60/1.05  monotx_restored_types:                  0
% 2.60/1.05  sat_num_of_epr_types:                   0
% 2.60/1.05  sat_num_of_non_cyclic_types:            0
% 2.60/1.05  sat_guarded_non_collapsed_types:        0
% 2.60/1.05  num_pure_diseq_elim:                    0
% 2.60/1.05  simp_replaced_by:                       0
% 2.60/1.05  res_preprocessed:                       93
% 2.60/1.05  prep_upred:                             0
% 2.60/1.05  prep_unflattend:                        0
% 2.60/1.05  smt_new_axioms:                         0
% 2.60/1.05  pred_elim_cands:                        2
% 2.60/1.05  pred_elim:                              0
% 2.60/1.05  pred_elim_cl:                           0
% 2.60/1.05  pred_elim_cycles:                       2
% 2.60/1.05  merged_defs:                            8
% 2.60/1.05  merged_defs_ncl:                        0
% 2.60/1.05  bin_hyper_res:                          8
% 2.60/1.05  prep_cycles:                            4
% 2.60/1.05  pred_elim_time:                         0.
% 2.60/1.05  splitting_time:                         0.
% 2.60/1.05  sem_filter_time:                        0.
% 2.60/1.05  monotx_time:                            0.
% 2.60/1.05  subtype_inf_time:                       0.
% 2.60/1.05  
% 2.60/1.05  ------ Problem properties
% 2.60/1.05  
% 2.60/1.05  clauses:                                18
% 2.60/1.05  conjectures:                            3
% 2.60/1.05  epr:                                    3
% 2.60/1.05  horn:                                   18
% 2.60/1.05  ground:                                 3
% 2.60/1.05  unary:                                  9
% 2.60/1.05  binary:                                 6
% 2.60/1.05  lits:                                   30
% 2.60/1.05  lits_eq:                                13
% 2.60/1.05  fd_pure:                                0
% 2.60/1.05  fd_pseudo:                              0
% 2.60/1.05  fd_cond:                                0
% 2.60/1.05  fd_pseudo_cond:                         1
% 2.60/1.05  ac_symbols:                             0
% 2.60/1.05  
% 2.60/1.05  ------ Propositional Solver
% 2.60/1.05  
% 2.60/1.05  prop_solver_calls:                      28
% 2.60/1.05  prop_fast_solver_calls:                 435
% 2.60/1.05  smt_solver_calls:                       0
% 2.60/1.05  smt_fast_solver_calls:                  0
% 2.60/1.05  prop_num_of_clauses:                    2435
% 2.60/1.05  prop_preprocess_simplified:             5917
% 2.60/1.05  prop_fo_subsumed:                       1
% 2.60/1.05  prop_solver_time:                       0.
% 2.60/1.05  smt_solver_time:                        0.
% 2.60/1.05  smt_fast_solver_time:                   0.
% 2.60/1.05  prop_fast_solver_time:                  0.
% 2.60/1.05  prop_unsat_core_time:                   0.
% 2.60/1.05  
% 2.60/1.05  ------ QBF
% 2.60/1.05  
% 2.60/1.05  qbf_q_res:                              0
% 2.60/1.05  qbf_num_tautologies:                    0
% 2.60/1.05  qbf_prep_cycles:                        0
% 2.60/1.05  
% 2.60/1.05  ------ BMC1
% 2.60/1.05  
% 2.60/1.05  bmc1_current_bound:                     -1
% 2.60/1.05  bmc1_last_solved_bound:                 -1
% 2.60/1.05  bmc1_unsat_core_size:                   -1
% 2.60/1.05  bmc1_unsat_core_parents_size:           -1
% 2.60/1.05  bmc1_merge_next_fun:                    0
% 2.60/1.05  bmc1_unsat_core_clauses_time:           0.
% 2.60/1.05  
% 2.60/1.05  ------ Instantiation
% 2.60/1.05  
% 2.60/1.05  inst_num_of_clauses:                    821
% 2.60/1.05  inst_num_in_passive:                    199
% 2.60/1.05  inst_num_in_active:                     327
% 2.60/1.05  inst_num_in_unprocessed:                295
% 2.60/1.05  inst_num_of_loops:                      330
% 2.60/1.05  inst_num_of_learning_restarts:          0
% 2.60/1.05  inst_num_moves_active_passive:          1
% 2.60/1.05  inst_lit_activity:                      0
% 2.60/1.05  inst_lit_activity_moves:                0
% 2.60/1.05  inst_num_tautologies:                   0
% 2.60/1.05  inst_num_prop_implied:                  0
% 2.60/1.05  inst_num_existing_simplified:           0
% 2.60/1.05  inst_num_eq_res_simplified:             0
% 2.60/1.05  inst_num_child_elim:                    0
% 2.60/1.05  inst_num_of_dismatching_blockings:      49
% 2.60/1.05  inst_num_of_non_proper_insts:           606
% 2.60/1.05  inst_num_of_duplicates:                 0
% 2.60/1.05  inst_inst_num_from_inst_to_res:         0
% 2.60/1.05  inst_dismatching_checking_time:         0.
% 2.60/1.05  
% 2.60/1.05  ------ Resolution
% 2.60/1.05  
% 2.60/1.05  res_num_of_clauses:                     0
% 2.60/1.05  res_num_in_passive:                     0
% 2.60/1.05  res_num_in_active:                      0
% 2.60/1.05  res_num_of_loops:                       97
% 2.60/1.05  res_forward_subset_subsumed:            71
% 2.60/1.05  res_backward_subset_subsumed:           0
% 2.60/1.05  res_forward_subsumed:                   0
% 2.60/1.05  res_backward_subsumed:                  0
% 2.60/1.05  res_forward_subsumption_resolution:     0
% 2.60/1.05  res_backward_subsumption_resolution:    0
% 2.60/1.05  res_clause_to_clause_subsumption:       200
% 2.60/1.05  res_orphan_elimination:                 0
% 2.60/1.05  res_tautology_del:                      66
% 2.60/1.05  res_num_eq_res_simplified:              0
% 2.60/1.05  res_num_sel_changes:                    0
% 2.60/1.05  res_moves_from_active_to_pass:          0
% 2.60/1.05  
% 2.60/1.05  ------ Superposition
% 2.60/1.05  
% 2.60/1.05  sup_time_total:                         0.
% 2.60/1.05  sup_time_generating:                    0.
% 2.60/1.05  sup_time_sim_full:                      0.
% 2.60/1.05  sup_time_sim_immed:                     0.
% 2.60/1.05  
% 2.60/1.05  sup_num_of_clauses:                     97
% 2.60/1.05  sup_num_in_active:                      64
% 2.60/1.05  sup_num_in_passive:                     33
% 2.60/1.05  sup_num_of_loops:                       65
% 2.60/1.05  sup_fw_superposition:                   77
% 2.60/1.05  sup_bw_superposition:                   73
% 2.60/1.05  sup_immediate_simplified:               85
% 2.60/1.05  sup_given_eliminated:                   1
% 2.60/1.05  comparisons_done:                       0
% 2.60/1.05  comparisons_avoided:                    0
% 2.60/1.05  
% 2.60/1.05  ------ Simplifications
% 2.60/1.05  
% 2.60/1.05  
% 2.60/1.05  sim_fw_subset_subsumed:                 0
% 2.60/1.05  sim_bw_subset_subsumed:                 0
% 2.60/1.05  sim_fw_subsumed:                        15
% 2.60/1.05  sim_bw_subsumed:                        0
% 2.60/1.05  sim_fw_subsumption_res:                 0
% 2.60/1.05  sim_bw_subsumption_res:                 0
% 2.60/1.05  sim_tautology_del:                      0
% 2.60/1.05  sim_eq_tautology_del:                   31
% 2.60/1.05  sim_eq_res_simp:                        0
% 2.60/1.05  sim_fw_demodulated:                     41
% 2.60/1.05  sim_bw_demodulated:                     2
% 2.60/1.05  sim_light_normalised:                   57
% 2.60/1.05  sim_joinable_taut:                      0
% 2.60/1.05  sim_joinable_simp:                      0
% 2.60/1.05  sim_ac_normalised:                      0
% 2.60/1.05  sim_smt_subsumption:                    0
% 2.60/1.05  
%------------------------------------------------------------------------------
